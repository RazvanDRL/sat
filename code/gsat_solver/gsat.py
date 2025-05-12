"""
GSAT (Greedy SATisfiability) Implementation.

This module implements the GSAT algorithm, an incomplete stochastic local search
algorithm for solving SAT problems, as described in the paper by Selman, Levesque,
and Mitchell (1992).
"""

import sys
import time
import random
import os
from typing import List, Set, Tuple, Dict, Optional

# Adjust the import path to find the common module
current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)
sys.path.append(parent_dir)

from common.structures import Literal
from common.dimacs_parser import parse_dimacs_cnf


class GSATSolver:
    """
    GSAT (Greedy SATisfiability) solver implementation.
    
    GSAT is a local search algorithm that starts with a random assignment and 
    iteratively flips the variable that maximizes the number of satisfied clauses.
    """
    
    def __init__(self, clauses: List[List[Literal]], n_vars: int, max_flips: int = 100000, max_tries: int = 100):
        """
        Initialize the GSAT solver.
        
        Args:
            clauses: List of clauses (each clause is a list of Literal objects)
            n_vars: Number of variables in the formula
            max_flips: Maximum number of variable flips per try
            max_tries: Maximum number of random restarts
        """
        self.clauses = clauses
        self.n_vars = n_vars
        self.max_flips = max_flips
        self.max_tries = max_tries
        
        # Statistics
        self.flips = 0
        self.tries = 0
        self.start_time = 0
    
    def initialize_random_assignment(self) -> List[int]:
        """Create a random assignment for all variables."""
        assignment = [0]  # Index 0 is not used (variables are 1-indexed)
        for i in range(1, self.n_vars + 1):
            # Randomly assign True (1) or False (-1)
            assignment.append(random.choice([1, -1]))
        return assignment
    
    def count_satisfied_clauses(self, assignment: List[int]) -> int:
        """Count the number of clauses satisfied by the current assignment."""
        satisfied_count = 0
        for clause in self.clauses:
            # A clause is satisfied if at least one of its literals is true
            satisfied = False
            for lit in clause:
                var = lit.variable_index
                is_negated = lit.is_negated
                # Check if the literal is satisfied
                if (not is_negated and assignment[var] > 0) or (is_negated and assignment[var] < 0):
                    satisfied = True
                    break
            if satisfied:
                satisfied_count += 1
        return satisfied_count
    
    def get_unsatisfied_clauses(self, assignment: List[int]) -> List[List[Literal]]:
        """Get the list of clauses that are not satisfied by the current assignment."""
        unsatisfied = []
        for clause in self.clauses:
            satisfied = False
            for lit in clause:
                var = lit.variable_index
                is_negated = lit.is_negated
                if (not is_negated and assignment[var] > 0) or (is_negated and assignment[var] < 0):
                    satisfied = True
                    break
            if not satisfied:
                unsatisfied.append(clause)
        return unsatisfied
    
    def compute_score_changes(self, assignment: List[int]) -> List[int]:
        """
        Compute the score change (increase in satisfied clauses) for flipping each variable.
        
        Returns:
            A list where index i contains the net change in satisfied clauses if variable i is flipped
        """
        score_changes = [0] * (self.n_vars + 1)  # Index 0 is unused
        
        # For each clause, check the impact of flipping each of its variables
        for clause in self.clauses:
            # Check if the clause is currently satisfied
            is_satisfied = False
            critical_lit = None  # The literal that makes the clause satisfied (if any)
            
            for lit in clause:
                var = lit.variable_index
                is_negated = lit.is_negated
                if (not is_negated and assignment[var] > 0) or (is_negated and assignment[var] < 0):
                    is_satisfied = True
                    critical_lit = lit
                    break
            
            if is_satisfied:
                # If the clause is satisfied by exactly one literal, flipping that variable
                # would make the clause unsatisfied
                if critical_lit:
                    var = critical_lit.variable_index
                    # Flipping this variable would make the clause unsatisfied
                    score_changes[var] -= 1
            else:
                # If the clause is unsatisfied, flipping a variable might make it satisfied
                for lit in clause:
                    var = lit.variable_index
                    is_negated = lit.is_negated
                    # Check if flipping this variable would satisfy the clause
                    if (not is_negated and assignment[var] < 0) or (is_negated and assignment[var] > 0):
                        score_changes[var] += 1
        
        return score_changes
    
    def find_best_flip(self, assignment: List[int], tabu_vars: Set[int] = None) -> int:
        """
        Find the variable flip that leads to the largest increase in satisfied clauses.
        
        Args:
            assignment: Current variable assignment
            tabu_vars: Set of variables that are tabu (not allowed to flip)
            
        Returns:
            The variable to flip (0 if none)
        """
        score_changes = self.compute_score_changes(assignment)
        
        # Find the variable with the highest score change
        best_var = 0
        best_score = -1
        
        for var in range(1, self.n_vars + 1):
            if tabu_vars and var in tabu_vars:
                continue
                
            if score_changes[var] > best_score:
                best_score = score_changes[var]
                best_var = var
        
        # If multiple variables have the same score, choose randomly among them
        candidates = []
        for var in range(1, self.n_vars + 1):
            if tabu_vars and var in tabu_vars:
                continue
                
            if score_changes[var] == best_score:
                candidates.append(var)
        
        if candidates:
            return random.choice(candidates)
        
        return 0  # No variables to flip (shouldn't happen with proper parameters)
    
    def solve(self, timeout=None) -> Tuple[bool, Optional[List[int]]]:
        """
        Solve the SAT instance using GSAT.
        
        Args:
            timeout: Optional timeout in seconds
            
        Returns:
            Tuple containing:
            - Boolean indicating if a satisfying assignment was found
            - List of literals in the satisfying assignment (or None if none found)
        """
        self.start_time = time.time()
        self.tries = 0
        self.flips = 0
        
        for _ in range(self.max_tries):
            self.tries += 1
            
            # Check timeout
            if timeout and time.time() - self.start_time > timeout:
                return False, None
            
            # Start with a random assignment
            assignment = self.initialize_random_assignment()
            
            # Count initial satisfied clauses
            satisfied_count = self.count_satisfied_clauses(assignment)
            
            # If already satisfied, return immediately
            if satisfied_count == len(self.clauses):
                return True, self.assignment_to_literals(assignment)
            
            # Perform local search
            for _ in range(self.max_flips):
                self.flips += 1
                
                # Check timeout
                if timeout and time.time() - self.start_time > timeout:
                    return False, None
                
                # Find the best variable to flip
                var_to_flip = self.find_best_flip(assignment)
                
                if var_to_flip == 0:
                    break  # No variables to flip
                
                # Flip the variable
                assignment[var_to_flip] = -assignment[var_to_flip]
                
                # Check if solution is found
                satisfied_count = self.count_satisfied_clauses(assignment)
                if satisfied_count == len(self.clauses):
                    return True, self.assignment_to_literals(assignment)
        
        # No solution found within the given tries and flips
        return False, None
    
    def assignment_to_literals(self, assignment: List[int]) -> List[int]:
        """Convert internal assignment representation to a list of literals."""
        result = []
        for var in range(1, len(assignment)):
            if assignment[var] > 0:
                result.append(var)
            else:
                result.append(-var)
        return result


def solve_file(filepath: str, max_flips: int = 100000, max_tries: int = 100, timeout=None) -> Tuple[bool, Optional[List[int]], Dict]:
    """
    Solve a DIMACS CNF file using the GSAT algorithm.
    
    Args:
        filepath: Path to the DIMACS CNF file
        max_flips: Maximum number of variable flips per try
        max_tries: Maximum number of random restarts
        timeout: Optional timeout in seconds
        
    Returns:
        Tuple containing:
        - Boolean indicating satisfiability
        - List of literals in a satisfying assignment (or None if none found)
        - Dictionary of statistics
    """
    clauses, num_vars, _ = parse_dimacs_cnf(filepath)
    solver = GSATSolver(clauses, num_vars, max_flips, max_tries)
    
    start_time = time.time()
    result, model = solver.solve(timeout)
    solve_time = time.time() - start_time
    
    statistics = {
        "tries": solver.tries,
        "flips": solver.flips,
        "time": solve_time,
        "timeout": timeout is not None and solve_time >= timeout
    }
    
    return result, model, statistics


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python gsat.py <cnf_file> [max_flips] [max_tries] [timeout]")
        sys.exit(1)
    
    filepath = sys.argv[1]
    
    max_flips = 100000
    if len(sys.argv) > 2:
        max_flips = int(sys.argv[2])
    
    max_tries = 100
    if len(sys.argv) > 3:
        max_tries = int(sys.argv[3])
    
    timeout = None
    if len(sys.argv) > 4:
        timeout = float(sys.argv[4])
    
    print(f"Solving {filepath} with GSAT algorithm...")
    print(f"Parameters: max_flips={max_flips}, max_tries={max_tries}, timeout={timeout}")
    
    start_time = time.time()
    satisfiable, model, stats = solve_file(filepath, max_flips, max_tries, timeout)
    
    if satisfiable:
        print("SATISFIABLE")
        print(f"Model: {' '.join(str(lit) for lit in model)} 0")
    else:
        print("NO SOLUTION FOUND (incomplete algorithm)")
    
    print(f"Time: {stats['time']:.3f}s")
    print(f"Tries: {stats['tries']}")
    print(f"Flips: {stats['flips']}") 