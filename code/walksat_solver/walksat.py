"""
WalkSAT Implementation.

This module implements the WalkSAT algorithm, an incomplete stochastic local search
algorithm for solving SAT problems, as described in the paper by Selman, Kautz,
and Cohen (1994). WalkSAT extends GSAT by adding random walks to escape local minima.
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


class WalkSATSolver:
    """
    WalkSAT solver implementation.
    
    WalkSAT is a local search algorithm that starts with a random assignment and
    iteratively chooses an unsatisfied clause and flips a variable in that clause.
    With probability p, it chooses a random variable from the clause; otherwise,
    it chooses the variable that minimizes the number of clauses that become unsatisfied.
    """
    
    def __init__(self, clauses: List[List[Literal]], n_vars: int, max_flips: int = 100000, max_tries: int = 100, noise: float = 0.5):
        """
        Initialize the WalkSAT solver.
        
        Args:
            clauses: List of clauses (each clause is a list of Literal objects)
            n_vars: Number of variables in the formula
            max_flips: Maximum number of variable flips per try
            max_tries: Maximum number of random restarts
            noise: Probability of making a random walk (noise parameter)
        """
        self.clauses = clauses
        self.n_vars = n_vars
        self.max_flips = max_flips
        self.max_tries = max_tries
        self.noise = noise
        
        # Statistics
        self.flips = 0
        self.tries = 0
        self.random_walks = 0
        self.greedy_walks = 0
        self.start_time = 0
    
    def initialize_random_assignment(self) -> List[int]:
        """Create a random assignment for all variables."""
        assignment = [0]  # Index 0 is not used (variables are 1-indexed)
        for i in range(1, self.n_vars + 1):
            # Randomly assign True (1) or False (-1)
            assignment.append(random.choice([1, -1]))
        return assignment
    
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
    
    def compute_breaks(self, assignment: List[int], var: int) -> int:
        """
        Compute the 'breaks' value for a variable - how many currently satisfied
        clauses would become unsatisfied if this variable were flipped.
        """
        breaks = 0
        for clause in self.clauses:
            # Check if the clause is currently satisfied
            is_satisfied = False
            critical_lit = None  # The literal that makes the clause satisfied (if any)
            contains_var = False
            
            for lit in clause:
                if lit.variable_index == var:
                    contains_var = True
                if (not lit.is_negated and assignment[lit.variable_index] > 0) or (lit.is_negated and assignment[lit.variable_index] < 0):
                    is_satisfied = True
                    critical_lit = lit
                    break
            
            # If this clause is satisfied by exactly one literal and that literal
            # contains our variable, flipping the variable would break this clause
            if is_satisfied and contains_var and critical_lit and critical_lit.variable_index == var:
                breaks += 1
        
        return breaks
    
    def compute_makes(self, assignment: List[int], var: int, unsatisfied_clauses: List[List[Literal]]) -> int:
        """
        Compute the 'makes' value for a variable - how many currently unsatisfied
        clauses would become satisfied if this variable were flipped.
        """
        makes = 0
        for clause in unsatisfied_clauses:
            for lit in clause:
                if lit.variable_index == var:
                    # If flipping the variable would make this literal true, it would make the clause satisfied
                    if (not lit.is_negated and assignment[var] < 0) or (lit.is_negated and assignment[var] > 0):
                        makes += 1
                        break
        
        return makes
    
    def choose_variable_to_flip(self, assignment: List[int], unsatisfied_clause: List[Literal]) -> int:
        """
        Choose a variable to flip from an unsatisfied clause.
        
        With probability self.noise, choose a random variable from the clause.
        Otherwise, choose the variable that minimizes the number of breaks.
        """
        # With probability noise, make a random walk
        if random.random() < self.noise:
            self.random_walks += 1
            random_lit = random.choice(unsatisfied_clause)
            return random_lit.variable_index
        
        # Otherwise, make a greedy choice
        self.greedy_walks += 1
        
        # Find the variable that minimizes breaks (or maximizes makes-breaks)
        best_var = 0
        best_score = float('inf')  # Lower breaks is better
        
        for lit in unsatisfied_clause:
            var = lit.variable_index
            breaks = self.compute_breaks(assignment, var)
            
            # If we find a variable with 0 breaks, choose it immediately
            if breaks == 0:
                return var
            
            if breaks < best_score:
                best_score = breaks
                best_var = var
        
        # If multiple variables have the same best score, choose randomly among them
        candidates = []
        for lit in unsatisfied_clause:
            var = lit.variable_index
            breaks = self.compute_breaks(assignment, var)
            if breaks == best_score:
                candidates.append(var)
        
        if candidates:
            return random.choice(candidates)
        
        return best_var
    
    def solve(self, timeout=None) -> Tuple[bool, Optional[List[int]]]:
        """
        Solve the SAT instance using WalkSAT.
        
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
        self.random_walks = 0
        self.greedy_walks = 0
        
        for _ in range(self.max_tries):
            self.tries += 1
            
            # Check timeout
            if timeout and time.time() - self.start_time > timeout:
                return False, None
            
            # Start with a random assignment
            assignment = self.initialize_random_assignment()
            
            # Get initial unsatisfied clauses
            unsatisfied_clauses = self.get_unsatisfied_clauses(assignment)
            
            # If already satisfied, return immediately
            if not unsatisfied_clauses:
                return True, self.assignment_to_literals(assignment)
            
            # Perform local search
            for _ in range(self.max_flips):
                self.flips += 1
                
                # Check timeout
                if timeout and time.time() - self.start_time > timeout:
                    return False, None
                
                # If all clauses are satisfied, we're done
                if not unsatisfied_clauses:
                    return True, self.assignment_to_literals(assignment)
                
                # Choose an unsatisfied clause randomly
                unsatisfied_clause = random.choice(unsatisfied_clauses)
                
                # Choose a variable from the clause to flip
                var_to_flip = self.choose_variable_to_flip(assignment, unsatisfied_clause)
                
                # Flip the variable
                assignment[var_to_flip] = -assignment[var_to_flip]
                
                # Recompute unsatisfied clauses after the flip
                unsatisfied_clauses = self.get_unsatisfied_clauses(assignment)
        
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


def solve_file(filepath: str, max_flips: int = 100000, max_tries: int = 100, 
               noise: float = 0.5, timeout=None) -> Tuple[bool, Optional[List[int]], Dict]:
    """
    Solve a DIMACS CNF file using the WalkSAT algorithm.
    
    Args:
        filepath: Path to the DIMACS CNF file
        max_flips: Maximum number of variable flips per try
        max_tries: Maximum number of random restarts
        noise: Probability of making a random walk
        timeout: Optional timeout in seconds
        
    Returns:
        Tuple containing:
        - Boolean indicating satisfiability
        - List of literals in a satisfying assignment (or None if none found)
        - Dictionary of statistics
    """
    clauses, num_vars, _ = parse_dimacs_cnf(filepath)
    solver = WalkSATSolver(clauses, num_vars, max_flips, max_tries, noise)
    
    start_time = time.time()
    result, model = solver.solve(timeout)
    solve_time = time.time() - start_time
    
    statistics = {
        "tries": solver.tries,
        "flips": solver.flips,
        "random_walks": solver.random_walks,
        "greedy_walks": solver.greedy_walks,
        "noise": noise,
        "time": solve_time,
        "timeout": timeout is not None and solve_time >= timeout
    }
    
    return result, model, statistics


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python walksat.py <cnf_file> [max_flips] [max_tries] [noise] [timeout]")
        sys.exit(1)
    
    filepath = sys.argv[1]
    
    max_flips = 100000
    if len(sys.argv) > 2:
        max_flips = int(sys.argv[2])
    
    max_tries = 100
    if len(sys.argv) > 3:
        max_tries = int(sys.argv[3])
    
    noise = 0.5
    if len(sys.argv) > 4:
        noise = float(sys.argv[4])
    
    timeout = None
    if len(sys.argv) > 5:
        timeout = float(sys.argv[5])
    
    print(f"Solving {filepath} with WalkSAT algorithm...")
    print(f"Parameters: max_flips={max_flips}, max_tries={max_tries}, noise={noise}, timeout={timeout}")
    
    start_time = time.time()
    satisfiable, model, stats = solve_file(filepath, max_flips, max_tries, noise, timeout)
    
    if satisfiable:
        print("SATISFIABLE")
        print(f"Model: {' '.join(str(lit) for lit in model)} 0")
    else:
        print("NO SOLUTION FOUND (incomplete algorithm)")
    
    print(f"Time: {stats['time']:.3f}s")
    print(f"Tries: {stats['tries']}")
    print(f"Flips: {stats['flips']}")
    print(f"Random walks: {stats['random_walks']}")
    print(f"Greedy walks: {stats['greedy_walks']}") 