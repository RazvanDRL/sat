"""
Simulated Annealing Implementation for SAT solving.

This module implements a Simulated Annealing approach for solving SAT problems,
based on Kirkpatrick, Gelatt and Vecchi (1983). Simulated Annealing is a 
metaheuristic for global optimization that allows accepting worse solutions
with a probability that decreases over time.
"""

import sys
import time
import random
import math
from typing import List, Tuple, Dict, Optional

sys.path.append("../")
from common.structures import Literal
from common.dimacs_parser import parse_dimacs_cnf


class SimulatedAnnealingSolver:
    """
    Simulated Annealing solver for SAT problems.
    
    This implementation treats SAT as a minimization problem where the cost function
    is the number of unsatisfied clauses. The algorithm starts with a random assignment
    and iteratively moves to neighboring assignments (by flipping variables), accepting
    worse solutions with a probability that decreases over time.
    """
    
    def __init__(self, clauses: List[List[Literal]], n_vars: int, initial_temp: float = 2.0, 
                 cooling_factor: float = 0.95, steps_per_temp: int = 100, 
                 min_temp: float = 0.01, max_iterations: int = 1000000):
        """
        Initialize the Simulated Annealing solver.
        
        Args:
            clauses: List of clauses (each clause is a list of Literal objects)
            n_vars: Number of variables in the formula
            initial_temp: Initial temperature parameter
            cooling_factor: Factor to multiply temperature at each cooling step (0 < cooling_factor < 1)
            steps_per_temp: Number of iterations at each temperature level
            min_temp: Minimum temperature (stopping condition)
            max_iterations: Maximum total iterations
        """
        self.clauses = clauses
        self.n_vars = n_vars
        self.initial_temp = initial_temp
        self.cooling_factor = cooling_factor
        self.steps_per_temp = steps_per_temp
        self.min_temp = min_temp
        self.max_iterations = max_iterations
        
        # Statistics
        self.iterations = 0
        self.accepted_moves = 0
        self.rejected_moves = 0
        self.uphill_moves = 0  # Moves that increase cost but are accepted
        self.start_time = 0
    
    def initialize_random_assignment(self) -> List[int]:
        """Create a random assignment for all variables."""
        assignment = [0]  # Index 0 is not used (variables are 1-indexed)
        for i in range(1, self.n_vars + 1):
            # Randomly assign True (1) or False (-1)
            assignment.append(random.choice([1, -1]))
        return assignment
    
    def count_unsatisfied_clauses(self, assignment: List[int]) -> int:
        """Count the number of clauses unsatisfied by the current assignment."""
        unsatisfied_count = 0
        for clause in self.clauses:
            # A clause is unsatisfied if all its literals are false
            satisfied = False
            for lit in clause:
                var = lit.variable_index
                is_negated = lit.is_negated
                # Check if the literal is satisfied
                if (not is_negated and assignment[var] > 0) or (is_negated and assignment[var] < 0):
                    satisfied = True
                    break
            if not satisfied:
                unsatisfied_count += 1
        return unsatisfied_count
    
    def acceptance_probability(self, old_cost: int, new_cost: int, temperature: float) -> float:
        """
        Calculate the probability of accepting a move that changes the cost.
        
        For cost-decreasing moves, always return 1.0 (100% acceptance).
        For cost-increasing moves, return probability based on cost difference and temperature.
        """
        if new_cost <= old_cost:
            return 1.0  # Always accept if cost decreases or remains the same
        
        # Calculate probability for accepting a worse solution
        delta = new_cost - old_cost
        return math.exp(-delta / temperature)
    
    def solve(self, timeout=None) -> Tuple[bool, Optional[List[int]]]:
        """
        Solve the SAT instance using Simulated Annealing.
        
        Args:
            timeout: Optional timeout in seconds
            
        Returns:
            Tuple containing:
            - Boolean indicating if a satisfying assignment was found
            - List of literals in the satisfying assignment (or None if none found)
        """
        self.start_time = time.time()
        self.iterations = 0
        self.accepted_moves = 0
        self.rejected_moves = 0
        self.uphill_moves = 0
        
        # Initialize with a random assignment
        current_assignment = self.initialize_random_assignment()
        current_cost = self.count_unsatisfied_clauses(current_assignment)
        
        # If initial assignment is a solution, return immediately
        if current_cost == 0:
            return True, self.assignment_to_literals(current_assignment)
        
        # Best solution found so far
        best_assignment = current_assignment.copy()
        best_cost = current_cost
        
        # Initial temperature
        temperature = self.initial_temp
        
        # Main loop
        while temperature > self.min_temp and self.iterations < self.max_iterations:
            # Check timeout
            if timeout and time.time() - self.start_time > timeout:
                if best_cost == 0:
                    return True, self.assignment_to_literals(best_assignment)
                return False, None
            
            # Perform steps at this temperature
            for _ in range(self.steps_per_temp):
                self.iterations += 1
                
                # Check timeout
                if timeout and time.time() - self.start_time > timeout:
                    if best_cost == 0:
                        return True, self.assignment_to_literals(best_assignment)
                    return False, None
                
                # Choose a random variable to flip
                var_to_flip = random.randint(1, self.n_vars)
                
                # Make a tentative flip
                new_assignment = current_assignment.copy()
                new_assignment[var_to_flip] = -new_assignment[var_to_flip]
                
                # Calculate new cost
                new_cost = self.count_unsatisfied_clauses(new_assignment)
                
                # If new assignment is a solution, return immediately
                if new_cost == 0:
                    return True, self.assignment_to_literals(new_assignment)
                
                # Decide whether to accept the new solution
                if random.random() < self.acceptance_probability(current_cost, new_cost, temperature):
                    current_assignment = new_assignment
                    current_cost = new_cost
                    self.accepted_moves += 1
                    
                    # Track uphill moves
                    if new_cost > current_cost:
                        self.uphill_moves += 1
                    
                    # Update best solution if improved
                    if current_cost < best_cost:
                        best_assignment = current_assignment.copy()
                        best_cost = current_cost
                else:
                    self.rejected_moves += 1
                
                # Optional: break early if solution found
                if current_cost == 0:
                    return True, self.assignment_to_literals(current_assignment)
            
            # Cool down
            temperature *= self.cooling_factor
        
        # Return best solution found
        if best_cost == 0:
            return True, self.assignment_to_literals(best_assignment)
        
        # No solution found
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


def solve_file(filepath: str, initial_temp: float = 2.0, cooling_factor: float = 0.95,
              steps_per_temp: int = 100, min_temp: float = 0.01, 
              max_iterations: int = 1000000, timeout=None) -> Tuple[bool, Optional[List[int]], Dict]:
    """
    Solve a DIMACS CNF file using the Simulated Annealing algorithm.
    
    Args:
        filepath: Path to the DIMACS CNF file
        initial_temp: Initial temperature parameter
        cooling_factor: Factor to multiply temperature at each cooling step
        steps_per_temp: Number of iterations at each temperature level
        min_temp: Minimum temperature (stopping condition)
        max_iterations: Maximum total iterations
        timeout: Optional timeout in seconds
        
    Returns:
        Tuple containing:
        - Boolean indicating satisfiability
        - List of literals in a satisfying assignment (or None if none found)
        - Dictionary of statistics
    """
    clauses, num_vars, _ = parse_dimacs_cnf(filepath)
    solver = SimulatedAnnealingSolver(
        clauses, num_vars, initial_temp, cooling_factor, steps_per_temp, min_temp, max_iterations
    )
    
    start_time = time.time()
    result, model = solver.solve(timeout)
    solve_time = time.time() - start_time
    
    statistics = {
        "iterations": solver.iterations,
        "accepted_moves": solver.accepted_moves,
        "rejected_moves": solver.rejected_moves,
        "uphill_moves": solver.uphill_moves,
        "initial_temp": initial_temp,
        "cooling_factor": cooling_factor,
        "time": solve_time,
        "timeout": timeout is not None and solve_time >= timeout
    }
    
    return result, model, statistics


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python simulated_annealing.py <cnf_file> [initial_temp] [cooling_factor] [steps_per_temp] [min_temp] [max_iterations] [timeout]")
        sys.exit(1)
    
    filepath = sys.argv[1]
    
    initial_temp = 2.0
    if len(sys.argv) > 2:
        initial_temp = float(sys.argv[2])
    
    cooling_factor = 0.95
    if len(sys.argv) > 3:
        cooling_factor = float(sys.argv[3])
    
    steps_per_temp = 100
    if len(sys.argv) > 4:
        steps_per_temp = int(sys.argv[4])
    
    min_temp = 0.01
    if len(sys.argv) > 5:
        min_temp = float(sys.argv[5])
    
    max_iterations = 1000000
    if len(sys.argv) > 6:
        max_iterations = int(sys.argv[6])
    
    timeout = None
    if len(sys.argv) > 7:
        timeout = float(sys.argv[7])
    
    print(f"Solving {filepath} with Simulated Annealing algorithm...")
    print(f"Parameters: initial_temp={initial_temp}, cooling_factor={cooling_factor}, steps_per_temp={steps_per_temp}, min_temp={min_temp}, max_iterations={max_iterations}, timeout={timeout}")
    
    start_time = time.time()
    satisfiable, model, stats = solve_file(filepath, initial_temp, cooling_factor, steps_per_temp, min_temp, max_iterations, timeout)
    
    if satisfiable:
        print("SATISFIABLE")
        print(f"Model: {' '.join(str(lit) for lit in model)} 0")
    else:
        print("NO SOLUTION FOUND (incomplete algorithm)")
    
    print(f"Time: {stats['time']:.3f}s")
    print(f"Iterations: {stats['iterations']}")
    print(f"Accepted moves: {stats['accepted_moves']}")
    print(f"Rejected moves: {stats['rejected_moves']}")
    print(f"Uphill moves: {stats['uphill_moves']}") 