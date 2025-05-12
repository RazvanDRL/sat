import sys
import time
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from common.structures import Literal, Assignment, clause_is_satisfied, get_unit_literal, clause_is_conflicting
from .heuristics import get_heuristic, first_unassigned_heuristic

class DPLLSolver:
    """
    A SAT solver implementing the Davis-Putnam-Logemann-Loveland (DPLL) algorithm,
    which is a complete, backtracking-based search algorithm.
    """
    def __init__(self, heuristic_name="first_unassigned"):
        """Initialize the solver with a specified variable selection heuristic."""
        self.heuristic = get_heuristic(heuristic_name)
        # Performance metrics
        self.stats = {
            "decisions": 0,
            "backtracking_steps": 0,
            "unit_propagations": 0,
            "time_spent": 0
        }
        self.reset_stats()
    
    def reset_stats(self):
        """Resets statistics counters."""
        self.stats = {key: 0 for key in self.stats}
    
    def unit_propagation(self, clauses, assignment, decision_level):
        """
        Performs unit propagation on the formula.
        Returns (True, None) if successful, (False, conflict_clause) if a conflict is found.
        """
        # Keep applying unit propagation until no more unit clauses are found
        propagated_something = True
        while propagated_something:
            propagated_something = False
            for clause in clauses:
                if clause_is_satisfied(clause, assignment):
                    continue
                
                unit_literal = get_unit_literal(clause, assignment)
                if unit_literal is not None:
                    self.stats["unit_propagations"] += 1
                    try:
                        assignment.assign(unit_literal, decision_level)
                        propagated_something = True
                    except ValueError:
                        # Conflict: we tried to assign a different value to an already assigned variable
                        return False, clause
                
                # Check if this clause has become conflicting
                if clause_is_conflicting(clause, assignment):
                    return False, clause
        
        return True, None

    def solve(self, clauses, num_variables):
        """
        Solves the SAT problem using DPLL.
        Returns (True, assignment) if satisfiable, (False, None) if unsatisfiable.
        """
        self.reset_stats()
        start_time = time.time()
        
        assignment = Assignment()
        result = self._dpll_recursive(clauses, assignment, 0, num_variables)
        
        self.stats["time_spent"] = time.time() - start_time
        return result
    
    def _dpll_recursive(self, clauses, assignment, decision_level, num_variables):
        """
        Recursive DPLL implementation.
        Returns (True, assignment) if satisfiable, (False, None) if unsatisfiable.
        """
        # Unit propagation
        success, conflict_clause = self.unit_propagation(clauses, assignment, decision_level)
        if not success:
            self.stats["backtracking_steps"] += 1
            return False, None
        
        # Check if all variables are assigned (formula is satisfied)
        if len(assignment.assigned_values) == num_variables:
            return True, assignment
        
        # Choose a variable to branch on
        var_to_branch = self.heuristic(assignment, num_variables)
        if var_to_branch is None:
            # This should not happen if there are unassigned variables
            raise ValueError("Heuristic failed to select an unassigned variable.")
        
        self.stats["decisions"] += 1
        
        # Try assigning True first
        literal = Literal(var_to_branch, False)  # Positive literal
        assignment.assign(literal, decision_level + 1)
        
        success, result_assignment = self._dpll_recursive(clauses, assignment, decision_level + 1, num_variables)
        if success:
            return True, result_assignment
        
        # If assigning True failed, backtrack and try assigning False
        assignment.backtrack_to_level(decision_level)
        
        literal = Literal(var_to_branch, True)  # Negative literal
        assignment.assign(literal, decision_level + 1)
        
        success, result_assignment = self._dpll_recursive(clauses, assignment, decision_level + 1, num_variables)
        if success:
            return True, result_assignment
        
        # If both assignments failed, backtrack
        assignment.backtrack_to_level(decision_level)
        self.stats["backtracking_steps"] += 1
        
        return False, None
    
    def solve_iterative(self, clauses, num_variables):
        """
        Solve the SAT problem using an iterative DPLL implementation.
        This shows how DPLL can be implemented without using recursion.
        Returns (True, assignment) if satisfiable, (False, None) if unsatisfiable.
        """
        self.reset_stats()
        start_time = time.time()
        
        assignment = Assignment()
        decision_level = 0
        
        # Trail of decisions (var_idx, tried_true)
        decision_trail = []
        
        while True:
            # Unit propagation
            success, conflict_clause = self.unit_propagation(clauses, assignment, decision_level)
            
            if not success:
                # Conflict, need to backtrack
                if not decision_trail:  # No more decisions to backtrack to
                    self.stats["time_spent"] = time.time() - start_time
                    return False, None
                
                # Backtrack
                self.stats["backtracking_steps"] += 1
                var_idx, tried_true = decision_trail.pop()
                decision_level -= 1
                
                # Clear all assignments at higher decision levels
                assignment.backtrack_to_level(decision_level)
                
                if not tried_true:
                    # If we tried assigning True and it failed, try False
                    assignment.assign(Literal(var_idx, True), decision_level + 1)
                    decision_trail.append((var_idx, True))
                    decision_level += 1
                # If we've tried both True and False, continue backtracking
                
                continue
            
            # Check if all variables are assigned (formula is satisfied)
            if len(assignment.assigned_values) == num_variables:
                self.stats["time_spent"] = time.time() - start_time
                return True, assignment
            
            # Choose a variable to branch on
            var_to_branch = self.heuristic(assignment, num_variables)
            if var_to_branch is None:
                # This should not happen
                raise ValueError("Heuristic failed to select an unassigned variable.")
            
            self.stats["decisions"] += 1
            
            # Try assigning True first
            assignment.assign(Literal(var_to_branch, False), decision_level + 1)
            decision_trail.append((var_to_branch, False))
            decision_level += 1
        
    def get_stats(self):
        """Returns the performance statistics of the solver."""
        return self.stats

if __name__ == "__main__":
    # Example usage
    from common.dimacs_parser import parse_dimacs_cnf
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python dpll.py [DIMACS_FILE] [heuristic_name?]")
        sys.exit(1)
    
    try:
        heuristic_name = sys.argv[2] if len(sys.argv) > 2 else "first_unassigned"
        
        clauses, num_vars, _ = parse_dimacs_cnf(sys.argv[1])
        solver = DPLLSolver(heuristic_name)
        
        print(f"Solving SAT instance with {num_vars} variables and {len(clauses)} clauses")
        print(f"Using heuristic: {heuristic_name}")
        
        satisfiable, assignment = solver.solve(clauses, num_vars)
        
        if satisfiable:
            print("SATISFIABLE")
            # Print the satisfying assignment in DIMACS format
            for var_idx in range(1, num_vars + 1):
                if var_idx in assignment.assigned_values:
                    val = assignment.assigned_values[var_idx]
                    print(f"{'+' if val else '-'}{var_idx}", end=" ")
            print()
        else:
            print("UNSATISFIABLE")
        
        stats = solver.get_stats()
        print(f"Statistics:")
        print(f"  Decisions: {stats['decisions']}")
        print(f"  Backtracking steps: {stats['backtracking_steps']}")
        print(f"  Unit propagations: {stats['unit_propagations']}")
        print(f"  Time spent: {stats['time_spent']:.6f} seconds")
    
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1) 