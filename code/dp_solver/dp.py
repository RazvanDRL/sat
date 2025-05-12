import sys
import time
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from common.structures import Literal, get_unit_literal
from collections import defaultdict

class DPSolver:
    """
    Implementation of the Davis-Putnam (DP) procedure for SAT solving.
    DP is a complete algorithm that eliminates variables through resolution
    rather than using backtracking like in DPLL.
    """
    def __init__(self):
        # Performance metrics
        self.stats = {
            "unit_propagations": 0,
            "pure_literal_eliminations": 0,
            "variable_eliminations": 0,
            "time_spent": 0
        }
        self.reset_stats()
    
    def reset_stats(self):
        """Resets statistics counters."""
        self.stats = {key: 0 for key in self.stats}
    
    def unit_propagation(self, clauses, assignment):
        """
        Performs unit propagation, removing satisfied clauses and falsified literals.
        Returns a new set of clauses with the unit propagation applied.
        """
        result = []
        propagated = False
        
        # Find unit clauses and add their literals to assignment
        for clause in clauses:
            if len(clause) == 1:
                literal = clause[0]
                var_idx = literal.variable_index
                is_negated = literal.is_negated
                
                if var_idx in assignment:
                    # Check for conflict
                    if assignment[var_idx] == is_negated:  # assigned True for a negative literal or vice versa
                        return None  # Conflict, formula is unsatisfiable
                else:
                    # Add to assignment
                    assignment[var_idx] = not is_negated  # Assign True for positive literal, False for negative
                    propagated = True
                    self.stats["unit_propagations"] += 1
        
        # Apply the assignment to all clauses
        for clause in clauses:
            new_clause = []
            satisfied = False
            
            for literal in clause:
                var_idx = literal.variable_index
                is_negated = literal.is_negated
                
                if var_idx in assignment:
                    # Check if literal is satisfied or falsified
                    if (assignment[var_idx] and not is_negated) or (not assignment[var_idx] and is_negated):
                        satisfied = True
                        break
                    # If literal is falsified, don't add it to the new clause
                else:
                    # Literal is still undetermined
                    new_clause.append(literal)
            
            if not satisfied and not new_clause:
                return None  # Empty clause, formula is unsatisfiable
            
            if not satisfied:
                result.append(new_clause)
        
        # If we've applied a unit propagation, recursively apply unit propagation again
        if propagated:
            return self.unit_propagation(result, assignment)
        
        return result
    
    def pure_literal_elimination(self, clauses):
        """
        Eliminates pure literals (variables that appear always with the same sign).
        Returns a new set of clauses with pure literals removed.
        """
        if not clauses:
            return []  # Empty formula is satisfiable
        
        # Count positive and negative occurrences of each variable
        pos_occurrences = defaultdict(int)
        neg_occurrences = defaultdict(int)
        
        for clause in clauses:
            for literal in clause:
                var_idx = literal.variable_index
                if literal.is_negated:
                    neg_occurrences[var_idx] += 1
                else:
                    pos_occurrences[var_idx] += 1
        
        # Find pure literals
        pure_literals = []
        for var_idx in set(pos_occurrences.keys()) | set(neg_occurrences.keys()):
            if pos_occurrences[var_idx] > 0 and neg_occurrences[var_idx] == 0:
                pure_literals.append(Literal(var_idx, False))  # Pure positive
                self.stats["pure_literal_eliminations"] += 1
            elif neg_occurrences[var_idx] > 0 and pos_occurrences[var_idx] == 0:
                pure_literals.append(Literal(var_idx, True))  # Pure negative
                self.stats["pure_literal_eliminations"] += 1
        
        # Remove clauses containing pure literals
        if pure_literals:
            result = []
            for clause in clauses:
                keep_clause = True
                for pure_lit in pure_literals:
                    if pure_lit in clause:
                        keep_clause = False
                        break
                if keep_clause:
                    result.append(clause)
            return result
        
        return clauses
    
    def variable_elimination(self, clauses, var_to_eliminate):
        """
        Eliminates a variable by applying resolution on all clauses where it appears.
        Returns a new set of clauses with the variable eliminated.
        """
        # Separate clauses into positive, negative, and irrelevant for this variable
        pos_clauses = []  # Clauses with positive occurrence of the variable
        neg_clauses = []  # Clauses with negative occurrence of the variable
        other_clauses = []  # Clauses without the variable
        
        for clause in clauses:
            has_pos = False
            has_neg = False
            
            for literal in clause:
                if literal.variable_index == var_to_eliminate:
                    if literal.is_negated:
                        has_neg = True
                    else:
                        has_pos = True
            
            if has_pos and not has_neg:
                pos_clauses.append(clause)
            elif has_neg and not has_pos:
                neg_clauses.append(clause)
            elif has_pos and has_neg:
                # Tautological clause, can be removed
                continue
            else:
                other_clauses.append(clause)
        
        # Apply resolution between all pairs of positive and negative clauses
        resolvents = []
        for pos_clause in pos_clauses:
            for neg_clause in neg_clauses:
                # Create resolvent by combining the clauses and removing the variable
                resolvent = []
                
                # Add literals from positive clause except the eliminated variable
                for lit in pos_clause:
                    if lit.variable_index != var_to_eliminate:
                        resolvent.append(lit)
                
                # Add literals from negative clause except the eliminated variable
                for lit in neg_clause:
                    if lit.variable_index != var_to_eliminate and lit not in resolvent:
                        resolvent.append(lit)
                
                # Check for tautology (contains both p and ¬p for some variable)
                is_tautology = False
                vars_pos = set()
                vars_neg = set()
                
                for lit in resolvent:
                    if not lit.is_negated:
                        vars_pos.add(lit.variable_index)
                    else:
                        vars_neg.add(lit.variable_index)
                
                for var_idx in vars_pos:
                    if var_idx in vars_neg:
                        is_tautology = True
                        break
                
                if not is_tautology:
                    resolvents.append(resolvent)
        
        # The result is the combination of resolvents and irrelevant clauses
        self.stats["variable_eliminations"] += 1
        return other_clauses + resolvents
    
    def select_variable(self, clauses):
        """
        Selects a variable to eliminate based on a simple heuristic.
        Here we'll use the variable that appears in the smallest number of clauses.
        """
        if not clauses:
            return None
        
        # Count occurrences of each variable
        var_counts = defaultdict(int)
        for clause in clauses:
            for lit in clause:
                var_counts[lit.variable_index] += 1
        
        # Select the variable with the fewest occurrences
        if not var_counts:
            return None
        
        return min(var_counts.items(), key=lambda x: x[1])[0]
    
    def solve(self, clauses):
        """
        Solves the SAT problem using the Davis-Putnam procedure.
        Returns (is_satisfiable, assignment) where assignment is None if unsatisfiable.
        """
        self.reset_stats()
        start_time = time.time()
        
        # Copy clauses to avoid modifying input
        current_clauses = [c[:] for c in clauses]
        assignment = {}
        
        # Apply unit propagation
        current_clauses = self.unit_propagation(current_clauses, assignment)
        if current_clauses is None:
            self.stats["time_spent"] = time.time() - start_time
            return False, None
        
        # Apply pure literal elimination
        current_clauses = self.pure_literal_elimination(current_clauses)
        
        # If formula is empty, it's satisfiable
        if not current_clauses:
            self.stats["time_spent"] = time.time() - start_time
            return True, assignment
        
        # Main loop: select a variable and eliminate it
        while current_clauses:
            var_to_eliminate = self.select_variable(current_clauses)
            if var_to_eliminate is None:
                break
            
            current_clauses = self.variable_elimination(current_clauses, var_to_eliminate)
            
            # Check if we've derived the empty clause
            if any(len(c) == 0 for c in current_clauses):
                self.stats["time_spent"] = time.time() - start_time
                return False, None
            
            # After variable elimination, try unit propagation and pure literal elimination again
            current_clauses = self.unit_propagation(current_clauses, assignment)
            if current_clauses is None:
                self.stats["time_spent"] = time.time() - start_time
                return False, None
            
            current_clauses = self.pure_literal_elimination(current_clauses)
            
            # If formula becomes empty, it's satisfiable
            if not current_clauses:
                self.stats["time_spent"] = time.time() - start_time
                return True, assignment
        
        # If we reach here with no clauses left, the formula is satisfiable
        # If there are still clauses, but we couldn't eliminate more variables,
        # we might need to use a more complete approach like DPLL in practical scenarios.
        # However, for completeness, we'll say it's satisfiable if no empty clause was derived.
        self.stats["time_spent"] = time.time() - start_time
        return not any(len(c) == 0 for c in current_clauses), assignment
    
    def get_stats(self):
        """Returns the performance statistics of the solver."""
        return self.stats

if __name__ == "__main__":
    # Example usage
    from common.dimacs_parser import parse_dimacs_cnf
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python dp.py [DIMACS_FILE]")
        sys.exit(1)
    
    try:
        clauses, num_vars, _ = parse_dimacs_cnf(sys.argv[1])
        solver = DPSolver()
        
        print(f"Solving SAT instance with {num_vars} variables and {len(clauses)} clauses using Davis-Putnam")
        
        satisfiable, assignment = solver.solve(clauses)
        
        if satisfiable:
            print("SATISFIABLE")
            # Print the partial assignment (might not be complete)
            for var_idx, val in assignment.items():
                print(f"{'+' if val else '-'}{var_idx}", end=" ")
            print("\n(Note: This may be a partial assignment. Some variables might be unassigned.)")
        else:
            print("UNSATISFIABLE")
        
        stats = solver.get_stats()
        print(f"Statistics:")
        print(f"  Unit propagations: {stats['unit_propagations']}")
        print(f"  Pure literal eliminations: {stats['pure_literal_eliminations']}")
        print(f"  Variable eliminations: {stats['variable_eliminations']}")
        print(f"  Time spent: {stats['time_spent']:.6f} seconds")
    
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1) 