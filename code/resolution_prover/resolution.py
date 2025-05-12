import sys
import time
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from common.structures import Literal

class ResolutionProver:
    """
    Implementation of the Resolution method for SAT proving.
    Resolution is a rule of inference that allows for the derivation of a new clause 
    from two clauses containing complementary literals.
    """
    def __init__(self):
        # Performance metrics
        self.stats = {
            "resolutions_performed": 0,
            "clauses_generated": 0,
            "time_spent": 0
        }
        self.reset_stats()
    
    def reset_stats(self):
        """Resets statistics counters."""
        self.stats = {key: 0 for key in self.stats}
    
    def resolve(self, clause1, clause2, pivot_var):
        """
        Applies the resolution rule on two clauses over a pivot variable.
        Returns None if no resolution is possible, otherwise returns the resolved clause.
        """
        # Find pivot literals in both clauses
        pivot_pos = None
        pivot_neg = None
        
        for lit in clause1:
            if lit.variable_index == pivot_var:
                if not lit.is_negated:
                    pivot_pos = lit
                else:
                    pivot_neg = lit
        
        for lit in clause2:
            if lit.variable_index == pivot_var:
                if not lit.is_negated:
                    pivot_pos = lit
                else:
                    pivot_neg = lit
        
        # No resolution possible if the pivot variable doesn't appear with opposite signs
        if (pivot_pos is None) or (pivot_neg is None):
            return None
        
        # Construct the resolvent clause (excluding pivot literals)
        resolvent = []
        
        # Add literals from clause 1 except pivot
        for lit in clause1:
            if lit.variable_index != pivot_var:
                resolvent.append(lit)
        
        # Add literals from clause 2 except pivot, avoiding duplicates
        for lit in clause2:
            if lit.variable_index != pivot_var and lit not in resolvent:
                resolvent.append(lit)
        
        return resolvent
    
    def is_tautology(self, clause):
        """Checks if a clause is a tautology (contains both p and ¬p for some variable)."""
        variables_pos = set()
        variables_neg = set()
        
        for lit in clause:
            var_idx = lit.variable_index
            if not lit.is_negated:
                variables_pos.add(var_idx)
            else:
                variables_neg.add(var_idx)
        
        # Check if any variable appears both positively and negatively
        for var_idx in variables_pos:
            if var_idx in variables_neg:
                return True
        
        return False
    
    def solve(self, clauses):
        """
        Applies resolution repeatedly until either the empty clause is derived (unsatisfiable)
        or no new clauses can be derived (satisfiable).
        Returns (is_satisfiable, final_clause_set).
        """
        self.reset_stats()
        start_time = time.time()
        
        # Make a copy of the clauses to avoid modifying the input
        current_clauses = clauses.copy()
        
        # Get all variables that appear in the clauses
        variables = set()
        for clause in current_clauses:
            for lit in clause:
                variables.add(lit.variable_index)
        
        # Find all possible resolvents and add them to the clause set
        new_clauses_added = True
        while new_clauses_added:
            new_clauses_added = False
            
            # Get pairs of clauses to attempt resolution
            clause_pairs = [(i, j) for i in range(len(current_clauses)) 
                           for j in range(i + 1, len(current_clauses))]
            
            for i, j in clause_pairs:
                clause1 = current_clauses[i]
                clause2 = current_clauses[j]
                
                # Try resolution on all possible pivot variables
                for pivot_var in variables:
                    resolvent = self.resolve(clause1, clause2, pivot_var)
                    
                    if resolvent is not None:
                        self.stats["resolutions_performed"] += 1
                        
                        # Check if resolvent is the empty clause
                        if not resolvent:
                            self.stats["time_spent"] = time.time() - start_time
                            return False, current_clauses  # Unsatisfiable
                        
                        # Skip tautologies
                        if self.is_tautology(resolvent):
                            continue
                        
                        # Check if this clause is new
                        if resolvent not in current_clauses:
                            current_clauses.append(resolvent)
                            self.stats["clauses_generated"] += 1
                            new_clauses_added = True
        
        # If we reach here, resolution reached a fixed point without deriving the empty clause
        self.stats["time_spent"] = time.time() - start_time
        return True, current_clauses  # Potentially satisfiable
    
    def get_stats(self):
        """Returns the performance statistics of the prover."""
        return self.stats

if __name__ == "__main__":
    # Example usage
    from common.dimacs_parser import parse_dimacs_cnf
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python resolution.py [DIMACS_FILE]")
        sys.exit(1)
    
    try:
        clauses, num_vars, _ = parse_dimacs_cnf(sys.argv[1])
        prover = ResolutionProver()
        
        print(f"Applying resolution to SAT instance with {num_vars} variables and {len(clauses)} clauses")
        
        satisfiable, final_clauses = prover.solve(clauses)
        
        if satisfiable:
            print("POTENTIALLY SATISFIABLE (Resolution cannot prove satisfiability)")
            print(f"Final clause set size: {len(final_clauses)}")
        else:
            print("UNSATISFIABLE (Empty clause derived)")
        
        stats = prover.get_stats()
        print(f"Statistics:")
        print(f"  Resolutions performed: {stats['resolutions_performed']}")
        print(f"  New clauses generated: {stats['clauses_generated']}")
        print(f"  Time spent: {stats['time_spent']:.6f} seconds")
    
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1) 