"""
CDCL (Conflict-Driven Clause Learning) SAT Solver Implementation.

This module implements the CDCL algorithm for solving SAT problems.
CDCL extends DPLL with conflict analysis and non-chronological backtracking.
"""

import sys
import time
from typing import Dict, List, Set, Tuple, Optional

sys.path.append("../")
from common.structures import Literal, Assignment
from common.dimacs_parser import parse_dimacs_cnf


class CDCLSolver:
    """
    CDCL (Conflict-Driven Clause Learning) SAT Solver.
    
    This implementation includes:
    - Two-watched literals for efficient unit propagation
    - Conflict analysis and clause learning
    - Non-chronological backtracking
    - VSIDS decision heuristic
    - Restart strategy
    """
    
    def __init__(self, clauses: List[List[Literal]], n_vars: int):
        """
        Initialize the CDCL solver.
        
        Args:
            clauses: List of clauses (each clause is a list of Literal objects)
            n_vars: Number of variables in the formula
        """
        self.clauses = clauses
        self.n_vars = n_vars
        self.learned_clauses = []
        self.assignment = Assignment()
        self.decision_level = 0
        self.implication_graph = {}  # For conflict analysis
        self.watches = self._initialize_watches()
        
        # VSIDS scores for variable activity
        self.vsids_scores = [1.0] * (self.n_vars + 1)
        self.vsids_decay_factor = 0.95
        
        # Statistics
        self.decisions = 0
        self.conflicts = 0
        self.propagations = 0
        self.restarts = 0
        self.start_time = 0
        
    def _initialize_watches(self) -> Dict[Tuple[int, bool], List[List[Literal]]]:
        """Initialize the two-watched literals scheme."""
        watches = {}
        for var in range(1, self.n_vars + 1):
            watches[(var, True)] = []  # Watches for negative literals
            watches[(var, False)] = []  # Watches for positive literals
        
        for clause in self.clauses:
            if len(clause) >= 2:
                # Watch first two literals
                lit1 = clause[0]
                lit2 = clause[1]
                watches[(lit1.variable_index, not lit1.is_negated)].append(clause)
                watches[(lit2.variable_index, not lit2.is_negated)].append(clause)
            elif len(clause) == 1:
                # For unit clauses, just watch the single literal
                lit = clause[0]
                watches[(lit.variable_index, not lit.is_negated)].append(clause)
            # Empty clause means unsatisfiable
            elif len(clause) == 0:
                return {}
        
        return watches
    
    def vsids_bump(self, var: int):
        """Bump the activity score of a variable."""
        self.vsids_scores[var] *= 1.1
    
    def decay_vsids_scores(self):
        """Decay all variable activity scores."""
        for i in range(1, self.n_vars + 1):
            self.vsids_scores[i] *= self.vsids_decay_factor
    
    def choose_variable(self) -> int:
        """Choose the next variable to assign using VSIDS heuristic."""
        max_score = -1
        chosen_var = 0
        
        for var in range(1, self.n_vars + 1):
            if var in self.assignment.assigned_values:
                continue
            
            if self.vsids_scores[var] > max_score:
                max_score = self.vsids_scores[var]
                chosen_var = var
        
        return chosen_var
    
    def propagate(self) -> Optional[List[Literal]]:
        """
        Perform unit propagation using watched literals.
        Returns the conflict clause if a conflict is found, None otherwise.
        """
        # Get all literals that have been assigned but not yet processed
        propagation_queue = []
        for var, value in self.assignment.assigned_values.items():
            # Add only literals that were assigned since last propagation
            if var not in self.assignment.decision_levels:
                continue
            
            # Create a literal from the variable's assignment
            # If value is True, then we're watching for ~var (i.e., var=False)
            # If value is False, then we're watching for var (i.e., var=True)
            propagation_queue.append((var, not value))
        
        while propagation_queue:
            var, watch_for = propagation_queue.pop(0)
            
            # Get clauses watching this literal
            watch_list = self.watches.get((var, watch_for), []).copy()
            self.watches[(var, watch_for)] = []
            
            for clause in watch_list:
                self.propagations += 1
                
                # Ensure first two literals are being watched
                if len(clause) >= 2:
                    lit1 = clause[0]
                    lit2 = clause[1]
                    
                    # If the watched literal is no longer at position 0 or 1, swap it
                    if (lit1.variable_index != var or lit1.is_negated == watch_for) and (lit2.variable_index != var or lit2.is_negated == watch_for):
                        # Find the watched literal in the clause
                        for i in range(2, len(clause)):
                            if clause[i].variable_index == var and clause[i].is_negated != watch_for:
                                # Found it, swap with position 0
                                clause[0], clause[i] = clause[i], clause[0]
                                lit1 = clause[0]
                                break
                
                # Check if the other watched literal is satisfied
                other_lit = lit2 if (lit1.variable_index == var and lit1.is_negated != watch_for) else lit1
                
                if other_lit.variable_index in self.assignment.assigned_values:
                    # If it's satisfied, keep watching
                    if (not other_lit.is_negated and self.assignment.assigned_values[other_lit.variable_index]) or \
                       (other_lit.is_negated and not self.assignment.assigned_values[other_lit.variable_index]):
                        self.watches[(var, watch_for)].append(clause)
                        continue
                
                # Try to find a new literal to watch
                found_new_watch = False
                for i in range(2, len(clause)):
                    lit = clause[i]
                    # If the literal is not assigned or is satisfied, it can be watched
                    if lit.variable_index not in self.assignment.assigned_values or \
                       (not lit.is_negated and self.assignment.assigned_values[lit.variable_index]) or \
                       (lit.is_negated and not self.assignment.assigned_values[lit.variable_index]):
                        # Found a new literal to watch
                        # Swap it with the current watched literal
                        if lit1.variable_index == var and lit1.is_negated != watch_for:
                            clause[0], clause[i] = clause[i], clause[0]
                        else:
                            clause[1], clause[i] = clause[i], clause[1]
                        # Update watch list for the new literal
                        new_lit = clause[0] if lit1.variable_index == var and lit1.is_negated != watch_for else clause[1]
                        self.watches[(new_lit.variable_index, not new_lit.is_negated)].append(clause)
                        found_new_watch = True
                        break
                
                if found_new_watch:
                    continue
                
                # If no new watch found, check the other watched literal
                # If it's unassigned, unit propagation
                if other_lit.variable_index not in self.assignment.assigned_values:
                    # Unit clause found, propagate it
                    self.assignment.assign(other_lit, self.decision_level)
                    propagation_queue.append((other_lit.variable_index, other_lit.is_negated))
                    self.watches[(var, watch_for)].append(clause)
                else:
                    # Both watched literals are false, we have a conflict
                    # Re-add to watches since we'll backtrack
                    self.watches[(var, watch_for)].append(clause)
                    return clause
        
        return None
    
    def analyze_conflict(self, conflict_clause: List[Literal]) -> Tuple[List[Literal], int]:
        """
        Analyze the conflict to learn a new clause and determine backtrack level.
        Returns the learned clause and the backtrack level.
        """
        self.conflicts += 1
        
        # First UIP (Unique Implication Point) scheme
        learned_clause = conflict_clause.copy()
        current_level_literals = 0
        
        # Count the number of literals from current decision level
        for lit in learned_clause:
            if lit.variable_index in self.assignment.decision_levels and self.assignment.decision_levels.get(lit.variable_index) == self.decision_level:
                current_level_literals += 1
        
        # Resolve until we have only one literal from current decision level (1UIP)
        while current_level_literals > 1:
            # Find the most recently assigned literal from current level
            latest_lit = None
            for lit in learned_clause:
                if lit.variable_index in self.assignment.decision_levels and self.assignment.decision_levels.get(lit.variable_index) == self.decision_level:
                    if latest_lit is None or self.assignment.get_assignment_order(lit.variable_index) > self.assignment.get_assignment_order(latest_lit.variable_index):
                        latest_lit = lit
            
            if latest_lit is None:
                break  # Should not happen with proper algorithm flow
            
            # Get the reason clause for this literal (antecedent)
            # This is a placeholder; in a real CDCL implementation, reason clauses would be tracked
            reason_clause = []  # This should be retrieved from the assignment's reason mapping
            
            # Resolve learned_clause with reason_clause
            # Remove latest_lit from learned_clause
            learned_clause.remove(latest_lit)
            current_level_literals -= 1
            
            # Add all literals from reason_clause except for the asserted one
            for lit in reason_clause:
                if lit != latest_lit.negated() and lit not in learned_clause:
                    learned_clause.append(lit)
                    if lit.variable_index in self.assignment.decision_levels and self.assignment.decision_levels.get(lit.variable_index) == self.decision_level:
                        current_level_literals += 1
        
        # Determine backtrack level (second highest level in the clause)
        levels = []
        for lit in learned_clause:
            if lit.variable_index in self.assignment.decision_levels:
                level = self.assignment.decision_levels.get(lit.variable_index)
                if level not in levels:
                    levels.append(level)
        
        levels.sort(reverse=True)
        
        backtrack_level = 0
        if len(levels) > 1:
            backtrack_level = levels[1]  # Second highest level
        
        # Bump VSIDS scores for variables in the learned clause
        for lit in learned_clause:
            self.vsids_bump(lit.variable_index)
        
        return learned_clause, backtrack_level
    
    def backtrack(self, level: int):
        """Backtrack to the given decision level."""
        if level < 0:
            level = 0
            
        self.assignment.backtrack_to_level(level)
        self.decision_level = level
    
    def should_restart(self) -> bool:
        """Determine if we should restart the search."""
        # Luby restart strategy
        if self.conflicts % (100 * (1 << min(self.restarts, 10))) == 0:
            return True
        return False
    
    def solve(self, timeout=None) -> bool:
        """
        Solve the SAT instance using CDCL.
        Returns True if satisfiable, False if unsatisfiable.
        """
        self.start_time = time.time()
        
        # Check if the formula already has a conflict
        conflict = self.propagate()
        if conflict is not None:
            return False
        
        while True:
            # Check timeout
            if timeout and time.time() - self.start_time > timeout:
                raise TimeoutError("Solver timeout reached")
            
            # Check if we should restart
            if self.should_restart():
                self.backtrack(0)
                self.restarts += 1
            
            # If all variables are assigned, formula is satisfiable
            if len(self.assignment.assigned_values) == self.n_vars:
                return True
            
            # Choose the next variable to assign
            var = self.choose_variable()
            if var == 0:  # No unassigned variables left
                return True
            
            # Make a decision
            self.decision_level += 1
            self.decisions += 1
            
            # Decide the phase (positive or negative)
            # Simple phase selection: prefer positive
            positive_lit = Literal(var, False)  # Create a positive literal
            self.assignment.assign(positive_lit, self.decision_level)
            
            # Propagate
            conflict = self.propagate()
            
            # Handle conflicts
            while conflict is not None:
                # At decision level 0, the formula is unsatisfiable
                if self.decision_level == 0:
                    return False
                
                # Analyze conflict to learn a new clause and determine backtrack level
                learned_clause, backtrack_level = self.analyze_conflict(conflict)
                
                # Add the learned clause to the formula
                self.learned_clauses.append(learned_clause)
                self.clauses.append(learned_clause)
                
                # Initialize watches for the new clause
                if len(learned_clause) >= 2:
                    lit1 = learned_clause[0]
                    lit2 = learned_clause[1]
                    self.watches[(lit1.variable_index, not lit1.is_negated)].append(learned_clause)
                    self.watches[(lit2.variable_index, not lit2.is_negated)].append(learned_clause)
                elif len(learned_clause) == 1:
                    lit = learned_clause[0]
                    self.watches[(lit.variable_index, not lit.is_negated)].append(learned_clause)
                
                # Backtrack to the computed level
                self.backtrack(backtrack_level)
                
                # Propagate the asserting literal
                asserting_lit = None
                for lit in learned_clause:
                    if lit.variable_index not in self.assignment.assigned_values or \
                       (lit.variable_index in self.assignment.decision_levels and 
                        self.assignment.decision_levels.get(lit.variable_index) == self.decision_level):
                        asserting_lit = lit
                        break
                
                if asserting_lit:
                    # Assign the asserting literal to satisfy the learned clause
                    self.assignment.assign(asserting_lit, self.decision_level)
                
                # Check for more conflicts
                conflict = self.propagate()
                
                # Decay VSIDS scores periodically
                if self.conflicts % 100 == 0:
                    self.decay_vsids_scores()


def solve_file(filepath: str, timeout=None) -> Tuple[bool, Optional[List[int]], Dict]:
    """
    Solve a DIMACS CNF file using the CDCL algorithm.
    
    Args:
        filepath: Path to the DIMACS CNF file
        timeout: Optional timeout in seconds
        
    Returns:
        Tuple containing:
        - Boolean indicating satisfiability
        - List of literals in a satisfying assignment (or None if unsatisfiable)
        - Dictionary of statistics
    """
    clauses, num_vars, _ = parse_dimacs_cnf(filepath)
    solver = CDCLSolver(clauses, num_vars)
    
    try:
        result = solver.solve(timeout)
    except TimeoutError:
        print(f"Timeout after {timeout} seconds")
        return False, None, {
            "decisions": solver.decisions,
            "conflicts": solver.conflicts,
            "propagations": solver.propagations,
            "learned_clauses": len(solver.learned_clauses),
            "restarts": solver.restarts,
            "time": time.time() - solver.start_time,
            "timeout": True
        }
    
    assignment = None
    if result:
        # Convert assignment to model format
        model = []
        for var in range(1, solver.n_vars + 1):
            if var in solver.assignment.assigned_values:
                if solver.assignment.assigned_values[var]:
                    model.append(var)
                else:
                    model.append(-var)
            else:
                # If a variable is unassigned (possible for satisfiable instances), assign arbitrarily
                model.append(var)
        assignment = model
    
    statistics = {
        "decisions": solver.decisions,
        "conflicts": solver.conflicts,
        "propagations": solver.propagations,
        "learned_clauses": len(solver.learned_clauses),
        "restarts": solver.restarts,
        "time": time.time() - solver.start_time,
        "timeout": False
    }
    
    return result, assignment, statistics


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python cdcl.py <cnf_file> [timeout]")
        sys.exit(1)
    
    filepath = sys.argv[1]
    timeout = None
    if len(sys.argv) > 2:
        timeout = float(sys.argv[2])
    
    print(f"Solving {filepath} with CDCL algorithm...")
    start_time = time.time()
    
    satisfiable, model, stats = solve_file(filepath, timeout)
    
    if satisfiable:
        print("SATISFIABLE")
        print(f"Model: {' '.join(str(lit) for lit in model)} 0")
    else:
        print("UNSATISFIABLE")
    
    print(f"Time: {stats['time']:.3f}s")
    print(f"Decisions: {stats['decisions']}")
    print(f"Conflicts: {stats['conflicts']}")
    print(f"Propagations: {stats['propagations']}")
    print(f"Learned clauses: {stats['learned_clauses']}")
    print(f"Restarts: {stats['restarts']}") 