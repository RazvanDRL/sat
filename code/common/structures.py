class Literal:
    """Represents a literal (a variable or its negation)."""
    def __init__(self, variable_index, is_negated):
        if not isinstance(variable_index, int) or variable_index <= 0:
            raise ValueError("Variable index must be a positive integer.")
        self.variable_index = variable_index
        self.is_negated = bool(is_negated)

    def __eq__(self, other):
        if not isinstance(other, Literal):
            return False
        return self.variable_index == other.variable_index and self.is_negated == other.is_negated

    def __hash__(self):
        return hash((self.variable_index, self.is_negated))

    def __repr__(self):
        return f"{'-' if self.is_negated else ''}{self.variable_index}"

    def negated(self):
        """Returns the negation of this literal."""
        return Literal(self.variable_index, not self.is_negated)

class Assignment:
    """Manages the assignment of truth values to variables."""
    def __init__(self):
        # Stores variable_index -> bool (True for True, False for False)
        self.assigned_values = {}
        # Stores variable_index -> decision_level
        self.decision_levels = {}
        # Trail of assigned literals in order
        self.trail = []
        # Assignment order for variables
        self.assignment_order = {}
        # Current assignment order counter
        self.current_order = 0

    def assign(self, literal, decision_level):
        """Assigns a truth value to a variable based on the literal."""
        if literal.variable_index in self.assigned_values:
            # Check for consistency
            current_value = self.assigned_values[literal.variable_index]
            if current_value == literal.is_negated: # assigned True if literal is var, False if literal is ~var
                raise ValueError(f"Variable {literal.variable_index} already assigned conflicting value.")
            return # Already assigned consistently

        value_to_assign = not literal.is_negated
        self.assigned_values[literal.variable_index] = value_to_assign
        self.decision_levels[literal.variable_index] = decision_level
        self.trail.append(literal)
        # Track assignment order
        self.current_order += 1
        self.assignment_order[literal.variable_index] = self.current_order

    def unassign(self, literal):
        """Unassigns a truth value from a variable."""
        if literal.variable_index in self.assigned_values:
            del self.assigned_values[literal.variable_index]
            del self.decision_levels[literal.variable_index]
            # Remove from assignment order
            if literal.variable_index in self.assignment_order:
                del self.assignment_order[literal.variable_index]
            # More sophisticated trail management might be needed for CDCL
            # For simple DPLL, clearing from assigned_values is often enough for backtracking
            # However, a proper trail helps reconstruct states.
            # For this simple version, we'll find and remove the specific literal from the trail
            # A more robust trail would pop assignments made at a certain decision level.
            try:
                # This removal from trail is simplistic for basic DPLL.
                # CDCL would require more careful trail unwinding.
                self.trail = [l for l in self.trail if l.variable_index != literal.variable_index]
            except ValueError:
                pass # Should not happen if var was in assigned_values

    def is_assigned(self, variable_index):
        """Checks if a variable is assigned."""
        return variable_index in self.assigned_values

    def get_value(self, literal):
        """
        Gets the truth value of a literal under the current assignment.
        Returns True if the literal is true, False if false, None if unassigned.
        """
        if literal.variable_index not in self.assigned_values:
            return None
        
        variable_value = self.assigned_values[literal.variable_index]
        return variable_value if not literal.is_negated else not variable_value

    def __repr__(self):
        return f"Assignment: {self.assigned_values}"

    def get_assigned_literals_at_level(self, decision_level):
        """Returns literals assigned at a specific decision level."""
        # This is a simplified version. A real trail would be more structured.
        return [l for l in self.trail if self.decision_levels.get(l.variable_index) == decision_level]

    def backtrack_to_level(self, decision_level):
        """
        Removes assignments made at levels greater than 'decision_level'.
        For DPLL, this means removing assignments from the current level being backtracked from.
        """
        vars_to_unassign = [
            var_idx for var_idx, dl in self.decision_levels.items() if dl > decision_level
        ]
        for var_idx in vars_to_unassign:
            # Need to find the literal form to unassign
            # This is still a simplification. A proper trail makes this easier.
            val = self.assigned_values[var_idx]
            literal_to_unassign = Literal(var_idx, not val) # if val is True, unassign ~var, if False, unassign var
            
            # More robust unassignment that actually removes the specific assignment
            if var_idx in self.assigned_values:
                del self.assigned_values[var_idx]
            if var_idx in self.decision_levels:
                del self.decision_levels[var_idx]

        # Rebuild trail without the unassigned variables
        self.trail = [l for l in self.trail if l.variable_index not in vars_to_unassign]

    def get_assignment_order(self, var_index):
        """Returns the order in which a variable was assigned."""
        return self.assignment_order.get(var_index, 0)

def clause_is_satisfied(clause, assignment):
    """Checks if a clause is satisfied by the current assignment."""
    for lit in clause:
        lit_val = assignment.get_value(lit)
        if lit_val is True:
            return True
    return False

def clause_is_conflicting(clause, assignment):
    """Checks if a clause is conflicting (all literals false) under the assignment."""
    for lit in clause:
        lit_val = assignment.get_value(lit)
        if lit_val is True or lit_val is None: # If any literal is true or unassigned, not conflicting
            return False
    return True # All literals are false

def get_unit_literal(clause, assignment):
    """
    If the clause is a unit clause under the current assignment,
    returns the unit literal. Otherwise, returns None.
    A clause is unit if all but one of its literals are false, and that
    one literal is unassigned.
    """
    unassigned_literal = None
    false_literals_count = 0
    for lit in clause:
        val = assignment.get_value(lit)
        if val is True: # Clause is satisfied
            return None
        if val is False:
            false_literals_count += 1
        elif val is None:
            if unassigned_literal is not None: # More than one unassigned
                return None
            unassigned_literal = lit
            
    if unassigned_literal is not None and false_literals_count == len(clause) - 1:
        return unassigned_literal
    return None 