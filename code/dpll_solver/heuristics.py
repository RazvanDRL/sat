import random

def first_unassigned_heuristic(assignment, num_variables):
    """Selects the first unassigned variable by numerical order."""
    for i in range(1, num_variables + 1):
        if not assignment.is_assigned(i):
            return i
    return None # Should not happen if there are unassigned variables

def random_unassigned_heuristic(assignment, num_variables):
    """Selects a random unassigned variable."""
    unassigned_vars = []
    for i in range(1, num_variables + 1):
        if not assignment.is_assigned(i):
            unassigned_vars.append(i)
    if not unassigned_vars:
        return None
    return random.choice(unassigned_vars)


HEURISTICS = {
    "first_unassigned": first_unassigned_heuristic,
    "random_unassigned": random_unassigned_heuristic,
}

def get_heuristic(name):
    heuristic_fn = HEURISTICS.get(name)
    if heuristic_fn is None:
        raise ValueError(f"Unknown heuristic: {name}. Available: {list(HEURISTICS.keys())}")
    return heuristic_fn 