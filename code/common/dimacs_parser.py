from .structures import Literal

def parse_dimacs_cnf(filepath):
    """
    Parses a CNF formula from a DIMACS file.
    Returns a tuple: (list_of_clauses, num_variables, num_clauses_header)
    Each clause is a list of Literal objects.
    num_variables is the number of variables declared in the header.
    num_clauses_header is the number of clauses declared in the header.
    """
    clauses = []
    num_variables = 0
    num_clauses_header = 0
    parsed_clauses_count = 0

    try:
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                if line.startswith('c'): # Comment line
                    continue
                if line.startswith('p'): # Problem line: p cnf <num_vars> <num_clauses>
                    parts = line.split()
                    if len(parts) != 4 or parts[1] != 'cnf':
                        raise ValueError(f"Invalid problem line format: {line}")
                    num_variables = int(parts[2])
                    num_clauses_header = int(parts[3])
                    if num_variables < 0 or num_clauses_header < 0:
                         raise ValueError("Number of variables and clauses must be non-negative.")
                    continue
                
                # Clause line: space-separated integers, ending with 0
                literals_str = line.split()
                if not literals_str or literals_str[-1] != '0':
                    # Gracefully skip lines that are not comments, problem line, or valid clauses
                    # Or raise error for stricter parsing:
                    # raise ValueError(f"Clause line must end with 0: {line}")
                    print(f"Warning: Malformed line (not ending in 0 or not a standard line): {line}")
                    continue

                clause = []
                for lit_str in literals_str[:-1]: # Exclude the trailing 0
                    try:
                        val = int(lit_str)
                        if val == 0:
                            raise ValueError("Literal 0 is not allowed in DIMACS.") # Should be caught by [-1] !='0' but good for robustness
                        var_index = abs(val)
                        if var_index > num_variables and num_variables > 0: # Allow if num_variables not yet defined (e.g. header after clauses)
                            # This could be a warning or an error depending on strictness
                            print(f"Warning: Literal {var_index} exceeds declared num_variables {num_variables} in line: {line}")
                            # To be very strict, you might want to raise an error or cap num_variables dynamically.
                            # For now, we will allow it but it might indicate a malformed file or needs dynamic num_vars update.
                        is_negated = val < 0
                        clause.append(Literal(var_index, is_negated))
                    except ValueError:
                        raise ValueError(f"Invalid literal format '{lit_str}' in line: {line}")
                
                if clause: # Only add non-empty clauses
                    clauses.append(clause)
                    parsed_clauses_count += 1
    
    except FileNotFoundError:
        raise FileNotFoundError(f"Error: File not found at {filepath}")
    except Exception as e:
        raise Exception(f"Error parsing DIMACS file {filepath}: {e}")

    if num_clauses_header > 0 and parsed_clauses_count != num_clauses_header:
        print(f"Warning: Number of parsed clauses ({parsed_clauses_count}) does not match header ({num_clauses_header}).")

    # Determine the actual maximum variable index if not strictly adhering to header
    max_var_in_clauses = 0
    for clause in clauses:
        for lit in clause:
            if lit.variable_index > max_var_in_clauses:
                max_var_in_clauses = lit.variable_index
    
    # If num_variables from header was 0 or less than actual variables, update it.
    if num_variables == 0 or num_variables < max_var_in_clauses:
        # print(f"Warning: Updating num_variables from header ({num_variables}) to max found in clauses ({max_var_in_clauses}).")
        num_variables = max_var_in_clauses
        
    return clauses, num_variables, num_clauses_header

if __name__ == '__main__':
    # Example usage (assuming you have a test.cnf file in the same directory or provide a full path)
    # Create a dummy test.cnf for this example to run:
    # c This is a comment
    # p cnf 3 2
    # 1 -2 0
    # -1 2 3 0
    try:
        dummy_cnf_content = """
        c This is a comment
        p cnf 3 2
        1 -2 0
        -1 2 3 0
        2 -3 0
        """
        with open("test.cnf", "w") as f_dummy:
            f_dummy.write(dummy_cnf_content)
        
        clauses, num_vars, num_clauses_h = parse_dimacs_cnf("test.cnf")
        print(f"Successfully parsed {len(clauses)} clauses with {num_vars} variables (header said {num_clauses_h} clauses).")
        for i, clause in enumerate(clauses):
            print(f"Clause {i+1}: {clause}")

        # Test with a malformed file
        malformed_cnf_content = """
        p cnf 2 1
        1 2 3  c no zero ending
        """
        with open("malformed.cnf", "w") as f_malformed:
            f_malformed.write(malformed_cnf_content)
        # clauses, num_vars, num_clauses_h = parse_dimacs_cnf("malformed.cnf") # This would print a warning

    except Exception as e:
        print(e) 