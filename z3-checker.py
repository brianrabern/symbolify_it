# this script was just for development and testing purposes. see api/z3-solver.py for the actual script

import z3


def check_satisfiability(smt_script):
    # Parse the SMT-LIB formula using Z3 parser
    parsed_formula = z3.parse_smt2_string(smt_script)

    z3_formula = z3.And(*parsed_formula)

    print(z3_formula)

    # Create the solver
    solver = z3.Solver()

    # Add the formula to the solver
    solver.add(z3_formula)

    # Check for satisfiability
    result = solver.check()

    return result


# Example usage:
smt_script = """
(declare-const P Bool)
(assert (and P (not P)))
"""


# """
# (declare-const P Bool)
# (assert (and P (not P)))
# """

result = check_satisfiability(smt_script)

if result == z3.sat:
    print("Satisfiable!")

elif result == z3.unsat:
    print("Unsatisfiable!")
else:
    print("Unknown result or an error occurred.")
