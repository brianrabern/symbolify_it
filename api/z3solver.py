from http.server import BaseHTTPRequestHandler
import z3


class handler(BaseHTTPRequestHandler):

    def do_GET(self):
        self.send_response(200)
        self.send_header('Content-type', 'text/plain')
        self.end_headers()

        try:
            # Replace this with your desired expression
            expression = "(and P Q)"
            result = self.solve_with_z3(expression)
            self.wfile.write(result.encode('utf-8'))
        except Exception as e:
            self.wfile.write(f"Error: {str(e)}".encode('utf-8'))

        return

    def solve_with_z3(self, expression):
        # Parse the SMT-LIB formula using Z3 parser
        z3_formula = z3.parse_smt2_string(expression)

        # Create the solver
        solver = z3.Solver()

        # Add the formula to the solver
        solver.add(z3_formula)

        # Check for satisfiability
        result = solver.check()

        if result == z3.sat:
            return "The formula is satisfiable."
        elif result == z3.unsat:
            return "The formula is unsatisfiable."
        else:
            return "Unable to determine the satisfiability."
