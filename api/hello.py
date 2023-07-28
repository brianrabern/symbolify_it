# hello.py

from http.server import BaseHTTPRequestHandler
import json
import z3


class handler(BaseHTTPRequestHandler):

    def do_POST(self):
        self.send_response(200)
        self.send_header('Content-Type', 'text/plain')
        self.end_headers()

        try:
            content_length = int(self.headers['Content-Length'])
            post_data = self.rfile.read(content_length)
            data = json.loads(post_data.decode('utf-8'))
            formula = data.get('formula', '')

            result = self.check_formula(formula)
            self.wfile.write(result.encode('utf-8'))
        except Exception as e:
            self.wfile.write(f"Error: {str(e)}".encode('utf-8'))

    def check_formula(self, formula):
        try:
            # Parse the SMT-LIB formula using Z3 parser
            parsed_formula = z3.parse_smt2_string(formula)

            z3_formula = z3.And(*parsed_formula)

            print(z3_formula)

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
        except Exception as e:
            return f"Error: {str(e)}"
