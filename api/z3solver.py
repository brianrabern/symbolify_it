from http.server import BaseHTTPRequestHandler
import json
import z3


class handler(BaseHTTPRequestHandler):

    def do_POST(self):
        self.send_response(200)
        self.send_header('Content-type', 'text/plain')
        self.end_headers()

        try:
            # Extract the formulas from the request body
            content_length = int(self.headers['Content-Length'])
            post_data = self.rfile.read(content_length)
            data = json.loads(post_data.decode('utf-8'))
            formula1 = data.get('formula1', '')
            formula2 = data.get('formula2', '')

            print('Received data:', data)
            result = self.check_equivalence(formula1, formula2)
            print('Result:', result)
            self.wfile.write(json.dumps(result).encode('utf-8'))
        except Exception as e:
            print('Error:', e)
            self.wfile.write(f"Error yo: {str(e)}".encode('utf-8'))

        return

    def check_equivalence(self, formula1, formula2):
        # Parse the SMT-LIB formulas using Z3 parser
        z3_formula1 = z3.parse_smt2_string(formula1)
        z3_formula2 = z3.parse_smt2_string(formula2)

        # Create the solver
        solver = z3.Solver()

        # Add the formulas to the solver
        solver.add(z3_formula1)
        solver.add(z3_formula2)

        # Check for logical equivalence
        result = solver.check()

        if result == z3.sat:
            return "The formulas are logically equivalent."
        elif result == z3.unsat:
            return "The formulas are not logically equivalent."
        else:
            return "Unable to determine the equivalence."
