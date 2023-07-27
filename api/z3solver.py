from http.server import BaseHTTPRequestHandler
from z3 import Ints, Solver, sat, eval


class handler(BaseHTTPRequestHandler):

    def do_GET(self):
        self.send_response(200)
        self.send_header('Content-type', 'text/plain')
        self.end_headers()

        try:
            # Replace this with your desired expression
            expression = "(x > 5) & (y <= 10)"
            result = self.solve_with_z3(expression)
            self.wfile.write(result.encode('utf-8'))
        except Exception as e:
            self.wfile.write(f"Error: {str(e)}".encode('utf-8'))

        return

    def solve_with_z3(self, expression):
        x, y = Ints('x y')
        solver = Solver()
        # Use eval to parse the expression as Z3 constraints
        solver.add(eval(expression))
        if solver.check() == sat:
            model = solver.model()
            return f"Model: {model}"
        else:
            return "Expression is unsatisfiable"
