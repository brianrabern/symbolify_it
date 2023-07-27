from http.server import BaseHTTPRequestHandler
from z3 import Solver


class handler(BaseHTTPRequestHandler):

    def do_GET(self):
        self.send_response(200)
        self.send_header('Content-type', 'text/plain')
        self.end_headers()
        solver = Solver()
        print(solver)
        expression = "(x > 5) & (y <= 10)"
        self.wfile.write(expression.encode('utf-8'))

        return
