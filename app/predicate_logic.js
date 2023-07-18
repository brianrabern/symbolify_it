// Generated automatically by nearley, version 2.20.1
// http://github.com/Hardmath123/nearley
(function () {
function id(x) { return x[0]; }
var grammar = {
    Lexer: undefined,
    ParserRules: [
    {"name": "wff", "symbols": ["predicate", {"literal":"("}, "term_list", {"literal":")"}]},
    {"name": "wff", "symbols": [{"literal":"¬"}, "wff"]},
    {"name": "wff", "symbols": [{"literal":"("}, "wff", "connective", "wff", {"literal":")"}]},
    {"name": "wff", "symbols": [{"literal":"∀"}, "variable", "wff"]},
    {"name": "wff", "symbols": [{"literal":"∃"}, "variable", "wff"]},
    {"name": "term", "symbols": ["variable"]},
    {"name": "term", "symbols": ["constant"]},
    {"name": "term_list", "symbols": ["term"]},
    {"name": "term_list", "symbols": ["term", {"literal":","}, "term_list"]},
    {"name": "quantifier", "symbols": [{"literal":"∀"}]},
    {"name": "quantifier", "symbols": [{"literal":"∃"}]},
    {"name": "connective", "symbols": [{"literal":"∧"}]},
    {"name": "connective", "symbols": [{"literal":"∨"}]},
    {"name": "connective", "symbols": [{"literal":"→"}]},
    {"name": "connective", "symbols": [{"literal":"↔"}]},
    {"name": "predicate", "symbols": [/[A-Z]/]},
    {"name": "variable", "symbols": [/[s-z]/]},
    {"name": "constant", "symbols": [/[a-r]/]}
]
  , ParserStart: "wff"
}
if (typeof module !== 'undefined'&& typeof module.exports !== 'undefined') {
   module.exports = grammar;
} else {
   window.grammar = grammar;
}
})();
