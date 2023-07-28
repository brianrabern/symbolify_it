// Generated automatically by nearley, version 2.20.1
// http://github.com/Hardmath123/nearley
(function () {
  function id(x) {
    return x[0];
  }
  var grammarPred = {
    Lexer: undefined,
    ParserRules: [
      { name: "wff", symbols: ["predicate", "term_list"] },
      { name: "wff", symbols: [{ literal: "¬" }, "wff"] },
      {
        name: "wff",
        symbols: [
          { literal: "(" },
          "wff",
          "ws",
          "connective",
          "ws",
          "wff",
          { literal: ")" },
        ],
      },
      { name: "wff", symbols: [{ literal: "∀" }, "variable", "wff"] },
      { name: "wff", symbols: [{ literal: "∃" }, "variable", "wff"] },
      { name: "term", symbols: ["variable"] },
      { name: "term", symbols: ["constant"] },
      { name: "term_list", symbols: ["term"] },
      { name: "term_list", symbols: ["term_list", "term"] },
      { name: "quantifier", symbols: [{ literal: "∀" }] },
      { name: "quantifier", symbols: [{ literal: "∃" }] },
      { name: "connective", symbols: [{ literal: "∧" }] },
      { name: "connective", symbols: [{ literal: "∨" }] },
      { name: "connective", symbols: [{ literal: "→" }] },
      { name: "connective", symbols: [{ literal: "↔" }] },
      { name: "predicate", symbols: [/[A-Z]/] },
      { name: "predicate", symbols: [{ literal: "F" }, "digit"] },
      { name: "variable", symbols: [/[s-z]/] },
      { name: "variable", symbols: [{ literal: "x" }, "digit"] },
      { name: "constant", symbols: [/[a-r]/] },
      { name: "constant", symbols: [{ literal: "a" }, "digit"] },
      { name: "digit", symbols: [/[1-9]/] },
      { name: "digit", symbols: [/[1-9]/, /[0-9]/] },
      { name: "ws", symbols: [] },
      { name: "ws", symbols: [{ literal: " " }] },
    ],
    ParserStart: "wff",
  };
  if (typeof module !== "undefined" && typeof module.exports !== "undefined") {
    module.exports = grammarPred;
  } else {
    window.grammar = grammarPred;
  }
})();
