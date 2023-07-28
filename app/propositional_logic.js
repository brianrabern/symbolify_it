// Generated automatically by nearley, version 2.20.1
// http://github.com/Hardmath123/nearley
(function () {
  function id(x) {
    return x[0];
  }
  var grammarProp = {
    Lexer: undefined,
    ParserRules: [
      { name: "wff", symbols: ["proposition"] },
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
      { name: "connective", symbols: [{ literal: "∧" }] },
      { name: "connective", symbols: [{ literal: "∨" }] },
      { name: "connective", symbols: [{ literal: "→" }] },
      { name: "connective", symbols: [{ literal: "↔" }] },
      { name: "proposition", symbols: [/[A-Z]/] },
      { name: "proposition", symbols: [{ literal: "P" }, "digit"] },
      { name: "digit", symbols: [/[1-9]/] },
      { name: "digit", symbols: [/[1-9]/, /[0-9]/] },
      { name: "ws", symbols: [] },
      { name: "ws", symbols: [{ literal: " " }] },
    ],
    ParserStart: "wff",
  };
  if (typeof module !== "undefined" && typeof module.exports !== "undefined") {
    module.exports = grammarProp;
  } else {
    window.grammar = grammarProp;
  }
})();
