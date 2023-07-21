// nearley, version 2.20.1
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
