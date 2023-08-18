// Abstract syntax tree (Nearley.js) to SMT-LIB converter for predicate logic
export default function astToSmt2Pred(ast) {
  // Helper function to map connective symbols to SMT-LIB format
  function mapConnectiveSmt(connective) {
    const connectiveMap = {
      "→": "=>",
      "∧": "and",
      "∨": "or",
      "↔": "=",
      "∀": "forall",
      "∃": "exists",
    };

    return connectiveMap[connective];
  }

  function isPredicateLetter(character) {
    const predicates = /^[A-Z]$/;
    return predicates.test(character[0]);
  }

  function isNameLetter(character) {
    const names = /^[a-r]$/;
    return names.test(character[0]);
  }
  const names = new Set(); // To store names encountered: [a-r] | "a" digit
  const monadicPredicates = new Set(); // To store 1-place predicates
  const binaryPredicates = new Set(); // To store 2-place predicates

  function processAst(ast) {
    if (ast.length === 2 && isPredicateLetter(ast[0][0])) {
      // Case 1: Monadic predication formula

      const predPrefix = ast[0][0];
      const predDigits = ast[0][1] ? ast[0][1].join("") : "";
      const predicate = predPrefix + predDigits;

      const termPrefix = ast[1][0][0];
      const termDigits = ast[1][0][1] ? ast[1][0][1].join("") : "";
      const term = termPrefix + termDigits;

      isNameLetter(term) ? names.add(term) : null;
      monadicPredicates.add(predicate);

      return { smt2: `(${predicate} ${term})` };
    } else if (ast.length === 3 && isPredicateLetter(ast[0][0])) {
      // Case 2: Binary predication formula
      const predPrefix = ast[0][0];
      const predDigits = ast[0][1] ? ast[0][1].join("") : "";
      const predicate = predPrefix + predDigits;

      const term1Prefix = ast[1][0][0];
      const term1Digits = ast[1][0][1] ? ast[1][0][1].join("") : "";
      const term1 = term1Prefix + term1Digits;

      const term2Prefix = ast[2][0][0];
      const term2Digits = ast[2][0][1] ? ast[2][0][1].join("") : "";
      const term2 = term2Prefix + term2Digits;

      isNameLetter(term1) ? names.add(term1) : null;
      isNameLetter(term2) ? names.add(term2) : null;
      binaryPredicates.add(predicate);

      return { smt2: `(${predicate} ${term1} ${term2})` };
    } else if (ast.length === 2 && ast[0][0] === "¬") {
      // Case 3: Negation formula
      const subFormula = processAst(ast[1]);
      return { smt2: `(not ${subFormula.smt2})` };
    } else if (ast.length === 3 && (ast[0] === "∀" || ast[0] === "∃")) {
      // Case 4: Quantification formula
      const quantifier = ast[0];
      const variable = ast[1];
      const subFormula = processAst(ast[2]);
      const smt2Quantifier = mapConnectiveSmt(quantifier);
      const quantifiedFormula = `(${smt2Quantifier} ((${variable} Object)) ${subFormula.smt2})`;

      return { smt2: quantifiedFormula };
    } else if (ast.length === 7 && ast[0][0] === "(" && ast[6][0] === ")") {
      // Case 5: Formula with a binary connective
      const leftOperand = processAst(ast[1]);
      const connective = ast[3][0];
      const rightOperand = processAst(ast[5]);

      const smt2Connective = mapConnectiveSmt(connective);
      const smt2 = `(${smt2Connective} ${leftOperand.smt2} ${rightOperand.smt2})`;

      return { smt2 };
    } else {
      console.log("Error: Invalid AST");
      return;
    }
  }

  const result = processAst(ast);
  return { smt2: result.smt2, names, monadicPredicates, binaryPredicates };
}
