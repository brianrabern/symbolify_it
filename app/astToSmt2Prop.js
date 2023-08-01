// Abstract syntax tree (Nearley.js) to SMT-LIB converter for propositional logic
export default function astToSmt2Prop(ast) {
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
  const propositions = new Set(); // To store propositions encountered

  function processAst(ast) {
    if (ast.length === 1) {
      // Case 1: Simple proposition letter (variable)
      const propPrefix = ast[0][0];
      const propDigits = ast[0][1] ? ast[0][1].join("") : "";
      const smt2Prop = propPrefix + propDigits;
      propositions.add(smt2Prop);
      return { smt2: smt2Prop, propositions };
    } else if (ast.length === 2) {
      // Case 2: Negation
      const subFormula = processAst(ast[1]);
      return {
        smt2: `(not ${subFormula.smt2})`,
        propositions: subFormula.propositions,
      };
    } else if (ast.length === 7) {
      // Case 3: Formula with a binary connective
      const leftOperand = processAst(ast[1]);
      const connective = ast[3][0];
      const rightOperand = processAst(ast[5]);

      // Merge the propositions from both sides
      const allPropositions = new Set([
        ...leftOperand.propositions,
        ...rightOperand.propositions,
      ]);

      // Map the connective symbols using the helper function
      const smt2Connective = mapConnectiveSmt(connective);
      const smt2 = `(${smt2Connective} ${leftOperand.smt2} ${rightOperand.smt2})`;

      return { smt2, propositions: allPropositions };
    } else {
      console.log("Error: Invalid AST");
      return;
    }
  }

  const result = processAst(ast);
  return { smt2: result.smt2, propositions: result.propositions };
}

// Example usage:
// import nearley from "nearley";
// import grammarProp from "./propositional_logic.js";
// const parserProp = new nearley.Parser(
//   nearley.Grammar.fromCompiled(grammarProp)
// );
// const wffProp = "(P45 ∧ ¬Q)";
// const parsedAst1 = parserProp.feed(wffProp).results[0];

// const test = astToSmt2Prop(parsedAst1);
// console.log(test);
// const { smt2, propositions } = astToSmt2Prop(parsedAst1);
// console.log(generateSMTScriptProp(smt2, propositions));
