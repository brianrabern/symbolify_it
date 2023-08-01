import nearley from "nearley";
import grammarProp from "./propositional_logic.js";
import grammarPred from "./predicate_logic.js";

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

// Abstract syntax tree (Nearley.js) to SMT-LIB converter for propositional logic
function astToSmt2Prop(ast) {
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

function generateSMTScriptProp(smtFormula, propositionalVariables) {
  function generateDeclarations(variables) {
    let declarations = "";
    variables.forEach((variable) => {
      declarations += `(declare-const ${variable} Bool)\n`;
    });
    return declarations;
  }

  const declarationsString = generateDeclarations(propositionalVariables);

  return declarationsString + `(assert ${smtFormula})`;
}

// Example usage:
// const parserProp = new nearley.Parser(
//   nearley.Grammar.fromCompiled(grammarProp)
// );
// const wffProp = "(P45 ∧ ¬Q)";
// const parsedAst1 = parserProp.feed(wffProp).results[0];

// const test = astToSmt2Prop(parsedAst1);
// console.log(test);
// const { smt2, propositions } = astToSmt2Prop(parsedAst1);
// console.log(generateSMTScriptProp(smt2, propositions));

// Abstract syntax tree (Nearley.js) to SMT-LIB converter for predicate logic
function astToSmt2Pred(ast) {
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

function generateSMTScriptPred(
  smtFormula,
  names,
  monadicPredicates,
  binaryPredicates
) {
  let script = "";

  names.forEach((name) => {
    script += `(declare-const ${name} Object)\n`;
  });

  monadicPredicates.forEach((predicate) => {
    script += `(declare-fun ${predicate} (Object) Bool)\n`;
  });

  binaryPredicates.forEach((predicate) => {
    script += `(declare-fun ${predicate} (Object Object) Bool)\n`;
  });

  script += `(assert ${smtFormula})`;

  return script;
}

// Example usage:
// const parserPred1 = new nearley.Parser(
//   nearley.Grammar.fromCompiled(grammarPred)
// );
// const case1 = "Fa";
// const parsed_case1 = parserPred1.feed(case1).results[0];
// console.log(astToSmt2Pred(parsed_case1));
// const smt2Output = astToSmt2Pred(parsed_case1);
// const smtScript = generateSMTScriptPred(
//   smt2Output.smt2,
//   smt2Output.names,
//   smt2Output.monadicPredicates,
//   smt2Output.binaryPredicates
// );
// console.log(smtScript);
// const { smtFormula, namesSet, monoPredSet, binPredSet } =
//   astToSmt2Pred(parsed_case1);
// console.log(namesSet);
// console.log(monoPredSet);
// console.log(binPredSet);
// console.log(
//   generateSMTScriptPred(smtFormula, namesSet, monoPredSet, binPredSet)
// );
