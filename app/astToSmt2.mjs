import nearley from "nearley";
import grammarProp from "./propositional_logic.js";
import grammarPred from "./predicate_logic.js";

// Abstract syntax tree (Nearley.js) to SMT-LIB converter for propositional logic
// export function astToSmt2Prop(ast) {
//   if (ast.length === 1) {
//     // Case 1: Simple proposition letter
//     return ast[0][0];
//   } else if (ast.length === 2) {
//     // Case 2: Negation
//     return `(not ${astToSmt2Prop(ast[1])})`;
//   } else if (ast.length === 7) {
//     // Case 3: Formula with a binary connective
//     const leftOperand = astToSmt2Prop(ast[1]);
//     const connective = ast[3][0];
//     const rightOperand = astToSmt2Prop(ast[5]);

//     // Map the connective symbols to the SMT-LIB format
//     switch (connective) {
//       case "→":
//         return `(=> ${leftOperand} ${rightOperand})`;
//       case "∧":
//         return `(and ${leftOperand} ${rightOperand})`;
//       case "∨":
//         return `(or ${leftOperand} ${rightOperand})`;
//       case "↔":
//         return `(= ${leftOperand} ${rightOperand})`;
//     }
//   } else {
//     console.log("Error: Invalid AST");
//   }
// }
function astToSmt2Prop(ast) {
  if (ast.length === 1) {
    // Case 1: Simple proposition letter (variable)
    const variable = ast[0][0];
    return { smt2: variable, declarations: new Set([variable]) };
  } else if (ast.length === 2) {
    // Case 2: Negation
    const subFormula = astToSmt2Prop(ast[1]);
    return {
      smt2: `(not ${subFormula.smt2})`,
      declarations: subFormula.declarations,
    };
  } else if (ast.length === 7) {
    // Case 3: Formula with a binary connective
    const leftOperand = astToSmt2Prop(ast[1]);
    const connective = ast[3][0];
    const rightOperand = astToSmt2Prop(ast[5]);

    // Merge the declarations from both sides
    const allDeclarations = new Set([
      ...leftOperand.declarations,
      ...rightOperand.declarations,
    ]);

    // Map the connective symbols to the SMT-LIB format
    let smt2;
    switch (connective) {
      case "→":
        smt2 = `(=> ${leftOperand.smt2} ${rightOperand.smt2})`;
        break;
      case "∧":
        smt2 = `(and ${leftOperand.smt2} ${rightOperand.smt2})`;
        break;
      case "∨":
        smt2 = `(or ${leftOperand.smt2} ${rightOperand.smt2})`;
        break;
      case "↔":
        smt2 = `(= ${leftOperand.smt2} ${rightOperand.smt2})`;
        break;
      default:
        console.log("Error: Invalid connective");
        return;
    }

    return { smt2, declarations: allDeclarations };
  } else {
    console.log("Error: Invalid AST");
    return;
  }
}

function generateSMTScript(smtFormula, propositionalVariables) {
  function generateDeclarations(variables) {
    let declarations = "";
    for (const variable of variables) {
      declarations += `(declare-const ${variable} Bool)\n`;
    }
    return declarations;
  }

  function wrapInAssertAndCheckSat(formula) {
    const wrappedFormula = `(assert ${formula})\n(check-sat)`;
    return wrappedFormula;
  }

  const declarationsString = generateDeclarations(propositionalVariables);
  const wrappedFormula = wrapInAssertAndCheckSat(smtFormula);

  return declarationsString + wrappedFormula;
}
// Example usage:
const parserProp = new nearley.Parser(
  nearley.Grammar.fromCompiled(grammarProp)
);
const wffProp = "((P ∧ Q) ↔ ¬R)";
const parsedAst1 = parserProp.feed(wffProp).results[0];
const { smt2, declarations } = astToSmt2Prop(parsedAst1);
console.log(generateSMTScript(smt2, declarations));

// Abstract syntax tree (Nearley.js) to SMT-LIB converter for predicate logic
export function astToSmt2Pred(ast) {
  if (ast.length === 2 && ast[0] !== "¬") {
    // Case 1: Predication formula
    const predicateSymbol = ast[0];
    const args = ast[1].map((arg) => arg[0][0]);
    return `(${predicateSymbol} ${args.join(" ")})`;
  } else if (ast.length === 2 && ast[0][0] === "¬") {
    // Case 2: Negation formula
    return `(not ${astToSmt2Pred(ast[1])})`;
  } else if (ast.length === 7) {
    // Case 3: Binary connective formula
    const leftOperand = astToSmt2Pred(ast[1]);
    const connective = ast[3][0];
    const rightOperand = astToSmt2Pred(ast[5]);

    // Map the connective symbols to the SMT-LIB format
    switch (connective) {
      case "→":
        return `(=> ${leftOperand} ${rightOperand})`;
      case "∧":
        return `(and ${leftOperand} ${rightOperand})`;
      case "∨":
        return `(or ${leftOperand} ${rightOperand})`;
      case "↔":
        return `(= ${leftOperand} ${rightOperand})`;
    }
  } else if (ast.length === 3) {
    // Case 4: Quantified formula
    const quantifier = ast[0][0];
    const variable = ast[1][0][0];
    const wff = astToSmt2Pred(ast[2]);

    switch (quantifier) {
      case "∀":
        return `(forall ((${variable} Object)) ${wff})`;
      case "∃":
        return `(exists ((${variable} Object)) ${wff})`;
    }
  } else {
    console.log("Error: Invalid AST");
  }
}

// Example usage:
// const parserPred = new nearley.Parser(
//   nearley.Grammar.fromCompiled(grammarPred)
// );
// const wffPred = "∀x(Fx → Gx)";
// const parsedAst2 = parserPred.feed(wffPred).results[0];
// const smt2wff2 = astToSmt2Pred(parsedAst2);
// console.log(smt2wff2);
