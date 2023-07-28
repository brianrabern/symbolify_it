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
    const variablePrefix = ast[0][0];
    const variableDigits = ast[0][1].join("");
    const smt2Var = variablePrefix + variableDigits;
    return { smt2: smt2Var, declarations: new Set([smt2Var]) };
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

  const declarationsString = generateDeclarations(propositionalVariables);

  return declarationsString + `(assert ${smtFormula})`;
}

// Example usage:
const parserProp = new nearley.Parser(
  nearley.Grammar.fromCompiled(grammarProp)
);
const wffProp = "(P45 ∧ P2)";
const parsedAst1 = parserProp.feed(wffProp).results[0];
console.log(parsedAst1[1]);
const { smt2, declarations } = astToSmt2Prop(parsedAst1);
console.log(generateSMTScript(smt2, declarations));

// Abstract syntax tree (Nearley.js) to SMT-LIB converter for predicate logic
// export function astToSmt2Pred(ast) {
//   if (ast.length === 2 && ast[0] !== "¬") {
//     // Case 1: Predication formula
//     const predicateSymbol = ast[0];
//     const args = ast[1].map((arg) => arg[0][0]);
//     return `(${predicateSymbol} ${args.join(" ")})`;
//   } else if (ast.length === 2 && ast[0][0] === "¬") {
//     // Case 2: Negation formula
//     return `(not ${astToSmt2Pred(ast[1])})`;
//   } else if (ast.length === 7) {
//     // Case 3: Binary connective formula
//     const leftOperand = astToSmt2Pred(ast[1]);
//     const connective = ast[3][0];
//     const rightOperand = astToSmt2Pred(ast[5]);

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
//   } else if (ast.length === 3) {
//     // Case 4: Quantified formula
//     const quantifier = ast[0][0];
//     const variable = ast[1][0][0];
//     const wff = astToSmt2Pred(ast[2]);

//     switch (quantifier) {
//       case "∀":
//         return `(forall ((${variable} Object)) ${wff})`;
//       case "∃":
//         return `(exists ((${variable} Object)) ${wff})`;
//     }
//   } else {
//     console.log("Error: Invalid AST");
//   }
// }

// export function astToSmt2Pred(ast) {
//   function handleSymbolWithDigits(symbolArray) {
//     let symbol = "";
//     for (const element of symbolArray) {
//       if (Array.isArray(element)) {
//         symbol += handleSymbolWithDigits(element);
//       } else {
//         symbol += element;
//       }
//     }
//     return symbol;
//   }

//   if (ast.length === 2 && ast[0] !== "¬") {
//     // Case 1: Predication formula
//     const predicateSymbol = handleSymbolWithDigits(ast[0]);
//     const args = ast[1].map((arg) => handleSymbolWithDigits(arg));
//     return `(${predicateSymbol} ${args.join(" ")})`;
//   } else if (ast.length === 2 && ast[0][0] === "¬") {
//     // Case 2: Negation formula
//     return `(not ${astToSmt2Pred(ast[1])})`;
//   } else if (ast.length === 7) {
//     // Case 3: Binary connective formula
//     const leftOperand = astToSmt2Pred(ast[1]);
//     const connective = ast[3][0];
//     const rightOperand = astToSmt2Pred(ast[5]);

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
//   } else if (ast.length === 3) {
//     // Case 4: Quantified formula
//     const quantifier = ast[0][0];
//     const variableArray = ast[1];
//     const variable = handleSymbolWithDigits(variableArray);
//     const wff = astToSmt2Pred(ast[2]);

//     switch (quantifier) {
//       case "∀":
//         return `(forall ((${variable} Object)) ${wff})`;
//       case "∃":
//         return `(exists ((${variable} Object)) ${wff})`;
//     }
//   } else {
//     console.log("Error: Invalid AST");
//   }
// }

// export function astToSmt2Pred(ast) {
//   function handleSymbolWithDigits(symbolArray) {
//     let symbol = "";
//     for (const element of symbolArray) {
//       if (Array.isArray(element)) {
//         symbol += handleSymbolWithDigits(element);
//       } else {
//         symbol += element;
//       }
//     }
//     return symbol;
//   }

//   function collectNames(ast) {
//     const names = new Set();
//     if (ast.length === 2 && ast[0] !== "¬") {
//       // Case 1: Predication formula
//       const args = ast[1].map((arg) => handleSymbolWithDigits(arg));
//       args.forEach((arg) => {
//         if (arg[0].match(/[a-r]/)) {
//           names.add(arg);
//         }
//       });
//     } else if (ast.length === 2 && ast[0][0] === "¬") {
//       // Case 2: Negation formula
//       const subFormulaNames = collectNames(ast[1]);
//       subFormulaNames.forEach((name) => names.add(name));
//     } else if (ast.length === 7) {
//       // Case 3: Binary connective formula
//       const leftOperandNames = collectNames(ast[1]);
//       const rightOperandNames = collectNames(ast[5]);
//       leftOperandNames.forEach((name) => names.add(name));
//       rightOperandNames.forEach((name) => names.add(name));
//     } else if (ast.length === 3) {
//       // Case 4: Quantified formula
//       const wffNames = collectNames(ast[2]);
//       wffNames.forEach((name) => names.add(name));
//     }
//     return names;
//   }

//   function collectPredicates(ast) {
//     const predicates = {}; // Use an object to store predicates and their arities
//     if (ast.length === 2 && ast[0] !== "¬") {
//       // Case 1: Predication formula
//       const predicateSymbol = handleSymbolWithDigits(ast[0]);
//       const arity = ast[1].length; // Arity is the length of the argument array
//       predicates[predicateSymbol] = arity;
//     } else if (ast.length === 2 && ast[0][0] === "¬") {
//       // Case 2: Negation formula
//       const subFormulaPredicates = collectPredicates(ast[1]);
//       Object.assign(predicates, subFormulaPredicates);
//     } else if (ast.length === 7) {
//       // Case 3: Binary connective formula
//       const leftOperandPredicates = collectPredicates(ast[1]);
//       const rightOperandPredicates = collectPredicates(ast[5]);
//       Object.assign(predicates, leftOperandPredicates, rightOperandPredicates);
//     } else if (ast.length === 3) {
//       // Case 4: Quantified formula
//       const wffPredicates = collectPredicates(ast[2]);
//       Object.assign(predicates, wffPredicates);
//     }
//     return predicates;
//   }

//   if (ast.length === 2 && ast[0] !== "¬") {
//     // Case 1: Predication formula
//     const predicateSymbol = handleSymbolWithDigits(ast[0]);
//     const args = ast[1].map((arg) => handleSymbolWithDigits(arg));
//     const namesDeclarations = collectNames(ast);
//     const predicatesDeclarations = collectPredicates(ast);

//     return {
//       smt2: `(${predicateSymbol} ${args.join(" ")})`,
//       namesDeclarations,
//       predicatesDeclarations,
//     };
//   } else if (ast.length === 2 && ast[0][0] === "¬") {
//     // Case 2: Negation formula
//     const subFormula = astToSmt2Pred(ast[1]);
//     return {
//       smt2: `(not ${subFormula.smt2})`,
//       namesDeclarations: subFormula.namesDeclarations,
//       predicatesDeclarations: subFormula.predicatesDeclarations,
//     };
//   } else if (ast.length === 7) {
//     // Case 3: Binary connective formula
//     const leftOperand = astToSmt2Pred(ast[1]);
//     const connective = handleSymbolWithDigits(ast[3]);
//     const rightOperand = astToSmt2Pred(ast[5]);

//     // Merge the declarations from both sides
//     const namesDeclarations = new Set([
//       ...leftOperand.namesDeclarations,
//       ...rightOperand.namesDeclarations,
//     ]);
//     const predicatesDeclarations = new Set([
//       ...leftOperand.predicatesDeclarations,
//       ...rightOperand.predicatesDeclarations,
//     ]);

//     let smt2;
//     switch (connective) {
//       case "→":
//         smt2 = `(=> ${leftOperand.smt2} ${rightOperand.smt2})`;
//         break;
//       case "∧":
//         smt2 = `(and ${leftOperand.smt2} ${rightOperand.smt2})`;
//         break;
//       case "∨":
//         smt2 = `(or ${leftOperand.smt2} ${rightOperand.smt2})`;
//         break;
//       case "↔":
//         smt2 = `(= ${leftOperand.smt2} ${rightOperand.smt2})`;
//         break;
//     }

//     return {
//       smt2,
//       namesDeclarations,
//       predicatesDeclarations,
//     };
//   } else if (ast.length === 3) {
//     // Case 4: Quantified formula
//     const quantifier = ast[0][0];
//     const variableArray = ast[1];
//     const variable = handleSymbolWithDigits(variableArray);
//     const wff = astToSmt2Pred(ast[2]);

//     const wffNamesDeclarations = wff.namesDeclarations;
//     const wffPredicatesDeclarations = wff.predicatesDeclarations;

//     let smt2;
//     switch (quantifier) {
//       case "∀":
//         smt2 = `(forall ((${variable} Object)) ${wff.smt2})`;
//         break;
//       case "∃":
//         smt2 = `(exists ((${variable} Object)) ${wff.smt2})`;
//         break;
//     }

//     return {
//       smt2,
//       namesDeclarations: wffNamesDeclarations,
//       predicatesDeclarations: wffPredicatesDeclarations,
//     };
//   } else {
//     console.log("Error: Invalid AST");
//   }
// }

// Example usage:
// const parserPred = new nearley.Parser(
//   nearley.Grammar.fromCompiled(grammarPred)
// );
// const wffPred = "Fabcdasfdfgfgf";
// const parsedAst2 = parserPred.feed(wffPred).results[0];
// console.log(parsedAst2);
// const smt2wff2 = astToSmt2Pred(parsedAst2);
// console.log(smt2wff2);
// // [ [ [ 'a' ] ] ]
