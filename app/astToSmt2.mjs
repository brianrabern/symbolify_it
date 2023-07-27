import nearley from "nearley";
import grammarProp from "./propositional_logic.js";
import grammarPred from "./predicate_logic.js";

// Abstract syntax tree (Nearley.js) to SMT-LIB converter for propositional logic
export function astToSmt2Prop(ast) {
  if (ast.length === 1) {
    // Case 1: Simple proposition letter
    return ast[0][0];
  } else if (ast.length === 2) {
    // Case 2: Negation
    return `(not ${astToSmt2Prop(ast[1])})`;
  } else if (ast.length === 7) {
    // Case 3: Formula with a binary connective
    const leftOperand = astToSmt2Prop(ast[1]);
    const connective = ast[3][0];
    const rightOperand = astToSmt2Prop(ast[5]);

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
  } else {
    console.log("Error: Invalid AST");
  }
}

// Example usage:
const parserProp = new nearley.Parser(
  nearley.Grammar.fromCompiled(grammarProp)
);
const wffProp = "((P ∧ Q) ↔ R)";
const parsedAst1 = parserProp.feed(wffProp).results[0];
const smt2wff = astToSmt2Prop(parsedAst1);
console.log(smt2wff);

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
const parserPred = new nearley.Parser(
  nearley.Grammar.fromCompiled(grammarPred)
);
const wffPred = "∀x(Fx → Gx)";
const parsedAst2 = parserPred.feed(wffPred).results[0];
const smt2wff2 = astToSmt2Pred(parsedAst2);
console.log(smt2wff2);
