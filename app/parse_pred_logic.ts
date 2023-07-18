// @ts-ignore
const nearley = require("nearley");
const grammar = require("./predicate_logic.js");
const problem = require("./problem.json");

const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));

try {
  parser.feed(problem.form);
  console.log("parse success", parser.results);
} catch (e: any) {
  console.log("parse fail", e.message);
}
