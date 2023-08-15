export default function generateSMTScriptProp(userSmt, sysSmt) {
  function generateDeclarations(propositions) {
    let declarations = "";
    propositions.forEach((proposition) => {
      declarations += `(declare-const ${proposition} Bool)\n`;
    });
    return declarations;
  }

  const declarationsString =
    generateDeclarations(userSmt.propositions) +
    generateDeclarations(sysSmt.propositions);

  return `${declarationsString}(assert (not (= ${userSmt.smt2} ${sysSmt.smt2})))`;
}

// (assert (not (= Formula1 Formula2)))
//for example: p and ~~p
// assume not equivalent: ~(p iff ~~p)
// if sat then not equivalent
// if unsat then equivalent
