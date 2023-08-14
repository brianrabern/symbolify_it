export default function generateSMTScriptProp(
  userSmt,sysSmt
) {
  let {userSmtFormula,userPropositionLetters} = userSmt;
  let {sysSmtFormula,sysPropositionLetters} = sysSmt;
  function generateDeclarations(propositions) {
    let declarations = "";
    propositions.forEach((proposition) => {
      declarations += `(declare-const ${proposition} Bool)\n`;
    });
    return declarations;
  }

  const declarationsString = generateDeclarations(userPropositionLetters) + generateDeclarations(sysPropositionLetters);

  return `${declarationsString}(assert ${smtFormula})`;
}
`${declarationsString}(assert (not (= ${userSmtFormula} ${sysSmtFormula})))`

// (assert (not (= Formula1 Formula2)))
//for example: p and ~~p
// assume not equivalent: ~(p iff ~~p)
// if sat then not equivalent
// if unsat then equivalent

