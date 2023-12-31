export default function generateSMTScriptProp(userSmt, sysSmt) {
  const declarationsSet = new Set(); // track declared propositions

  function generateDeclarations(propositions) {
    let declarations = "";

    propositions.forEach((proposition) => {
      if (!declarationsSet.has(proposition)) {
        declarations += `(declare-const ${proposition} Bool)\n`;
        declarationsSet.add(proposition); // mark proposition as declared
      }
    });

    return declarations;
  }

  const declarationsString =
    generateDeclarations(userSmt.propositions) +
    generateDeclarations(sysSmt.propositions);

  return `${declarationsString}(assert (not (= ${userSmt.smt2} ${sysSmt.smt2})))`;
}
