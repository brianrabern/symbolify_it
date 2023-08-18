export default function generateSMTScriptPred(userSmt, sysSmt) {
  const declarationsSet = new Set(); // track declared name and predicates
  // get names
  function generateNameDeclarations(names) {
    let nameDeclarations = "";

    names.forEach((name) => {
      if (!declarationsSet.has(name)) {
        nameDeclarations += `(declare-const ${name} Object)\n`;
        declarationsSet.add(name); // mark name as declared
      }
    });

    return nameDeclarations;
  }

  // get monadic predicates
  function generateMonadicPredDeclarations(monadicPredicates) {
    let monadicPredDeclarations = "";

    monadicPredicates.forEach((predicate) => {
      if (!declarationsSet.has(predicate)) {
        monadicPredDeclarations += `(declare-fun ${predicate} (Object) Bool)\n`;
        declarationsSet.add(predicate); // mark predicate as declared
      }
    });

    return monadicPredDeclarations;
  }

  // get binary predicates
  function generateBinaryPredDeclarations(binaryPredicates) {
    let binaryPredDeclarations = "";

    binaryPredicates.forEach((predicate) => {
      if (!declarationsSet.has(predicate)) {
        binaryPredDeclarations += `(declare-fun ${predicate} (Object Object) Bool)\n`;
        declarationsSet.add(predicate); // mark predicate as declared
      }
    });

    return binaryPredDeclarations;
  }

  // generate script
  const declarationsString =
    generateNameDeclarations(userSmt.names) +
    generateNameDeclarations(sysSmt.names) +
    generateMonadicPredDeclarations(userSmt.monadicPredicates) +
    generateMonadicPredDeclarations(sysSmt.monadicPredicates) +
    generateBinaryPredDeclarations(userSmt.binaryPredicates) +
    generateBinaryPredDeclarations(sysSmt.binaryPredicates);

  console.log(
    "smt script: "`${declarationsString}(assert (not (= ${userSmt.smt2} ${sysSmt.smt2})))`
  );
  return `${declarationsString}(assert (not (= ${userSmt.smt2} ${sysSmt.smt2})))`;
}
