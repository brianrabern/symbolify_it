export default function generateSMTScriptProp(
  smtFormula,
  propositionalVariables
) {
  function generateDeclarations(variables) {
    let declarations = "";
    variables.forEach((variable) => {
      declarations += `(declare-fun ${variable} () Bool))\n`;
    });
    return declarations;
  }

  const declarationsString = generateDeclarations(propositionalVariables);

  return declarationsString + `(assert ${smtFormula})`;
}
