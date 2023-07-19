function substituteFormula(soa, formula) {
  // helper function to perform the substitutions in the formula
  function replaceVariables(match, key) {
    return soa[key]; // replace the key with its corresponding value from SOA
  }

  // regular expression to match the keys in the formula (e.g., a, b, F)
  const regex = /\b([a-zA-Z_][a-zA-Z0-9_]*)\b/g;

  // perform the substitutions using the helper function
  const substitutedFormula = formula.replace(regex, replaceVariables);

  return substitutedFormula;
}

// example SOA and formula
const soa1 = { a: "Hazel", b: "Ewan", F: "[1] loves [2]" };
const formula1 = "¬F(a, b)";

const soa2 = { c: "Hazel", d: "Ewan", G: "[1] loves [2]" };
const formula2 = "¬G(c, d)";

// call the function and get the transformed formula
const transformedFormula1 = substituteFormula(soa1, formula1);
const transformedFormula2 = substituteFormula(soa2, formula2);
console.log(transformedFormula1 == transformedFormula2);
