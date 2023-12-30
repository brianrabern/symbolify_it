import { lexiconDataPred } from "./lexiconPred.js";

const expRenamed = {};
let nameCounter = 1;
let predCounter = 1;

lexiconDataPred[0].Names.forEach((name) => {
  const symbol = `c${nameCounter}`;
  expRenamed[name] = symbol;
  nameCounter++;
});

lexiconDataPred[1].monadicPredicates.forEach((predicate) => {
  const symbol = `X${predCounter}`;
  expRenamed[predicate] = symbol;
  predCounter++;
});

lexiconDataPred[2].binaryPredicates.forEach((predicate) => {
  const symbol = `X${predCounter}`;
  expRenamed[predicate] = symbol;
  predCounter++;
});

function variablesMap(formula) {
  const variables = [];
  const map = {};

  // Extract variables from the formula
  formula.replace(/[s-z]/g, (match) => {
    if (!variables.includes(match)) {
      variables.push(match);
    }
  });

  // Assign values to variables
  for (let i = 0; i < variables.length; i++) {
    const variable = variables[i];
    const value = "z" + (i + 1);
    map[variable] = value;
  }

  return map;
}

export function alphaConversionPred(soa, formula) {
  for (const key in soa) {
    formula = formula.replaceAll(key, expRenamed[soa[key]]);
  }

  const variablesRenamed = variablesMap(formula);
  for (const key in variablesRenamed) {
    formula = formula.replaceAll(key, variablesRenamed[key]);
  }

  formula = formula.replace(/\s/g, "");
  formula = formula.replaceAll("c", "a");
  formula = formula.replaceAll("X", "F");
  formula = formula.replaceAll("z", "x");

  return formula;
}
