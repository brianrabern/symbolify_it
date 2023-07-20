import { lexiconDataPred } from "./lexiconPred.js";

export function alphaConversion(soa, formula) {
  const expRenamed = renamingMap(lexiconDataPred);
  const variablesRenamed = variablesMap(formula);

  for (const key in soa) {
    formula = formula.replaceAll(key, expRenamed[soa[key]]);
  }

  for (const key in variablesRenamed) {
    formula = formula.replaceAll(key, variablesRenamed[key]);
  }

  return formula;
}

function renamingMap(lexicon) {
  const result = {};

  let nameCounter = 1;
  lexicon[0].Names.forEach((name) => {
    const symbol = `a${nameCounter}`;
    result[name] = symbol;
    nameCounter++;
  });

  let monadicCounter = 1;
  lexicon[1].monadicPredicates.forEach((predicate) => {
    const symbol = `F${monadicCounter}`;
    result[predicate] = symbol;
    monadicCounter++;
  });

  let binaryCounter = 1;
  lexicon[2].binaryPredicates.forEach((predicate) => {
    const symbol = `R${binaryCounter}`;
    result[predicate] = symbol;
    binaryCounter++;
  });

  return result;
}

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
    const value = "x" + (i + 1);
    map[variable] = value;
  }

  return map;
}
