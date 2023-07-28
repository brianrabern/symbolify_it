import { lexiconDataPred } from "./lexiconPred.js";

export function alphaConversionPred(soa, formula) {
  function renamingMap(lexicon) {
    const result = {};
    let nameCounter = 1;
    let predCounter = 1;

    lexicon[0].Names.forEach((name) => {
      const symbol = `c${nameCounter}`;
      result[name] = symbol;
      nameCounter++;
    });

    lexicon[1].monadicPredicates.forEach((predicate) => {
      const symbol = `X${predCounter}`;
      result[predicate] = symbol;
      predCounter++;
    });

    lexicon[2].binaryPredicates.forEach((predicate) => {
      const symbol = `X${predCounter}`;
      result[predicate] = symbol;
      predCounter++;
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
      const value = "z" + (i + 1);
      map[variable] = value;
    }

    return map;
  }

  const expRenamed = renamingMap(lexiconDataPred);
  const variablesRenamed = variablesMap(formula);

  for (const key in soa) {
    formula = formula.replaceAll(key, expRenamed[soa[key]]);
  }

  for (const key in variablesRenamed) {
    formula = formula.replaceAll(key, variablesRenamed[key]);
  }
  formula = formula.replace(/\s/g, "");
  formula = formula.replaceAll("c", "a");
  formula = formula.replaceAll("X", "F");
  formula = formula.replaceAll("z", "x");

  return formula;
}
