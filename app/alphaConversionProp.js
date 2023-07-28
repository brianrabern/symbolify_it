import { lexiconDataProp } from "./lexiconProp.js";

export function alphaConversionProp(soa, formula) {
  function renamingPropMap(lexicon) {
    const result = {};
    let propCounter = 1;
    lexicon[0].Propositions.forEach((proposition) => {
      const symbol = `X${propCounter}`;
      result[proposition] = symbol;
      propCounter++;
    });

    return result;
  }

  const propRenamed = renamingPropMap(lexiconDataProp);

  for (const key in soa) {
    formula = formula.replaceAll(key, propRenamed[soa[key]]);
  }
  formula = formula.replace(/\s/g, "");

  formula = formula.replaceAll("X", "P");

  return formula;
}
