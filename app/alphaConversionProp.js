import { lexiconDataProp } from "./lexiconProp.js";

export function alphaConversionProp(soa, formula) {
  const propRenamed = renamingPropMap(lexiconDataProp);

  for (const key in soa) {
    formula = formula.replaceAll(key, propRenamed[soa[key]]);
  }
  formula = formula.replace(/\s/g, "");
  return formula;
}

function renamingPropMap(lexicon) {
  const result = {};
  let propCounter = 1;
  lexicon[0].Propositions.forEach((proposition) => {
    const symbol = `P${propCounter}`;
    result[proposition] = symbol;
    propCounter++;
  });
  return result;
}
