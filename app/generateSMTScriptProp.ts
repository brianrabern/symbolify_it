interface Smt { smt2: string; propositions: Set<string>; }

export default function generateSMTScriptProp(userSmt: Smt, sysSmt: Smt): string {
  const declarationsArray = Array.from(new Set([...userSmt.propositions, ...sysSmt.propositions])).map((d) => `(declare-const ${d} Bool)\n`);
  declarationsArray.push(`(assert (not (= ${userSmt.smt2} ${sysSmt.smt2})))`);
  return declarationsArray.join("");
}
