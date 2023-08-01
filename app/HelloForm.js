// helloForm.js
import React, { useState } from "react";
import astToSmt2Prop from "./astToSmt2Prop.js";
import generateSMTScriptProp from "./generateSMTScriptProp.js";
import nearley from "nearley";
import grammarProp from "./propositional_logic.js";

const HelloForm = () => {
  const [formula, setFormula] = useState("");
  const [result, setResult] = useState("");

  const handleSubmit = async (e) => {
    e.preventDefault();

    const parser = new nearley.Parser(
      nearley.Grammar.fromCompiled(grammarProp)
    );

    const pform = parser.feed(formula).results[0];
    const { smt2, propositions } = astToSmt2Prop(pform);
    const script = generateSMTScriptProp(smt2, propositions);

    try {
      const response = await fetch("/api/hello", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
        },
        body: JSON.stringify({ script }),
      });

      if (!response.ok) {
        throw new Error("Failed to fetch the data.");
      }

      const data = await response.text();
      setResult(data);
    } catch (error) {
      console.error("Error:", error);
      setResult("Error: Unable to process the request");
    }
  };

  return (
    <form onSubmit={handleSubmit}>
      <label>
        Enter formula:
        <input
          className="text-black"
          type="text"
          value={formula}
          onChange={(e) => setFormula(e.target.value)}
        />
      </label>
      <button type="submit">Submit</button>
      <div>{result}</div>
    </form>
  );
};

export default HelloForm;
