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
    console.log("formula: ", formula);
    const parser = new nearley.Parser(
      nearley.Grammar.fromCompiled(grammarProp)
    );

    const pform = parser.feed(formula).results[0];
    const { smt2, propositions } = astToSmt2Prop(pform);
    console.log("smt2: ", smt2);

    const script = generateSMTScriptProp(smt2, propositions);
    console.log("script: ", script);
    try {
      const response = await fetch("/api/hello", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
        },
        body: script,
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
    <div>
      <br />
      <hr></hr>
      <br />
      <form onSubmit={handleSubmit}>
        <h1>Testing for Z3 solver API (under construction)</h1>
        <label>
          Enter formula:
          <input
            className="text-black"
            type="text"
            value={formula}
            onChange={(e) => setFormula(e.target.value)}
          />
        </label>
        <button
          className="px-4 py-1 mt-4 bg-red-500 hover:bg-blue-600 text-white rounded-md"
          type="submit"
        >
          Z3 API
        </button>
        <div>{result}</div>
      </form>
    </div>
  );
};

export default HelloForm;
