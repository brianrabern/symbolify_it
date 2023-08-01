// helloForm.js
import React, { useState } from "react";
import { astToSmt2Prop } from "./astToSmt2Prop.js";
import { generateSMTScriptProp } from "./generateSMTScriptProp.js";

const HelloForm = () => {
  const [formula, setFormula] = useState("");
  const [result, setResult] = useState("");

  const handleSubmit = async (e) => {
    e.preventDefault();
    let smtFormula = astToSmt2Prop(formula);
    let script = generateSMTScriptProp(smtFormula);
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
