// Z3SolverForm.js

import React, { useState } from "react";

const Z3SolverForm = () => {
  const [formula1, setFormula1] = useState("");
  const [formula2, setFormula2] = useState("");
  const [result, setResult] = useState("");

  const handleSubmit = async (e) => {
    e.preventDefault();

    try {
      const response = await fetch("/api/z3solver", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
        },
        body: JSON.stringify({ formula1, formula2 }),
      });

      const data = await response.json();
      setResult(data.result);
    } catch (error) {
      console.error("Error:", error);
      setResult("Error: Unable to process the request");
    }
  };

  return (
    <form onSubmit={handleSubmit}>
      <label>
        Formula 1:
        <input
          className="text-black"
          type="text"
          value={formula1}
          onChange={(e) => setFormula1(e.target.value)}
        />
      </label>
      <label>
        Formula 2:
        <input
          className="text-black"
          type="text"
          value={formula2}
          onChange={(e) => setFormula2(e.target.value)}
        />
      </label>
      <button type="submit">Submit</button>
      <div>Result: {result}</div>
    </form>
  );
};

export default Z3SolverForm;
