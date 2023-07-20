"use client";

import React, { useState } from "react";
import predProblems from "./predProblems.json";
import { lexiconDataPred } from "./lexiconPred.js";
import { alphaConversion } from "./alphaConversion.js";
import nearley from "nearley";
import grammar from "./predicate_logic.js";

export default function Home() {
  const [logic, setLogic] = useState("prop");
  const [selectedProblem, setSelectedProblem] = useState(1);
  const [userFormula, setUserFormula] = useState("");
  const [userSoa, setUserSoa] = useState([{ symbol: "", lexicon: "" }]);

  const names: string[] = lexiconDataPred[0]?.Names || [];
  const monadic: string[] = lexiconDataPred[1]?.monadicPredicates || [];
  const binary: string[] = lexiconDataPred[2]?.binaryPredicates || [];
  const lexiconOptions = [...names, ...monadic, ...binary];

  const handleProblemChange = (event: any) => {
    const selectedProblem = parseInt(event.target.value);
    setSelectedProblem(selectedProblem);
    setUserFormula("");
    setUserSoa([{ symbol: "", lexicon: "" }]);
  };

  const handleRandomProblem = () => {
    let randomIndex;
    do {
      randomIndex = Math.floor(Math.random() * predProblems.length) + 73;
    } while (randomIndex === selectedProblem);

    setSelectedProblem(randomIndex);
  };

  const handleSymbolChange = (index: number, value: string) => {
    const updatedUserSoa = [...userSoa];
    updatedUserSoa[index].symbol = value;
    setUserSoa(updatedUserSoa);
  };

  const handleLexiconChange = (index: number, value: string) => {
    const updatedUserSoa = [...userSoa];
    updatedUserSoa[index].lexicon = value;
    setUserSoa(updatedUserSoa);
  };

  const handleAddEntry = () => {
    setUserSoa([...userSoa, { symbol: "", lexicon: "" }]);
  };

  const handleConnectiveClick = (connective: string) => {
    setUserFormula(userFormula + connective);
    document.getElementById("userInput")?.focus();
  };

  function areObjectsEqual(obj1: object, obj2: object) {
    const keys1 = Object.keys(obj1);
    const keys2 = Object.keys(obj2);

    if (keys1.length !== keys2.length) {
      return false;
    }

    for (const key of keys1) {
      // @ts-ignore
      if (obj1[key] !== obj2[key]) {
        return false;
      }
    }

    return true;
  }

  const handleCheck = () => {
    let results;
    try {
      const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
      parser.feed(userFormula);
      // set results to the parsed result if successful
      results = parser.results[0];
    } catch (error: any) {
      // if there's an error, try parsing with added parentheses
      try {
        const parser = new nearley.Parser(
          nearley.Grammar.fromCompiled(grammar)
        );
        parser.feed("(" + userFormula + ")");
        // add parentheses to the user formula if successful
        if (parser.results[0] != 0) {
          setUserFormula("(" + userFormula + ")");
        }
        // set results to the formula with added parens if successful
        results = parser.results[0];
      } catch (nestedError) {
        // handle the error when both attempts fail
        console.log("Parsing error:", error.message);
        console.log("Parsing error with parentheses:", nestedError);
      }
    }

    // if well-formed, check if it's an alpha variant of system formula
    let userSoaFlat = {};
    for (let entry of userSoa) {
      // @ts-ignore
      userSoaFlat[entry.symbol] = entry.lexicon;
    }
    let alphaConUser = alphaConversion(userSoaFlat, userFormula);
    let alphaConSys = alphaConversion(
      selectedProblemObj?.soa,
      selectedProblemObj?.form
    );
    // console logs for debugging
    console.log("SOA: ", userSoaFlat, ", Formula: ", userFormula);
    console.log("alphaConUser: ", alphaConUser);
    console.log("alphaConSys: ", alphaConSys);
    console.log("variants?:", alphaConUser == alphaConSys);
  };

  const selectedProblemObj = predProblems.find(
    (problem) => problem.id === selectedProblem
  );

  return (
    <main className="flex min-h-screen flex-col items-center justify-between p-24">
      <div className="absolute top-4 right-4">
        <p className="text-white"> Select a problem</p>

        <select
          value={selectedProblem}
          onChange={handleProblemChange}
          className="text-black border border-gray-300 rounded-md p-1 mr-2 mb-2"
        >
          {predProblems.map((problem, index) => (
            <option key={problem.id} value={problem.id}>
              {problem.id}. {problem.sentence}
            </option>
          ))}
        </select>

        <button
          onClick={handleRandomProblem}
          className="text-sm mt-4 px-2 py-2 bg-blue-500 text-white rounded-md hover:bg-blue-600 focus:outline-none"
        >
          Random problem
        </button>
      </div>
      <br></br>
      <br></br>
      <br></br>
      {/* sentence to be symbolized */}

      <h2 className="text-4xl font-bold">{selectedProblemObj?.sentence}</h2>

      {/* scheme of abbreviation */}
      <div className="bg-gray-800 p-4 rounded-md w-full flex flex-col items-center">
        <h2 className="py-2 text-2xl font-bold text-gray-500">
          Scheme of Abbreviation
        </h2>
        {userSoa.map((entry, index) => (
          <div key={index} className="flex space-x-4 py-1">
            <input
              className="text-black border border-gray-300 rounded-md p-2 w-24"
              type="text"
              value={entry.symbol}
              onChange={(e) => handleSymbolChange(index, e.target.value)}
              placeholder="Symbol"
            />
            <span className="mx-4 text-2xl font-bold">:</span>
            <select
              className="text-black border border-gray-300 rounded-md p-2"
              value={entry.lexicon}
              onChange={(e) => handleLexiconChange(index, e.target.value)}
            >
              <option value="" disabled>
                Expression
              </option>
              {lexiconOptions.map((option) => (
                <option key={option} value={option}>
                  {option}
                </option>
              ))}
            </select>
          </div>
        ))}
        <button
          className="px-4 py-2 mt-4 bg-blue-500 hover:bg-blue-600 text-white rounded-md"
          onClick={handleAddEntry}
        >
          Add Entry
        </button>

        {/* formula input */}
        <div className="mt-2 bg-gray-800 p-4 rounded-md w-full flex flex-col items-center">
          <h2 className="py-2 text-2xl font-bold text-gray-500">Formula</h2>
          <div>
            <input
              id="userInput"
              className="text-black border-2 border-color-1 rounded-md p-2"
              value={userFormula}
              onChange={(e) => setUserFormula(e.target.value)}
              placeholder="Formula"
            />
          </div>
          {/* symbol buttons */}
          <div className="flex space-x-1 py-2">
            <button
              onClick={() => handleConnectiveClick("¬")}
              className="text-xs px-1 py-1 border rounded-md hover:bg-black"
            >
              ¬
            </button>
            <button
              onClick={() => handleConnectiveClick("∧")}
              className="text-xs px-1 py-1 border rounded-md hover:bg-black"
            >
              ∧
            </button>
            <button
              onClick={() => handleConnectiveClick("∨")}
              className="text-xs px-1 py-1 border rounded-md hover:bg-black"
            >
              ∨
            </button>
            <button
              onClick={() => handleConnectiveClick("→")}
              className="text-xs px-1 py-1 border rounded-md hover:bg-black"
            >
              →
            </button>
            <button
              onClick={() => handleConnectiveClick("↔")}
              className="text-xs px-1 py-1 border rounded-md hover:bg-black"
            >
              ↔
            </button>
            <button
              onClick={() => handleConnectiveClick("∀")}
              className="text-xs px-1 py-1 border rounded-md hover:bg-black"
            >
              ∀
            </button>
            <button
              onClick={() => handleConnectiveClick("∃")}
              className="text-xs px-1 py-1 border rounded-md hover:bg-black"
            >
              ∃
            </button>
          </div>
        </div>

        <button
          className="px-4 py-2 mt-4 bg-blue-500 hover:bg-blue-600 text-white rounded-md"
          onClick={handleCheck}
        >
          Check
        </button>
      </div>
    </main>
  );
}
