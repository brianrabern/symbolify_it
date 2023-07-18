"use client";

import React, { useState } from "react";
import problems from "./problems.json";
import { lexiconData } from "./lexicon.js";
import nearley from "nearley";
import grammar from "./predicate_logic.js";

export default function Home() {
  const [userFormula, setUserFormula] = useState("");
  const [userSoa, setUserSoa] = useState([{ symbol: "", lexicon: "" }]);

  const names: string[] = lexiconData[0]?.Names || [];
  const monadic: string[] = lexiconData[1]?.monadicPredicates || [];
  const binary: string[] = lexiconData[2]?.binaryPredicates || [];
  const lexiconOptions = [...names, ...monadic, ...binary];

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
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    console.log(parser.feed(userFormula).results[0]);
    console.log("SOA", userSoa, "Formula", userFormula);

    let soa = {};
    for (let entry of userSoa) {
      // @ts-ignore
      soa[entry.symbol] = entry.lexicon;
    }
    console.log(areObjectsEqual(soa, problems[0].soa));

    if (areObjectsEqual(soa, problems[0].soa)) {
      console.log("soa correct");
    }
    if (userFormula === problems[0].form) {
      console.log(" form correct");
    }
  };

  return (
    <main className="flex min-h-screen flex-col items-center justify-between p-24">
      {/* sentence to be symbolized */}
      <h1 className="text-6xl font-bold">"Hazel doesn't love Ewan."</h1>

      {/* scheme of abbreviation */}
      <div className="bg-gray-800 p-4 rounded-md w-full flex flex-col items-center">
        <h2 className="py-2 text-2xl font-bold text-blue-500">
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
          className="px-4 py-2 mt-4 bg-blue-500 text-white rounded-md"
          onClick={handleAddEntry}
        >
          Add Entry
        </button>
      </div>

      {/* formula input */}
      <div className="mt-2 bg-gray-800 p-4 rounded-md w-full flex flex-col items-center">
        <h2 className="py-2 text-2xl font-bold text-blue-500">Formula</h2>
        <div>
          <input
            style={{ color: "black" }}
            className="border-2 border-color-1 rounded-md p-2"
            value={userFormula}
            onChange={(e) => setUserFormula(e.target.value)}
            placeholder="Formula"
          />
        </div>
        {/* symbol buttons */}
        <div className="flex space-x-1 py-2">
          <button
            onClick={() => handleConnectiveClick("¬")}
            className="text-xs px-1 py-1 border rounded-md"
          >
            ¬
          </button>
          <button
            onClick={() => handleConnectiveClick("∧")}
            className="text-xs px-1 py-1 border rounded-md"
          >
            ∧
          </button>
          <button
            onClick={() => handleConnectiveClick("∨")}
            className="text-xs px-1 py-1 border rounded-md"
          >
            ∨
          </button>
          <button
            onClick={() => handleConnectiveClick("→")}
            className="text-xs px-1 py-1 border rounded-md"
          >
            →
          </button>
          <button
            onClick={() => handleConnectiveClick("↔")}
            className="text-xs px-1 py-1 border rounded-md"
          >
            ↔
          </button>
          <button
            onClick={() => handleConnectiveClick("∀")}
            className="text-xs px-1 py-1 border rounded-md"
          >
            ∀
          </button>
          <button
            onClick={() => handleConnectiveClick("∃")}
            className="text-xs px-1 py-1 border rounded-md"
          >
            ∃
          </button>
        </div>
      </div>

      <button
        className="px-6 py-3 bg-cyan-500 text-white rounded-md shadow-md font-medium"
        onClick={handleCheck}
      >
        Check
      </button>
    </main>
  );
}
