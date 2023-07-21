"use client";

import React, { useState, useEffect } from "react";
import Select from "react-select";
import predProblems from "./predProblems.json";
import propProblems from "./propProblems.json";
import { lexiconDataPred } from "./lexiconPred.js";
import { alphaConversionPred } from "./alphaConversionPred.js";
import { alphaConversionProp } from "./alphaConversionProp.js";
import nearley from "nearley";
import grammarPred from "./predicate_logic.js";
import grammarProp from "./propositional_logic.js";
import { lexiconDataProp } from "./lexiconProp";
import { GrCaretNext } from "react-icons/gr";

export default function Home() {
  const [logic, setLogic] = useState("prop");
  const [problemCollection, setProblemCollection] = useState(propProblems);
  const [selectedProblem, setSelectedProblem] = useState(1);
  const [userFormula, setUserFormula] = useState("");
  const [userSoa, setUserSoa] = useState([{ symbol: "", lexicon: "" }]);
  const [error, setError] = useState(false);
  const [errorText, setErrorText] = useState("");
  const [success, setSuccess] = useState(false);
  const [successText, setSuccessText] = useState("");

  const names: string[] = lexiconDataPred[0]?.Names || [];
  const monadic: string[] = lexiconDataPred[1]?.monadicPredicates || [];
  const binary: string[] = lexiconDataPred[2]?.binaryPredicates || [];
  const propositions: string[] = lexiconDataProp[0]?.Propositions || [];

  let lexiconOptions: string[] = [];

  if (logic === "pred") {
    lexiconOptions = [...names, ...monadic, ...binary];
  } else if (logic === "prop") {
    lexiconOptions = [...propositions];
  }

  const toggleLogic = (event: any) => {
    // setError(false);
    // setErrorText("");
    // setSuccess(false);
    // setSuccessText("");
    if (logic === "prop") {
      setLogic("pred");
      setProblemCollection(predProblems);
      setSelectedProblem(propProblems.length + 1);
    } else {
      setLogic("prop");
      setProblemCollection(propProblems);
    }
    console.log(logic);
    setUserFormula("");
    setUserSoa([{ symbol: "", lexicon: "" }]);
  };
  console.log(logic);
  const handleProblemChange = (event: any) => {
    const selectedProblem = parseInt(event.target.value);
    setSelectedProblem(selectedProblem);
    setUserFormula("");
    setUserSoa([{ symbol: "", lexicon: "" }]);
  };

  const getRandomNumber = (min: number, max: number) => {
    return Math.floor(Math.random() * (max - min + 1)) + min;
  };

  const handleRandomProblem = () => {
    setUserFormula("");
    setUserSoa([{ symbol: "", lexicon: "" }]);
    let randomIndex;
    if (logic === "prop") {
      do {
        randomIndex = getRandomNumber(1, propProblems.length);
      } while (randomIndex === selectedProblem);
      setSelectedProblem(randomIndex);
    } else {
      do {
        randomIndex = getRandomNumber(
          propProblems.length + 1,
          propProblems.length + predProblems.length
        );
      } while (randomIndex === selectedProblem);
      setSelectedProblem(randomIndex);
    }
    console.log("random index: " + randomIndex);
  };

  const handleNext = () => {
    setUserFormula("");
    setUserSoa([{ symbol: "", lexicon: "" }]);
    if (logic === "prop" && selectedProblem < propProblems.length) {
      setSelectedProblem(selectedProblem + 1);
    } else if (logic === "prop" && selectedProblem === propProblems.length) {
      setLogic("pred");
      setProblemCollection(predProblems);
      setSelectedProblem(propProblems.length + 1);
    } else if (
      logic === "pred" &&
      selectedProblem < propProblems.length + predProblems.length
    ) {
      setSelectedProblem(selectedProblem + 1);
    } else if (
      logic === "pred" &&
      selectedProblem === propProblems.length + predProblems.length
    ) {
      setLogic("prop");
      setProblemCollection(propProblems);
      setSelectedProblem(1);
    }
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

  const handleCheck = () => {
    let results;
    let userSoaFlat = {};
    for (let entry of userSoa) {
      // @ts-ignore
      userSoaFlat[entry.symbol] = entry.lexicon;
    }

    //propositional logic checks
    if (logic === "prop") {
      let alphaConSysProp = alphaConversionProp(
        selectedProblemObj?.soa,
        selectedProblemObj?.form
      );
      // check if user formula is well-formed using nearley parser for propositional logic
      try {
        const parser = new nearley.Parser(
          nearley.Grammar.fromCompiled(grammarProp)
        );
        parser.feed(userFormula);
        // set results to the parsed result if successful
        results = parser.results[0];

        //check if user formula is an alpha variant of system formula
        let alphaConUserProp = alphaConversionProp(userSoaFlat, userFormula);
        if (alphaConUserProp == alphaConSysProp) {
          setSuccess(true);
          setSuccessText("Your symbolization and scheme are perfect.");
        } else if (alphaConUserProp != alphaConSysProp) {
          setError(true);
          setErrorText(
            "That is well-formed but there is something wrong with your symbolization or scheme..."
          );
        }
        // console logs for debugging
        // console.log("SOA1: ", userSoaFlat, ", Formula: ", userFormula);
        // console.log("alphaConUserProp1: ", alphaConUserProp);
        // console.log("alphaConSysProp1: ", alphaConSysProp);
        // console.log("variants1?:", alphaConUserProp == alphaConSysProp);
      } catch (error: any) {
        // if there's an error, try parsing with added parentheses
        try {
          const parser = new nearley.Parser(
            nearley.Grammar.fromCompiled(grammarProp)
          );
          parser.feed("(" + userFormula + ")");

          // add parentheses to the user formula if successful
          if (parser.results[0] != 0) {
            let userFormulaUpdated = "(" + userFormula + ")";
            setUserFormula(userFormulaUpdated);
            console.log("userFormulaUpdated: ", userFormulaUpdated);
            results = parser.results[0];

            //check if user formula is an alpha variant of system formula
            let alphaConUserProp = alphaConversionProp(
              userSoaFlat,
              userFormulaUpdated
            );

            if (alphaConUserProp == alphaConSysProp) {
              setSuccess(true);
              setSuccessText("Your symbolization and scheme are perfect.");
            } else if (alphaConUserProp != alphaConSysProp) {
              setError(true);
              setErrorText(
                "That is well-formed but there is something wrong with your symbolization or scheme..."
              );
            }
          }
        } catch (nestedError) {
          // handle the error when both attempts fail
          setError(true);
          setErrorText("Your formula is not well-formed.");
          console.log("Parsing error:", error.message);
          console.log("Parsing error with parentheses:", nestedError);
        }
      }
    }

    // //predicate logic checks
    if (logic === "pred") {
      let alphaConSysPred = alphaConversionPred(
        selectedProblemObj?.soa,
        selectedProblemObj?.form
      );
      // check if user formula is well-formed using nearley parser for propositional logic
      try {
        const parser = new nearley.Parser(
          nearley.Grammar.fromCompiled(grammarPred)
        );
        parser.feed(userFormula);
        // set results to the parsed result if successful
        results = parser.results[0];

        //check if user formula is an alpha variant of system formula
        let alphaConUserPred = alphaConversionPred(userSoaFlat, userFormula);
        if (alphaConUserPred == alphaConSysPred) {
          setSuccess(true);
          setSuccessText("Your symbolization and scheme are perfect.");
        } else if (alphaConUserPred != alphaConSysPred) {
          setError(true);
          setErrorText(
            "That is well-formed but there is something wrong with your symbolization or scheme..."
          );
        }
        // console logs for debugging
        // console.log("SOA1: ", userSoaFlat, ", Formula: ", userFormula);
        // console.log("alphaConUserProp1: ", alphaConUserProp);
        // console.log("alphaConSysProp1: ", alphaConSysProp);
        // console.log("variants1?:", alphaConUserProp == alphaConSysProp);
      } catch (error: any) {
        // if there's an error, try parsing with added parentheses
        try {
          const parser = new nearley.Parser(
            nearley.Grammar.fromCompiled(grammarPred)
          );
          parser.feed("(" + userFormula + ")");

          // add parentheses to the user formula if successful
          if (parser.results[0] != 0) {
            let userFormulaUpdated = "(" + userFormula + ")";
            setUserFormula(userFormulaUpdated);
            console.log("userFormulaUpdated: ", userFormulaUpdated);
            results = parser.results[0];

            //check if user formula is an alpha variant of system formula
            let alphaConUserPred = alphaConversionPred(
              userSoaFlat,
              userFormulaUpdated
            );

            if (alphaConUserPred == alphaConSysPred) {
              setSuccess(true);
              setSuccessText("Your symbolization and scheme are perfect.");
            } else if (alphaConUserPred != alphaConSysPred) {
              setError(true);
              setErrorText(
                "That is well-formed but there is something wrong with your symbolization or scheme..."
              );
            }
          }
        } catch (nestedError) {
          // handle the error when both attempts fail
          setError(true);
          setErrorText("Your formula is not well-formed.");
          console.log("Parsing error:", error.message);
          console.log("Parsing error with parentheses:", nestedError);
        }
      }
    }
  };

  const selectedProblemObj = problemCollection.find(
    (problem) => problem.id === selectedProblem
  );

  //messages go away when user clicks anywhere
  useEffect(() => {
    const handleGeneralClick = (e: any) => {
      if (error === true) {
        setError(false);
        setErrorText("");
      }
      if (success === true) {
        setSuccess(false);
        setSuccessText("");
      }
    };

    document.addEventListener("click", handleGeneralClick);

    // clean up
    return () => {
      document.removeEventListener("click", handleGeneralClick);
    };
  }, [error, success]);

  const lexiconOptionsSelect = lexiconOptions.map((item) => ({
    value: item,
    label: item,
  }));

  const options = [
    { value: "chocolate", label: "Chocolate" },
    { value: "strawberry", label: "Strawberry" },
    { value: "vanilla", label: "Vanilla" },
  ];
  // const MyComponent = () => <Select options={options} />;

  console.log(userSoa);
  /////////////
  return (
    <main className="flex min-h-screen flex-col items-center justify-between p-24">
      <div>
        <div className="flex items-center space-x-3">
          <p className="text-sm font-medium text-gray-900 dark:text-gray-300 mb-1">
            Propositional Logic
          </p>
          <label className="relative inline-flex items-center cursor-pointer">
            <input
              type="checkbox"
              onClick={toggleLogic}
              className="sr-only peer"
            />
            <div className="w-14 h-7 bg-gray-200 peer-focus:outline-none peer-focus:ring-4 peer-focus:ring-blue-300 dark:peer-focus:ring-blue-800 rounded-full peer dark:bg-yellow-400 peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-0.5 after:left-[4px] after:bg-black after:border-gray-300 after:border after:rounded-full after:h-6 after:w-6 after:transition-all dark:border-gray-600 peer-checked:bg-blue-600"></div>{" "}
          </label>
          <span className="text-sm font-medium text-gray-900 dark:text-gray-300">
            Predicate Logic
          </span>
        </div>

        <div className="absolute top-4 right-4">
          <p className="text-blue-500"> Select a sentence</p>

          <select
            value={selectedProblem}
            onChange={handleProblemChange}
            className="text-black border border-gray-300 rounded-md p-1 mr-2 mb-2"
          >
            {problemCollection.map((problem, index) => (
              <option key={problem.id} value={problem.id}>
                {problem.id}. {problem.sentence}
              </option>
            ))}
          </select>

          <button
            onClick={handleRandomProblem}
            className="text-sm mt-4 px-2 py-2 bg-yellow-500 text-black rounded-md hover:bg-gray-600 focus:outline-none"
          >
            Random problem
          </button>
        </div>
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
              className="text-black border border-gray-300 rounded-md p-2 h-10 w-24 mt-2"
              type="text"
              value={entry.symbol}
              onChange={(e) => handleSymbolChange(index, e.target.value)}
              placeholder="Symbol"
            />
            <span className="mt-2 mx-4 text-2xl font-bold">:</span>
            <Select
              id="lexicon"
              className="text-black rounded-md p-2 w-64"
              value={
                entry.lexicon
                  ? lexiconOptionsSelect.find(
                      (option) => option.value === entry.lexicon
                    )
                  : null
              }
              onChange={(selectedOption) =>
                handleLexiconChange(
                  index,
                  selectedOption ? selectedOption.value : null
                )
              }
              // value={lexiconOptionsSelect.find(
              //   (option) => option.value === entry.lexicon
              // )}
              // onChange={(selectedOption) =>
              //   handleLexiconChange(index, selectedOption.value)
              // }
              options={lexiconOptionsSelect}
            />
            {/* <select
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
            </select> */}
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
            {logic === "pred" && (
              <button
                onClick={() => handleConnectiveClick("∀")}
                className="text-xs px-1 py-1 border rounded-md hover:bg-black"
              >
                ∀
              </button>
            )}
            {logic === "pred" && (
              <button
                onClick={() => handleConnectiveClick("∃")}
                className="text-xs px-1 py-1 border rounded-md hover:bg-black"
              >
                ∃
              </button>
            )}
          </div>
        </div>

        <button
          className="px-4 py-2 mt-4 bg-blue-500 hover:bg-blue-600 text-white rounded-md"
          onClick={handleCheck}
        >
          Check
        </button>
        <br></br>
        {error && (
          <div
            className="bg-red-100 border border-red-400 text-red-700 px-4 py-3 rounded relative"
            role="alert"
          >
            <strong className="font-bold">Hmm. </strong>
            <span className="block sm:inline">{errorText}</span>
            <span className="absolute top-0 bottom-0 right-0 px-4 py-3"></span>
          </div>
        )}

        {success && (
          <div className="relative">
            <div role="alert">
              <div className="bg-green-500 text-white font-bold rounded-t px-4 py-2">
                Correct!
              </div>
              <div className="border border-t-0 border-green-400 rounded-b bg-green-100 px-4 py-3 text-green-700">
                <p>{successText}</p>
              </div>
            </div>{" "}
            <button
              onClick={handleNext}
              className="absolute right-0 top-0 mt-2 mr-2 bg-green-800 text-white px-2 py-1 rounded"
            >
              <GrCaretNext />
            </button>
          </div>
        )}
      </div>
    </main>
  );
}
