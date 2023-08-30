"use client";

import React, { useState, useEffect } from "react";
import Select from "react-select";
import nearley from "nearley";
import grammarProp from "./propositional_logic.js";
import grammarPred from "./predicate_logic.js";
import propProblems from "./propProblems.json";
import predProblems from "./predProblems.json";
import { lexiconDataProp } from "./lexiconProp";
import { lexiconDataPred } from "./lexiconPred.js";
import { alphaConversionProp } from "./alphaConversionProp.js";
import { alphaConversionPred } from "./alphaConversionPred.js";
import astToSmt2Prop from "./astToSmt2Prop.js";
import astToSmt2Pred from "./astToSmt2Pred.js";
import { generateSMTScriptProp } from "./generateSMTScriptProp";
import generateSMTScriptPred from "./generateSMTScriptPred.js";
import HelpWindow from "./HelpWindow";
import LoadingSpinner from "./LoadingSpinner";
import { GrCaretNext } from "react-icons/gr";

type SOA = {
  [key: string]: string;
};

type Problem = {
  id: number;
  sentence: string;
  soa: SOA | any;
  form: string[];
};

type Entry = {
  symbol: string;
  lexicon: string;
};

const predProblemsA: Problem[] = predProblems as Problem[] as const;
const propProblemsA: Problem[] = propProblems as Problem[] as const;

export default function Home() {
  // user interaction
  const [logic, setLogic] = useState("prop");
  const [problemCollection, setProblemCollection] = useState<Problem[]>(
    propProblemsA
  );
  const [selectedProblem, setSelectedProblem] = useState(1);
  const [userFormula, setUserFormula] = useState("");
  const [userSoa, setUserSoa] = useState([{ symbol: "", lexicon: "" }]);

  // feedback
  const [error, setError] = useState<string | null>(null);
  const [success, setSuccess] = useState<string | null>(null);
  const [note, setNote] = useState<string | null>(null);
  const [apiIsLoading, setApiIsLoading] = useState(false);

  // help
  const [isSyntaxVisible, setIsSyntaxVisible] = useState(false);
  const [showHelp, setShowHelp] = useState(false);

  const names: string[] = lexiconDataPred[0]?.Names || [];
  const monadic: string[] = lexiconDataPred[1]?.monadicPredicates || [];
  const binary: string[] = lexiconDataPred[2]?.binaryPredicates || [];
  const propositions: string[] = lexiconDataProp[0]?.Propositions || [];

  let lexiconOptions: string[] = [];

  const toggleSyntaxVisible = () => {
    setIsSyntaxVisible(!isSyntaxVisible);
  };

  const toggleHelpWindow = () => {
    setShowHelp(!showHelp);
  };

  if (logic === "pred") {
    lexiconOptions = [...names, ...monadic, ...binary];
  } else if (logic === "prop") {
    lexiconOptions = [...propositions];
  }

  const toggleLogic = (event: any) => {
    if (logic === "prop") {
      setLogic("pred");
      setProblemCollection(predProblemsA as Problem[]);
      setSelectedProblem(propProblems.length + 1);
    } else {
      setLogic("prop");
      setProblemCollection(propProblemsA as Problem[]);
      setSelectedProblem(1);
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
          propProblemsA.length + 1,
          propProblemsA.length + predProblemsA.length
        );
      } while (randomIndex === selectedProblem);
      setSelectedProblem(randomIndex);
    }
    console.log("random index: " + randomIndex);
  };

  const handleNext = () => {
    setUserFormula("");
    setUserSoa([{ symbol: "", lexicon: "" }]);
    if (logic === "prop" && selectedProblem < propProblemsA.length) {
      setSelectedProblem(selectedProblem + 1);
    } else if (logic === "prop" && selectedProblem === propProblemsA.length) {
      setLogic("pred");
      setProblemCollection(predProblemsA);
      setSelectedProblem(propProblemsA.length + 1);
    } else if (
      logic === "pred" &&
      selectedProblem < propProblemsA.length + predProblemsA.length
    ) {
      setSelectedProblem(selectedProblem + 1);
    } else if (
      logic === "pred" &&
      selectedProblem === propProblemsA.length + predProblemsA.length
    ) {
      setLogic("prop");
      setProblemCollection(propProblemsA);
      setSelectedProblem(1);
    }
  };

  const handleUserFormula = (e: any) => {
    const escapeRegExp = (string: string) => {
      return string.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    };
    let value = e.target.value;

    // Define the mapping of symbols and their replacements
    const symbolMap: { [key: string]: string } = {
      "~": "¬",
      "\\neg": "¬",
      "\\not": "¬",
      "&": "∧",
      "\\wedge": "∧",
      "\\and": "∧",
      "·": "∧",
      "||": "∨",
      "+": "∨",
      "\\vee": "∨",
      "\\or": "∨",
      "->": "→",
      "⇒": "→",
      ">": "→",
      "⊃": "→",
      "\\to": "→",
      "\\then": "→",
      "\\rightarrow": "→",
      "\\supset": "→",
      "<->": "↔",
      "<>": "↔",
      "⇔": "↔",
      "\\leftrightarrow": "↔",
      "\\iff": "↔",
      "\\equiv": "↔",
      "≡": "↔",
      "!": "∀",
      "\\forall": "∀",
      "?": "∃",
      "\\exists": "∃",
    };

    const escapedSymbolMap: { [key: string]: string } = {};
    for (const symbol in symbolMap) {
      escapedSymbolMap[escapeRegExp(symbol)] = symbolMap[symbol];
    }

    let updatedValue = value;
    for (const symbol in escapedSymbolMap) {
      updatedValue = updatedValue.replace(
        new RegExp(symbol, "g"),
        escapedSymbolMap[symbol]
      );
    }

    setUserFormula(updatedValue);
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

  const handleRemoveEntry = (indexToRemove: number) => {
    setUserSoa((prevUserSoa) =>
      prevUserSoa.filter((entry, index) => index !== indexToRemove)
    );
  };

  const handleConnectiveClick = (connective: string) => {
    setUserFormula(userFormula + connective);
    document.getElementById("userInput")?.focus();
  };

  //send to Z3 API to check for logical equivalence
  const checkEquiv = async (smtScript: string) => {
    setApiIsLoading(true);
    let data = "";

    try {
      const response = await fetch("/api/z3_solver", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
        },
        body: smtScript,
      });

      if (!response.ok) {
        throw new Error("Failed to fetch the data.");
      }

      data = await response.text();
      setApiIsLoading(false);
    } catch (e) {
      console.error("Error:", e);
      setApiIsLoading(false);
    }

    return data;
  };

  async function processSmtPairs(userSmt, sysSmts, type) {
    const results = [];
    for (const sysSmt of sysSmts) {
      let script;
      if (type === "prop") {
        script = generateSMTScriptProp(userSmt, sysSmt);
      } else if (type === "pred") {
        script = generateSMTScriptPred(userSmt, sysSmt);
      }
      const result = await checkEquiv(script);
      results.push(result);
    }

    // Check the contents of the results array
    if (results.includes("unsat")) {
      return true; // at least one equivalant result found
    } else if (results.every((result) => result === "sat")) {
      return false; // no equivalant result found
    } else {
      console.log("Error: Mixed results encountered");
    }
  }

  const syntaxCheck = (formula, grammar) => {
    try {
      const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
      parser.feed(formula);
      return parser.results.length === 1;
    } catch (e) {
      return false;
    }
  };

  const formulaToAst = (formula, grammar) => {
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(formula);
    return parser.results[0];
  };

  const checkProp = async () => {
    console.log("checkProp1");
    //check if well-formed (or well-formed with added brackets)
    //get userSoa
    let userSoaFlat: SOA = {};
    for (let entry of userSoa) {
      userSoaFlat[entry.symbol] = entry.lexicon;
    }
    console.log("userSoaFlat: ", userSoaFlat);

    let alphaConUserProp = "";
    console.log("userFormula: ", userFormula);
    let isWellFormed = syntaxCheck(userFormula, grammarProp);
    console.log("isWellFormed: ", isWellFormed);
    if (isWellFormed) {
      alphaConUserProp = alphaConversionProp(userSoaFlat, userFormula);
      console.log("alphaConUserProp: ", alphaConUserProp);
    }
    if (!isWellFormed) {
      const userFormulaBrackets = "(" + userFormula + ")";
      isWellFormed = syntaxCheck(userFormulaBrackets, grammarProp);
      if (isWellFormed) {
        setUserFormula(userFormulaBrackets);
        alphaConUserProp = alphaConversionProp(
          userSoaFlat,
          userFormulaBrackets
        );
      }
    }

    if (!isWellFormed) {
      setError(
        "Your input is not well-formed for propositional logic. Check the syntax."
      );
      if (syntaxCheck(userFormula, grammarPred)) {
        setNote("Note: Your input is a formula of predicate logic.");
      }
      return;
    }

    //list of alpha variants of system formulas
    let alphaConSysProps = selectedProblemObj?.form.map((formula) =>
      alphaConversionProp(selectedProblemObj?.soa, formula)
    );

    //check if user formula is a simple alpha-variant of system formula
    if (alphaConSysProps?.includes(alphaConUserProp)) {
      setSuccess("Your symbolization and scheme are perfect.");
      if (alphaConSysProps.length > 1) {
        setNote(
          "Note: The English sentence is ambiguous. This symbolization captures one reading."
        );
      }
    } else if (!alphaConSysProps?.includes(alphaConUserProp)) {
      //if not a simple alpha variant, check if alpha conversion is logically equivalent to one of the system formula alpha conversions

      let userAst = formulaToAst(alphaConUserProp, grammarProp); // get user ast
      console.log("userAst: ", userAst);
      let userSmt = astToSmt2Prop(userAst); //get user smt formula
      console.log("userSmt: ", userSmt);

      let sysAsts = alphaConSysProps?.map((formula) => {
        return formulaToAst(formula, grammarProp);
      }); //get list of system asts
      console.log("sysAsts: ", sysAsts);

      let sysSmts = sysAsts?.map((ast) => astToSmt2Prop(ast)); //get list of system smt formulas and props of system formulas
      console.log("sysSmts: ", sysSmts);

      const equiv = await processSmtPairs(userSmt, sysSmts, "prop");
      if (equiv) {
        console.log("success");
        setSuccess(
          "Your symbolization is correct. It might be deviant but it is logically equivalent to a correct answer."
        );
        if (alphaConSysProps.length > 1) {
          setNote(
            "Note: The English sentence is ambiguous. This symbolization captures one reading."
          );
        }
      } else if (!equiv) {
        console.log("error");
        setError(
          "Your symbolization is not logically equivalent to a correct answer"
        );
      }
    } else {
      setError(
        "There is something wrong with your symbolization or scheme..."
      );
    }
  };

  const checkPred = async () => {
    console.log("checkPred");
    //check if well-formed (or well-formed with added brackets)
    //get userSoa
    let userSoaFlat: SOA = {};
    for (let entry of userSoa) {
      userSoaFlat[entry.symbol] = entry.lexicon;
    }
    let alphaConUserPred = "";
    let isWellFormed = syntaxCheck(userFormula, grammarPred);
    if (isWellFormed) {
      alphaConUserPred = alphaConversionPred(userSoaFlat, userFormula);
    }
    if (!isWellFormed) {
      const userFormulaBrackets = "(" + userFormula + ")";
      isWellFormed = syntaxCheck(userFormulaBrackets, grammarPred);
      if (isWellFormed) {
        setUserFormula(userFormulaBrackets);
        alphaConUserPred = alphaConversionPred(
          userSoaFlat,
          userFormulaBrackets
        );
      }
    }

    if (!isWellFormed) {
      setError(
        "Your input is not well-formed for predicate logic. Check the syntax."
      );
      if (syntaxCheck(userFormula, grammarProp)) {
        setNote("Note: Your input is a formula of propositional logic.");
      }
      return;
    }

    //list of alpha variants of system formulas
    let alphaConSysPreds = selectedProblemObj?.form.map((formula) =>
      alphaConversionPred(selectedProblemObj?.soa, formula)
    );

    //check if user formula is a simple alpha-variant of system formula
    if (alphaConSysPreds?.includes(alphaConUserPred)) {
      setSuccess("Your symbolization and scheme are perfect.");
      if (alphaConSysPreds.length > 1) {
        setNote(
          "Note: The English sentence is ambiguous. This symbolization captures one reading."
        );
      }
    } else if (!alphaConSysPreds?.includes(alphaConUserPred)) {
      //if not a simple alpha variant, check if alpha conversion is logically equivalent to one of the system formula alpha conversions

      let userAst = formulaToAst(alphaConUserPred, grammarPred); // get user ast
      console.log("userAst: ", userAst);
      let userSmt = astToSmt2Pred(userAst); //get user smt formula
      console.log("userSmt: ", userSmt);

      let sysAsts = alphaConSysPreds?.map((formula) => {
        return formulaToAst(formula, grammarPred);
      }); //get list of system asts
      console.log("sysAsts: ", sysAsts);

      let sysSmts = sysAsts?.map((ast) => astToSmt2Pred(ast)); //get list of system smt formulas and props of system formulas
      console.log("sysSmts: ", sysSmts);

      // console.log("equiv?: ", processSmtPairs(userSmt, sysSmts));
      const equiv = await processSmtPairs(userSmt, sysSmts, "pred");
      if (equiv) {
        console.log("success");
        setSuccess(
          "Your symbolization is correct. It might be deviant but it is logically equivalent to a correct answer."
        );
        if (alphaConSysPreds.length > 1) {
          setNote(
            "Note: The English sentence is ambiguous. This symbolization captures one reading."
          );
        }
      } else if (!equiv) {
        console.log("error");
        setError(
          "Your symbolization is not logically equivalent to a correct answer"
        );
      }
    } else {
      setError(
        "There is something wrong with your symbolization or scheme..."
      );
    }
  };

  const soaCheck = () => {
    function noteAboutWff() {
      const wellFormedProp =
        syntaxCheck(userFormula, grammarProp) ||
        syntaxCheck("(" + userFormula + ")", grammarProp);
      const wellFormedPred =
        syntaxCheck(userFormula, grammarPred) ||
        syntaxCheck("(" + userFormula + ")", grammarPred);
      if (wellFormedProp) {
        setNote("Note: Your input is a formula of propositional logic.");
      } else if (wellFormedPred) {
        setNote("Note: Your input is a formula of predicate logic.");
      } else {
        setNote("Note: Your input is also not a well-formed formula.");
      }
    }
    const missingSymbol = userSoa.some((item) => item.symbol === "");
    const missingLexicon = userSoa.some((item) => item.lexicon === "");

    const coorespond = userSoa.every((item) => {
      const symbolCharCode = item.symbol.charCodeAt(0);
      if (logic == "prop")
        return (
          symbolCharCode >= "A".charCodeAt(0) &&
          symbolCharCode <= "Z".charCodeAt(0)
        );
      else if (
        logic == "pred" &&
        (symbolCharCode < "a".charCodeAt(0) ||
          symbolCharCode > "r".charCodeAt(0)) &&
        (symbolCharCode < "A".charCodeAt(0) ||
          symbolCharCode > "Z".charCodeAt(0))
      ) {
        return false;
      } else if (
        logic == "pred" &&
        symbolCharCode >= "a".charCodeAt(0) &&
        symbolCharCode <= "r".charCodeAt(0)
      ) {
        return names.includes(item.lexicon);
      } else if (
        logic == "pred" &&
        symbolCharCode >= "s".charCodeAt(0) &&
        symbolCharCode <= "z".charCodeAt(0)
      ) {
        return false;
      } else if (
        logic == "pred" &&
        symbolCharCode >= "A".charCodeAt(0) &&
        symbolCharCode <= "Z".charCodeAt(0)
      ) {
        return monadic.includes(item.lexicon) || binary.includes(item.lexicon);
      } else {
        return true;
      }
    });

    if (missingSymbol && missingLexicon) {
      setError(
        "A symbol and English expression are missing in the scheme of abbreviation."
      );
      noteAboutWff();
      return true;
    } else if (missingSymbol) {
      setError("A symbol is missing in the scheme of abbreviation.");
      noteAboutWff();
      return true;
    } else if (missingLexicon) {
      setError(
        "An English expression is missing in the scheme of abbreviation."
      );
      noteAboutWff();
      return true;
    } else if (!coorespond) {
      setError(
        "There is a mismatch between a symbol type and the English expression type."
      );
      noteAboutWff();
      return true;
    }
  };

  const handleCheck = () => {
    if (logic === "prop") {
      if (!soaCheck()) {
        checkProp();
      }
    } else if (logic === "pred") {
      if (!soaCheck()) {
        checkPred();
      }
    }
  };

  const selectedProblemObj = problemCollection.find(
    (problem) => problem.id === selectedProblem
  );

  //messages go away when user clicks anywhere
  useEffect(() => {
    const handleGeneralClick = (e: any) => {
      if (error) {
        setError(null);
      }
      if (success) {
        setSuccess(null);
      }
      if (note) {
        setNote(null);
      }
    };

    document.addEventListener("click", handleGeneralClick);

    // clean up
    return () => {
      document.removeEventListener("click", handleGeneralClick);
    };
  }, [error, success, note]);

  const lexiconOptionsSelect = lexiconOptions.map((item) => ({
    value: item,
    label: item,
  }));

  return (
    <>
      {/* Navigation Bar */}
      <nav className="bg-gray-900 dark:bg-gray-800 p-4 fixed w-full z-50 flex items-center justify-between">
        <div className="flex items-center space-x-2">
          <img
            src="/logo.png" // Replace with the actual path to your logo image
            alt="Symbolify_It Logo"
            className="h-12 w-10"
            title="let us calculate!"
          />
          <div>
            <h1 className="text-2xl font-bold text-yellow-500">symbolify_it</h1>
            <p className="text-gray-500 text-sm">
              an interface for symbolization problems
            </p>
          </div>
        </div>
      </nav>
      {/* Spacer */}
      <div className="bg-gray-100 dark:bg-black p-4 min-w-[400px] min-h-[100px]"></div>
      <main className="p-2 md:p-8 lg:p-12 bg-gray-100 min-h-screen dark:bg-black">
        {/* <main className="p-24"> */}

        <div className="flex items-center space-x-3 mb-3">
          <p className="text-sm font-medium text-gray-900 dark:text-gray-200 mb-1">
            Propositional
          </p>
          <label className="relative inline-flex items-center cursor-pointer">
            <input
              type="checkbox"
              onClick={toggleLogic}
              className="sr-only peer"
            />
            <div className="w-14 h-7 bg-gray-400 peer-focus:outline-none peer-focus:ring-4 peer-focus:ring-blue-300 dark:peer-focus:ring-blue-800 rounded-full peer dark:bg-yellow-400 peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-0.5 after:left-[4px] after:bg-black after:border-gray-300 after:border after:rounded-full after:h-6 after:w-6 after:transition-all dark:border-gray-600 peer-checked:bg-blue-600"></div>{" "}
          </label>
          <span className="text-sm font-medium text-gray-900 dark:text-gray-200">
            Predicate
          </span>
        </div>

        <div>
          <select
            value={selectedProblem}
            onChange={handleProblemChange}
            className="text-black border border-gray-300 rounded-md p-1 mr-2 mb-2 max-w-full w-96 sm:w-96"
          >
            {problemCollection.map((problem, index) => (
              <option key={problem.id} value={problem.id}>
                {problem.id}. {problem.sentence}
              </option>
            ))}
          </select>

          <button
            onClick={handleRandomProblem}
            className="text-sm mb-2 px-2 py-1 bg-yellow-500 text-black rounded-md hover:bg-gray-600 focus:outline-none"
          >
            Random sentence
          </button>
        </div>

        <br></br>
        <br></br>
        <br></br>
        <div className="max-w-screen-md">
          {/* sentence to be symbolized */}
          <div className="mb-2">
            <div className="bg-yellow-500 text-black p-4 rounded-md min-w-[400px]">
              <h2 className="text-2xl font-bold">
                {selectedProblemObj?.sentence}
              </h2>
            </div>
          </div>
          {/* scheme of abbreviation */}
          <div>
            <div className="bg-gray-800 p-4 rounded-md min-w-[400px]">
              <h2 className="py-2 text-xl font-bold text-gray-400 flex justify-center">
                Scheme of Abbreviation
              </h2>
              {userSoa.map((entry, index) => (
                <div key={index} className="flex space-x-4 py-1 justify-center">
                  <input
                    className="text-black border border-gray-300 rounded-md p-2 h-10 w-24 mt-2"
                    type="text"
                    value={entry.symbol}
                    onChange={(e) => handleSymbolChange(index, e.target.value)}
                    placeholder="Symbol"
                  />
                  <span className="text-white mt-2 mx-4 text-2xl font-bold">
                    :
                  </span>
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
                        selectedOption ? selectedOption.value : ""
                      )
                    }
                    options={lexiconOptionsSelect}
                  />{" "}
                  <button
                    className="text-sm mt-2 h-8 px-2 bg-gray-600 hover:bg-red-500 rounded-md"
                    onClick={() => handleRemoveEntry(index)}
                  >
                    Remove
                  </button>
                </div>
              ))}
              <button
                className="text-sm px-4 py-2 mt-4 bg-blue-400 hover:bg-blue-600 text-white rounded-md"
                onClick={handleAddEntry}
              >
                Add Entry
              </button>
            </div>
            {/* formula input */}
            <div>
              <div className="mt-2 bg-gray-800 p-4 rounded-md min-w-[400px]">
                <h2 className="py-2 text-xl font-bold text-gray-400 flex justify-center">
                  Formula
                </h2>
                <div className="flex justify-center">
                  <input
                    id="userInput"
                    className="text-black w-64 border-2 border-color-1 rounded-md p-2"
                    value={userFormula}
                    onChange={handleUserFormula}
                    placeholder="Formula"
                  />
                </div>

                {/* symbol buttons */}
                <div className="max-w-sm mx-auto">
                  <div className="flex space-x-1 px-3 py-2 text-white">
                    <button
                      onClick={() => handleConnectiveClick("¬")}
                      className="flex-grow text-xs px-1 py-1 border rounded-md hover:bg-black"
                    >
                      ¬
                    </button>
                    <button
                      onClick={() => handleConnectiveClick("∧")}
                      className="flex-grow text-xs px-1 py-1 border rounded-md hover:bg-black"
                    >
                      ∧
                    </button>
                    <button
                      onClick={() => handleConnectiveClick("∨")}
                      className="flex-grow text-xs px-1 py-1 border rounded-md hover:bg-black"
                    >
                      ∨
                    </button>
                    <button
                      onClick={() => handleConnectiveClick("→")}
                      className="flex-grow text-xs px-1 py-1 border rounded-md hover:bg-black"
                    >
                      →
                    </button>
                    <button
                      onClick={() => handleConnectiveClick("↔")}
                      className="flex-grow text-xs px-1 py-1 border rounded-md hover:bg-black"
                    >
                      ↔
                    </button>
                    {logic === "pred" && (
                      <button
                        onClick={() => handleConnectiveClick("∀")}
                        className="flex-grow text-xs px-1 py-1 border rounded-md hover:bg-black"
                      >
                        ∀
                      </button>
                    )}
                    {logic === "pred" && (
                      <button
                        onClick={() => handleConnectiveClick("∃")}
                        className=" flex-grow text-xs px-1 py-1 border rounded-md hover:bg-black"
                      >
                        ∃
                      </button>
                    )}
                  </div>
                </div>
                <div className="flex justify-center">
                  <button
                    onClick={toggleSyntaxVisible}
                    className="text-white text-sm font-mono hover:bg-black"
                  >
                    syntax
                  </button>
                </div>
              </div>

              {isSyntaxVisible && logic === "prop" && (
                <div className="max-w-md p-4 bg-white text-black rounded-lg shadow-md">
                  <code className="text-sm font-mono">
                    wff := proposition<br></br>
                    wff := ¬ wff<br></br>
                    wff := ( wff connective wff )<br></br>
                    connective := ∧ | ∨ | → | ↔<br></br>
                    proposition := [A-Z]
                  </code>
                </div>
              )}
              {isSyntaxVisible && logic === "pred" && (
                <div className="max-w-md p-6 bg-white rounded-lg shadow-md">
                  <code className="text-sm text-black font-mono">
                    wff := predicate term_list<br></br>
                    wff := ¬ wff<br></br>
                    wff := ( wff connective wff )<br></br>
                    wff := quantifier variable wff <br></br>
                    term := variable | constant<br></br>
                    term_list := term | term term_list<br></br>
                    quantifier := ∀ | ∃<br></br>
                    connective := ∧ | ∨ | → | ↔<br></br>
                    predicate := [A-Z]<br></br>
                    variable := [s-z]<br></br>
                    constant := [a-r]
                  </code>
                </div>
              )}

              <button
                className="mx-2 px-4 py-2 mt-4 mb-2 bg-blue-400 hover:bg-yellow-600 text-white rounded-md"
                onClick={handleCheck}
              >
                Check
              </button>
              {apiIsLoading && <LoadingSpinner />}

              <br></br>
              {error && (
                <div
                  className="bg-red-100 border border-red-400 text-red-700 px-4 py-3 rounded relative"
                  role="alert"
                >
                  <strong className="font-bold">Hmm. </strong>
                  <span className="block sm:inline">{error}</span>
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
                      <p>{success}</p>
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
              {note && (
                <div className="border border-t-0 border-yellow-400 rounded-b bg-yellow-100 px-4 py-3 text-yellow-700">
                  <p>{note}</p>
                </div>
              )}
            </div>
            <div className="mt-6 flex justify-center">
              <button
                className="text-black dark:text-gray-200 text-sm font-mono hover:bg-gray-500"
                onClick={toggleHelpWindow}
              >
                help?
              </button>
            </div>
            {showHelp && <HelpWindow onClose={toggleHelpWindow} />}
          </div>
        </div>
      </main>
      <div className="text-gray-500 text-sm mt-8 mr-2 mb-2 text-right">
        brian.rabern@gmail.com
      </div>
    </>
  );
}
