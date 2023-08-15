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
import HelpWindow from "./HelpWindow";
import astToSmt2Prop from "./astToSmt2Prop.js";
// import Z3SolverForm from "./Z3SolverForm";
// import HelloForm from "./HelloForm.js";
import generateSMTScriptProp from "./generateSMTScriptProp";

type SOA = {
  [key: string]: string;
};

type Problem = {
  id: number;
  sentence: string;
  soa: SOA | any;
  form: string[];
};

type ProbCol = Problem[];

type Entry = {
  symbol: string;
  lexicon: string;
};

export default function Home() {
  const predProblemsA: ProbCol = predProblems as ProbCol;
  const propProblemsA: ProbCol = propProblems as ProbCol;

  const [logic, setLogic] = useState("prop");
  const [isSyntaxVisible, setIsSyntaxVisible] = useState(false);
  const [problemCollection, setProblemCollection] = useState<ProbCol>(
    propProblemsA as ProbCol
  );
  const [selectedProblem, setSelectedProblem] = useState(1);
  const [userFormula, setUserFormula] = useState("");
  const [userSoa, setUserSoa] = useState([{ symbol: "", lexicon: "" }]);
  const [error, setError] = useState(false);
  const [errorText, setErrorText] = useState("");
  const [success, setSuccess] = useState(false);
  const [successText, setSuccessText] = useState("");
  const [note, setNote] = useState(false);
  const [noteText, setNoteText] = useState("");

  const names: string[] = lexiconDataPred[0]?.Names || [];
  const monadic: string[] = lexiconDataPred[1]?.monadicPredicates || [];
  const binary: string[] = lexiconDataPred[2]?.binaryPredicates || [];
  const propositions: string[] = lexiconDataProp[0]?.Propositions || [];

  let lexiconOptions: string[] = [];

  const [showHelp, setShowHelp] = useState(false);

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
      setProblemCollection(predProblemsA as ProbCol);
      setSelectedProblem(propProblems.length + 1);
    } else {
      setLogic("prop");
      setProblemCollection(propProblemsA as ProbCol);
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
    } catch (error) {
      console.error("Error:", error);
    }

    return data;
  };

  async function processSmtPairs(userSmt, sysSmts) {
    const results = [];
    for (const sysSmt of sysSmts) {
      let script = generateSMTScriptProp(userSmt, sysSmt);
      console.log("script: ", script);
      const result = await checkEquiv(script);
      console.log("result: ", result);
      results.push(result);
      console.log("results: ", results);
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
    } catch (error) {
      return false;
    }
  };

  const formulaToAst = (formula, grammar) => {
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(formula);
    return parser.results[0];
  };

  const checkProp = async () => {
    //check if well-formed (or well-formed with added brackets)
    let isWellFormed = syntaxCheck(userFormula, grammarProp);
    if (!isWellFormed) {
      const userFormulaBrackets = "(" + userFormula + ")";
      isWellFormed = syntaxCheck(userFormulaBrackets, grammarProp);
      isWellFormed
        ? setUserFormula(userFormulaBrackets)
        : setUserFormula(userFormula);
    }

    if (!isWellFormed) {
      setError(true);
      setErrorText("Your input is not well-formed. Check the syntax.");
      return;
    }

    //get userSoa
    let userSoaFlat: SOA = {};
    for (let entry of userSoa) {
      userSoaFlat[entry.symbol] = entry.lexicon;
    }
    //alpha convert user formula
    let alphaConUserProp = alphaConversionProp(userSoaFlat, userFormula);
    //list of alpha variants of system formulas
    let alphaConSysProps = selectedProblemObj?.form.map((formula) =>
      alphaConversionProp(selectedProblemObj?.soa, formula)
    );

    //check if user formula is a simple alpha-variant of system formula
    if (alphaConSysProps?.includes(alphaConUserProp)) {
      setSuccess(true);
      setSuccessText("Your symbolization and scheme are perfect.");
      if (alphaConSysProps.length > 1) {
        setNote(true);
        setNoteText(
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

      console.log("equiv?: ", processSmtPairs(userSmt, sysSmts));
      const equiv = await processSmtPairs(userSmt, sysSmts);
      if (equiv) {
        console.log("success");
        setSuccess(true);
        setSuccessText(
          "Your symbolization is correct. It might be deviant but it is logically equivalent to a correct answer."
        );
        if (alphaConSysProps.length > 1) {
          setNote(true);
          setNoteText(
            "Note: The English sentence is ambiguous. This symbolization captures one reading."
          );
        }
      } else if (!equiv) {
        console.log("error");
        setError(true);
        setErrorText(
          "Your symbolization is not logically equivalent to a correct answer"
        );
      }
    } else {
      setError(true);
      setErrorText(
        "There is something wrong with your symbolization or scheme..."
      );
    }
    // console.log("well formed?: ", isWellFormed);
    // console.log("alphaConUserProp : ", alphaConUserProp);
    // console.log("alphaConSysProps : ", alphaConSysProps);
  };

  //   let alphaConSysProps = selectedProblemObj?.form.map((formula) =>
  //   alphaConversionProp(selectedProblemObj?.soa, formula)
  // ); //list of alpha variants of system formulas

  // // check if user formula is well-formed using nearley parser for propositional logic
  // try {
  //   const parser = new nearley.Parser(
  //     nearley.Grammar.fromCompiled(grammarProp)
  //   );
  //   parser.feed(userFormula);
  //   // set results to the parsed result if successful
  //   // results = parser.results[0];

  //   let alphaConUserProp = alphaConversionProp(userSoaFlat, userFormula);

  //   //check if user formula is a simple alpha-variant of system formula
  //   if (alphaConSysProps?.includes(alphaConUserProp)) {
  //     setSuccess(true);
  //     setSuccessText("Your symbolization and scheme are perfect.");
  //     if (alphaConSysProps.length > 1) {
  //       setNote(true);
  //       setNoteText(
  //         "Note: The English sentence is ambiguous. This symbolization captures one reading."
  //       );
  //     }
  //   } else if (!alphaConSysProps?.includes(alphaConUserProp)) {
  //     let smtSysProps = alphaConSysProps?.map((formula) =>
  //       astToSmt2Prop(formula)
  //     ); //list of system smt formulas and props of system formulas
  //     let smtUserProp = astToSmt2Prop(alphaConUserProp); //user smt formulas and props of user formulas
  //     if (processSmtPairs(smtUserProp, smtSysProps)) {
  //       setSuccess(true);
  //       setSuccessText(
  //         "Your symbolization and scheme are logically equivelant to a correct answer."
  //       );
  //       if (alphaConSysProps.length > 1) {
  //         setNote(true);
  //         setNoteText(
  //           "Note: The English sentence is ambiguous. This symbolization captures one reading."
  //         );
  //       }
  //     }
  //     //check if user formula is logically equivalent to one of the system formulas
  //   } else {
  //     setError(true);
  //     setErrorText(
  //       "There is something wrong with your symbolization or scheme..."
  //     );
  //   }
  // } catch (error: any) {
  //   // if there's an error, try parsing with added parentheses
  //   try {
  //     const parser = new nearley.Parser(
  //       nearley.Grammar.fromCompiled(grammarProp)
  //     );
  //     parser.feed("(" + userFormula + ")");

  //     // add parentheses to the user formula if successful
  //     if (parser.results[0] != 0) {
  //       let userFormulaUpdated = "(" + userFormula + ")";
  //       setUserFormula(userFormulaUpdated);
  //       console.log("userFormulaUpdated: ", userFormulaUpdated);
  //       // results = parser.results[0];

  //       //check if user formula is an alpha variant of system formula
  //       let alphaConUserProp = alphaConversionProp(
  //         userSoaFlat,
  //         userFormulaUpdated
  //       );
  //       if (alphaConSysProps?.includes(alphaConUserProp)) {
  //         setSuccess(true);
  //         setSuccessText("Your symbolization and scheme are perfect.");
  //         if (alphaConSysProps.length > 1) {
  //           setNote(true);
  //           setNoteText(
  //             "Note: The English sentence is ambiguous. This symbolization captures one reading."
  //           );
  //         }
  //       } else if (!alphaConSysProps?.includes(alphaConUserProp)) {
  //         setError(true);
  //         setErrorText(
  //           "There is something wrong with your symbolization or scheme..."
  //         );
  //       }
  //     }
  //   } catch (nestedError) {
  //     // handle the error when both attempts fail
  //     setError(true);
  //     setErrorText("Your formula is not well-formed.");
  //     console.log("Parsing error:", error.message);
  //     console.log("Parsing error with parentheses:", nestedError);
  //   }
  // }

  const checkPred = () => {
    console.log("checkPred");
  };

  const handleCheck = () => {
    //propositional logic checks
    if (logic === "prop") {
      checkProp();
    }

    if (logic === "pred") {
      checkPred();
    }

    // //predicate logic checks
    // if (logic === "pred") {
    //   let alphaConSysPred = selectedProblemObj?.form.map((formula) =>
    //     alphaConversionPred(selectedProblemObj?.soa, formula)
    //   );

    //   // check if user formula is well-formed using nearley parser
    //   try {
    //     const parser = new nearley.Parser(
    //       nearley.Grammar.fromCompiled(grammarPred)
    //     );
    //     parser.feed(alphaConversionPred(userSoaFlat, userFormula));
    //     // set results to the parsed result if successful
    //     results = parser.results[0];
    //     console.log(parser.results[0]);
    //     //check if user formula is an alpha variant of system formula
    //     let alphaConUserPred = alphaConversionPred(userSoaFlat, userFormula);
    //     if (alphaConSysPred?.includes(alphaConUserPred)) {
    //       setSuccess(true);
    //       setSuccessText("Your symbolization and scheme are perfect.");
    //       if (alphaConSysPred.length > 1) {
    //         setNote(true);
    //         setNoteText(
    //           "Note: The English sentence is ambiguous. This symbolization captures one reading."
    //         );
    //       }
    //     } else if (!alphaConSysPred?.includes(alphaConUserPred)) {
    //       setError(true);
    //       setErrorText(
    //         "There is something wrong with your symbolization or scheme..."
    //       );
    //     }
    //   } catch (error: any) {
    //     // if there's an error, try parsing with added parentheses
    //     try {
    //       const parser = new nearley.Parser(
    //         nearley.Grammar.fromCompiled(grammarPred)
    //       );
    //       parser.feed("(" + userFormula + ")");

    //       // add parentheses to the user formula if successful
    //       if (parser.results[0] != 0) {
    //         let userFormulaUpdated = "(" + userFormula + ")";
    //         setUserFormula(userFormulaUpdated);
    //         console.log("userFormulaUpdated: ", userFormulaUpdated);
    //         results = parser.results[0];

    //         //check if user formula is an alpha variant of system formula
    //         let alphaConUserPred = alphaConversionPred(
    //           userSoaFlat,
    //           userFormulaUpdated
    //         );

    //         if (alphaConSysPred?.includes(alphaConUserPred)) {
    //           setSuccess(true);
    //           setSuccessText("Your symbolization and scheme are perfect.");
    //           if (alphaConSysPred.length > 1) {
    //             setNote(true);
    //             setNoteText(
    //               "Note: The English sentence is ambiguous. This symbolization captures one reading."
    //             );
    //           }
    //         } else if (!alphaConSysPred?.includes(alphaConUserPred)) {
    //           setError(true);
    //           setErrorText(
    //             "There is something wrong with your symbolization or scheme..."
    //           );
    //         }
    //       }
    //     } catch (nestedError) {
    //       // handle the error when both attempts fail
    //       setError(true);
    //       setErrorText("Your formula is not well-formed.");
    //       console.log("Parsing error:", error.message);
    //       console.log("Parsing error with parentheses:", nestedError);
    //     }
    //   }
    // }
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
      if (note === true) {
        setNote(false);
        setNoteText("");
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
          className="px-4 py-2 mt-4 bg-blue-500 hover:bg-blue-600 text-white rounded-md"
          onClick={handleAddEntry}
        >
          Add Entry
        </button>

        {/* formula input */}
        <div className="mt-2 bg-gray-800 p-4 rounded-md w-full flex flex-col items-center">
          <h2 className="py-2 text-2xl font-bold text-gray-500">Formula</h2>

          <input
            id="userInput"
            className="text-black border-2 border-color-1 rounded-md p-2"
            value={userFormula}
            onChange={handleUserFormula}
            placeholder="Formula"
          />

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
          <button
            onClick={toggleSyntaxVisible}
            className="text-white text-sm font-mono hover:bg-black"
          >
            syntax
          </button>
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
        {note && (
          <div className="border border-t-0 border-yellow-400 rounded-b bg-yellow-100 px-4 py-3 text-yellow-700">
            <p>{noteText}</p>
          </div>
        )}
      </div>
      <button
        className="text-white text-sm font-mono hover:bg-gray-500"
        onClick={toggleHelpWindow}
      >
        help
      </button>
      {showHelp && <HelpWindow onClose={toggleHelpWindow} />}
      {/* z3 test*/}
      {/* <div>
        <h1>Z3 Solver</h1>
        <Z3SolverForm />
      </div> */}
      {/* <div>
        <HelloForm />
      </div> */}
    </main>
  );
}
