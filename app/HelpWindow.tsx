import React from "react";

const HelpWindow = ({ onClose }: any) => {
  return (
    <div className="bg-gray-300 text-black rounded-lg p-8 shadow-lg ">
      <h2 className="text-bold text-lg">Instructions</h2>
      <hr></hr>
      <br></br>
      <p>
        The task for these symbolizations problems is to provide a translation
        of the English sentence in the relevant formal language (propositional
        or predicate logic).{" "}
      </p>
      <br></br>
      <p>
        To do so you will first need to enter a scheme of abbreviation, which is
        like the translation manual for the simple expressions. Enter a symbol
        and choose, from the dropdown menu, what simple English expression it
        stands for.
      </p>
      <br></br>
      <p>
        Next type in the formal sentence (of propositional logic or predicate
        logic) that translates the English sentence based on the scheme of
        abbreviation.
      </p>
      <br></br>
      <p>
        For example, for the English sentence "Sam didn't sing" one could choose
        "P" to stand for "Sam sang", and then enter "¬P" as the propositional
        logic symbolization. Or for predicate logic, one could choose "a" to for
        "Sam", "F" for "sang", and then enter "¬Fa" as the predicate logic
        symbolization.
      </p>

      <br></br>
      <p>
        [ Note: Any translation that is logically equivalent to a correct
        symbolization (modulo alphabetic variance) is correct.]
      </p>
      <div className="flex justify-between">
        <button className="ml-auto hover:text-gray-800" onClick={onClose}>
          <svg
            className="w-6 h-6"
            fill="none"
            strokeLinecap="round"
            strokeLinejoin="round"
            strokeWidth="2"
            viewBox="0 0 24 24"
            stroke="currentColor"
          >
            <path d="M6 18L18 6M6 6l12 12"></path>
          </svg>
        </button>
      </div>
    </div>
  );
};

export default HelpWindow;
