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
        or predicate logic).
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
        abbreviation. The syntax for propositional logic is like this:
        &quot;¬P&quot;, &quot;(P→¬Q)&quot;, &quot;((¬S→R)∨P)&quot;, etc. And the
        syntax for predicate logic is like this: &quot;¬Fab&quot;,
        &quot;∀x(Fx→Gx)&quot;, &quot;∃x(Fx∧∀y(Gy→Hxy))&quot;, etc.
      </p>
      <br></br>
      <p>
        For example, for the English sentence &quot;Sam didn&apos;t sing&quot;
        one could choose &quot;P&quot; to stand for &quot;Sam sang&quot;, and
        then enter &quot;¬P&quot; as the propositional logic symbolization. Or
        for predicate logic, one could choose &quot;a&quot; for &quot;Sam&quot;,
        &quot;F&quot; for &quot;sang&quot;, and then enter &quot;¬Fa&quot; as
        the predicate logic symbolization.
      </p>

      <br></br>
      <p>
        The logical sumbols can be entered by clicking the button or by typing
        the relevant keys on your keyboard, for example:{" "}
      </p>
      <br></br>
      <pre className="text-sm font-mono pl-6">
        <code>
          ¬ : ~, \neg<br></br>∧ : &, ·, \wedge<br></br>∨ : ||, +, \vee
          <br></br>→ : -&gt;, \to, \rightarrow<br></br>↔ : &lt;-&gt;,
          \leftrightarrow
          <br></br>∀ : !, \forall<br></br>∃ : ?, \exists
        </code>
      </pre>

      <br></br>
      <p className="text-sm">
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
