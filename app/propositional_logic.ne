wff
    -> proposition
    | "¬" wff
    | "(" wff ws connective ws wff ")"

connective
    -> "∧"
    | "∨"
    | "→"
    | "↔"

proposition -> [A-Z] | "P" digit

digit -> [1-9] | [1-9] [0-9]

ws -> null | " "


# npx nearleyc propositional_logic.ne -o propositional_logic.js
