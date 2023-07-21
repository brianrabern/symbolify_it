wff
    -> proposition
    | "¬" wff
    | "(" wff ws connective ws wff ")"

connective
    -> "∧"
    | "∨"
    | "→"
    | "↔"

proposition -> [A-Z]

ws -> null | " "


# npx nearleyc propositional_logic.ne -o propositional_logic.js
