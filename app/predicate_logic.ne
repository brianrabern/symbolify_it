wff
    -> predicate term_list
    | "¬" wff
    | "(" wff ws connective ws wff ")"
    | "∀" variable wff
    | "∃" variable wff


term -> variable | constant
term_list -> term | term_list term

quantifier -> "∀"
quantifier -> "∃"

connective
    -> "∧"
    | "∨"
    | "→"
    | "↔"

predicate -> [A-Z] | "F" digit
variable -> [s-z] | "x" digit
constant -> [a-r] | "a" digit
digit -> [1-9] | [1-9] [0-9]

ws -> null | " "


# npx nearleyc predicate_logic.ne -o predicate_logic.js
