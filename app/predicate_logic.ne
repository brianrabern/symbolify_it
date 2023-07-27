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

predicate -> [A-Z]
variable -> [s-z]
constant -> [a-r]

ws -> null | " "


# npx nearleyc predicate_logic.ne -o predicate_logic.js
