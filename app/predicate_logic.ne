wff
    -> predicate
    | predicate "(" term_list ")"
    | "¬" wff
    | "(" wff connective wff ")"
    | "∀" variable wff
    | "∃" variable wff


term -> variable | constant
term_list -> term | term "," term_list

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
