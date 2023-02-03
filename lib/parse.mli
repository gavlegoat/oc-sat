val parse_formula : string -> Types.formula
(** Parse a formula from a CNF file.

    [parse_formula fn] reads a propositional logic formula from the file [fn].
    The file is expected to contain a formula in conjunctive normal form. Each
    variable in the formula is represented by a positive integer, and the
    negation of a variable is represented by the negation of the associated
    integer. Each line in the file is a whitespace-separated list of integers
    representing one clause of the formula. The file may not contain anything
    besides a set of clauses. For example, the formula
    {[(x1 || x2) && (!x2 || x3 || !x4) && (!x1 || !x3)]}
    is represesented in the file as
    {[1 2
      -2 3 -4
      -1 3]}
 *)
