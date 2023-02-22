(** Several type definitions along with low-level interfaces to those types.

    The [Types] module sets up a number of types which are needed by other
    parts of the solver. Most types are opaque and can be intereacted with
    using supplied functions from this module.
  *)

(** {0 Literals} *)

type literal
(** A literal is either a variable or its negation.

    A literal is represented by an integer. The variables in the formula are
    positive integers, while the negation of any variable is represented by
    the negation of the assiciated integer.
  *)

val lit_of_int : int -> literal
(** Convert an integer to a literal. *)

val lit_of_string : string -> literal
(** Convert a string to a literal.

    [lit_of_string s] creates a literal by parsing [s] as an integer then
    converting the resulting integer to a literal.
  *)

val base_literal : literal -> literal
(** Get the positive version of this literal.

    [base_literal l] yields [l] ifself if [l] is a variable and if [l] is a
    negation then [base_literal l] gives the variable which has been negated.
  *)

val neg : literal -> literal
(** Negate a literal

    [neg l] is the logical negation of the literal [l].
  *)

val is_negated : literal -> bool
(** Determine whether a literal is a negation. *)

val print_literal : literal -> unit
(** Print a literal to stdout. *)

(** {0 Variable Sets} *)

type varset
(** A set of variables.

    Because literals represent either variables or their negations, variables
    are returned as literals. Functions which interact with [varset] will only
    return positive literals, i.e., variables.
  *)

val choose_arbitrary_variable : varset -> literal
(** Choose one variable from a set of variables.

    [choose_arbitrary_variable vs] chooses one variable from [vs] but makes no
    guarantee about which variable is picked.
  *)

val remove_variable : literal -> varset -> varset
(** Remove one variable from a set of variables.

    [remove_variable l vs] is a copy of [vs] except that [l] has been removed.
    If [l] is not in [vs] or if [l] is negated then [vs] is returned.
  *)

val varset_find_first : (literal -> bool) -> varset -> literal option
(** Find a variable which satisfies a condition.

    [varset_find_first pred vs] finds a variable [l] in [vs] for which [pred l]
    is true. If no such variable exists in [vs] then the result of
    [varset_find_first] is [None].
  *)

val print_varset : varset -> unit
(** Print a set of variables to stdout. *)

(** {0 Clauses} *)

type clause
(** A clause is a set of literals joined by disjunction. *)

val clause_of_literal_list : literal list -> clause
(** Convert a list of literals to a clause.

    [clause_of_literal_list lits] is a clause representing the disjunction of
    all of the literals in [lits].
  *)

val satisfied_clause : clause
(** Create a satisfied clause.

    [satisfied_clause] is a special clause which has no literals and represents
    a satisfied clause in a formula.
  *)

val clause_contains : literal -> clause -> bool
(** Determin whether a literal appears in a clause.

    [clause_contains l c] is true if literal [l] appears in clause [c].
  *)

val clause_sign : literal -> clause -> bool option
(** Find the sign of a variable in a clause.

    [clause_sign l c] returns [Some true] if [l] is a (non-negated) variable
    in [c], [Some false] if [l] is a negated variable in [c], and [None] if
    [l] does not appear in [c]. Note that [l] is expected to be positive.
  *)

val clause_remove_duplicates : clause -> clause
(** Remove duplicate literals from a clause.

    [clause_remove_duplicates c] finds and removes any duplicate literals from
    [c]. Note that this can cause a clause to become satisfied if both [l] and
    [neg l] appear in the clause for any literal [l].
  *)

val eliminate_literal : literal -> clause -> clause
(** Remove a literal from a clause.

    [eliminate_literal l c] removes [l] and [neg l] from [c] without changing
    any other literals.
  *)

val get_unit_literal : clause -> literal option
(** Determine whether this is a unit clause and return the literal if it is.

    [get_unit_literal c] first checks if [c] is a unit clause, i.e., has only
    one literal. If it is, then [get_unit_literal c] is [Some l] where [l] is
    the only literal in [c]. Otherwise, it is [None].
  *)

val collect_clause_literals : clause -> varset
(** Find all of the variables in a clause.

    [collect_clause_literals c] returns the set of all variables which appear
    (whether negated or not) in [c].
  *)

val print_clause : clause -> unit
(** Print a clause to stdout. *)

(** {0 Formulae} *)

type formula
(** A propositional formula.

    Formulas are stored in conjunctive normal form, i.e., as a conjunction of
    clauses. Note that the order of clauses in formulas does not matter, so
    in general conversions between a formula and a clause list or other formula
    functions may arbitrarily reorder clauses.
  *)

val formula_of_clause_list : clause list -> formula
(** Convert a list of clauses to a formula.

    [formula_of_clause_list cs] is a formula representing the conjunction of
    the clause [cs].
  *)

val get_clauses : formula -> clause list
(** Get the clauses in a formula.

    [get_clauses f] is a list of the clauses in the formula [f].
  *)

val find_unit_clause : formula -> clause option
(** Get a unit clause if one exists.

    [find_unit_clause f] gets any unit clause from the formul [f] if one exists
    and returns the clause along with its label.
  *)

val formula_map : (clause -> clause) -> formula -> formula
(** Apply a function to each clause in a formula.

    [formula_map func form] applies the function [func] to each clause in
    [form] and builds a new formula from the result.
  *)

val strip_satisfied_clauses : formula -> formula
(** Remove all satisfied clauses from a formula.

    [strip_satisfied_clauses f] is a copy of [f] with all trivially satisfied
    clauses (i.e., clauses equal to [satisfied_clause]) removed. The resulting
    formula is logically equivalent to [f].
  *)

val formula_satisfied : formula -> bool
(** Determine whether a formula is trivially satisfied.

    [formula_satisfied f] is true if and only if there are no clauses in [f].
    It is usually called after [strip_satisfied_clauses] to ensure that there
    are no more trivial clauses in the formula.
  *)

val formula_unsatisfiable : formula -> bool
(** Determine if a formula is trivially unsatisfiable.

    [formula_unsatisfiable f] is true if and only if [f] contains an
    unsatisfiable clause.
  *)

val collect_formula_literals : formula -> varset
(** Find all variables in a formula.

    [collect_formula_literals f] is the set of all variables which appear
    (negated or not) in [f].
  *)

val remove_duplicates_within_clauses : formula -> formula
(** Remove duplicate literals from within each clause.

    [remove_duplicates_within_clauses f] replaces each clause in [f] with a
    version which has all duplicate literals removed.
  *)

val print_formula : formula -> unit
(** Print a formula to stdout. *)

val parse_formula : string -> formula
(** Read a formula from a file.

    [parse_formula fn] reads a formula in CNF format from the file at [fn]. The
    format is:
      - one clause per line
      - each literal is an integer
      - positive integers represent positive literals, and for a variable [i],
        [- i] represents [neg i].
  *)

(** {0 Assignments/Interpretations} *)

type assignment
(** A map from variables to values.

    A partial assignment (also called an interpretation) assigns a value to
    some subset of the variables of a formula.
  *)

val empty_assignment : assignment
(** Create a new empty assignment.

    [empty_assignment] is an assignment in which no variables have values.
  *)

val add_interpretation : literal -> bool -> assignment -> assignment
(** Add a new variable value to an assignment.

    [add_interpretation l v asgn] is an assignment which extends [asgn] by
    assigning the value [v] to the variable [l].
  *)

(** {0 Configuration} *)

(** Configuration options for a SAT solver. *)
type sat_config = {
  unit_prop : bool;  (** Use unit propagation. *)
  pure_literal_prop : bool  (** Use pure literal propagation. *)
}

(** {0 Results} *)

type sat_result
(** The result of a SAT query.

    The result of a SAT query indicates whether or not a formula is
    satisfiable and, if it is satisfiable, an assignment to the variables which
    satisfies the formula.
  *)

val make_sat_result : bool -> assignment option -> sat_result
(** Create a SAT result.

    [make_sat_result sat asgn] is a SAT result where [sat] indicates whether or
    not the formula is satisfiable and [asgn] is an assignment which satisfies
    the formula if possible.
  *)

val is_satisfied : sat_result -> bool
(** Determine whether a SAT result indicates a formula is satisfiable. *)

val get_var_assignment : literal -> sat_result -> bool option
(** Get a satisfying assignment for a variable from a SAT result.

    [get_var_assignment l res] is the assignment to [l] in the satisfying
    assignment associated with [res]. This function can return [None] in three
    cases:
    - [l] is not a variable, i.e., [l] is negated.
    - The formula is not satisfiable so there is no satisfying assignment.
    - Either value of [l] satisfies the formula so [l] is not assigned in the
      satisfying assignment.
  *)

val print_assignment : sat_result -> unit
(** Print an assignment to stdout. *)
