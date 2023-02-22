(** Several type definitions along with low-level interfaces to those types.

    The [Types] module sets up a number of types which are needed by other
    parts of the solver. Most types are opaque and can be intereacted with
    using supplied functions from this module.
  *)

module ISet = Set.Make(Int)

(** {0 Literals} *)

type literal
(** A literal is either a variable or its negation.

    A literal is represented by an integer. The variables in the formula are
    positive integers, while the negation of any variable is represented by
    the negation of the assiciated integer.
  *)

val lit_of_int : int -> literal
(** Convert an integer to a literal. *)

val int_of_lit : literal -> int
(** Convert a literal to an integer. *)

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

module Literal
(** A literal interface for functor instantiation. *)

module LMap

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

val choose_watch_literals : clause -> assignment -> literal list

(** {0 Clauses} *)

type clause
(** A clause is a set of literals joined by disjunction. *)

val get_unit_literal : clause -> literal option
(** Get the literal from a unit clause if possible.

    If [cl] is a unit clause then [get_unit_literal cl] returns the only
    literal in [cl]. Otherwise it returns [None].
  *)

val clause_sign : literal -> clause -> bool option
(** Find the sign of a variable in a clause.

    [clause_sign l c] returns [Some true] if [l] is a (non-negated) variable
    in [c], [Some false] if [l] is a negated variable in [c], and [None] if
    [l] does not appear in [c]. Note that [l] is expected to be positive.
  *)

val choose_two_literals : clause -> literal * literal;

(** {0 Formulae} *)

type formula
(** A propositional formula. *)

val get_clauses : formula -> clause list
(** Get the clauses of a formula.

    [get_clauses f] returns all of the clauses in [f]. Note that they may be
    given in any arbitrary order.
  *)

val get_clause : int -> formula -> clause
(** Get a clause from a formula by its label. *)

val get_labeled_clauses : formula -> (int * clause) list
(** Get the clauses of a formula along with their labels. *)

val collect_formula_literals : formula -> varset
(** Find all variables in a formula.

    [collect_formula_literals f] is the set of all variables which appear
    (negated or not) in [f].
  *)

val remove_duplicates_within_clauses : formula -> formula
(** Ensure each clause of a formula has only one copy of each variable.

    [remove_duplicates_within_clauses f] is a version of [f] in which each
    variable appears at most once in each clause. Repeated literals may be
    dropped as they don't affect the truth value of the formula. If both [v]
    and [neg v] appear in a clause for any variable [v], then that clause is
    trivially satisfied.
  *)

val substitute : formula -> literal -> bool -> formula
(** Replace each instance of a literal with a given value.

    [substitute f l v] replaces each instance of [l] with [v] and each instance
    of [neg l] with [not v] in [f].
  *)

val formula_find : (clause -> bool) -> formula -> (int * clause) option
(** Find a clause satisfying some condition.

    [formula_find p f] finds one clause in [f] satisfying the predicate[p]. If
    one is found, it is returned along with its index.
  *)

val get_clause_indices : formula -> ISet.t

(** {0 Results} *)

type sat_result
(** The result of a SAT query.

    The result of a SAT query indicates whether or not a formula is
    satisfiable and, if it is satisfiable, an assignment to the variables which
    satisfies the formula.
  *)

val make_sat_result : bool -> assignment option -> sat_result
(** Create a SAT result. *)
