type literal
val lit_of_int : int -> literal
val lit_of_string : string -> literal
val base_literal : literal -> literal
val neg : literal -> literal
val is_negated : literal -> bool
val print_literal : literal -> unit

type varset
val print_varset : varset -> unit
val choose_arbitrary_variable : varset -> literal
val remove_variable : literal -> varset -> varset
val varset_find_first : (literal -> bool) -> varset -> literal option

type clause
val clause_of_literal_list : literal list -> clause
val clause_contains : literal -> clause -> bool
val clause_sign : literal -> clause -> bool option
val clause_remove_duplicates : clause -> clause
val eliminate_literal : literal -> clause -> clause
val get_unit_literal : clause -> literal option
val collect_clause_literals : clause -> varset
val print_clause : clause -> unit

type formula
val formula_of_clause_list : clause list -> formula
val get_clauses : formula -> clause list
val formula_map : (clause -> clause) -> formula -> formula
val strip_satisfied_clauses : formula -> formula
val formula_satisfied : formula -> bool
val formula_unsatisfiable : formula -> bool
val collect_formula_literals : formula -> varset
val remove_duplicates_within_clauses : formula -> formula
val print_formula : formula -> unit

type assignment
val empty_assignment : assignment
val add_interpretation : literal -> bool -> assignment -> assignment

type sat_config = {
  unit_prop : bool;
  pure_literal_prop : bool
}

type sat_result
val make_sat_result : bool -> assignment option -> sat_result
val is_satisfied : sat_result -> bool
val get_var_assignment : literal -> sat_result -> bool option
val print_assignment : sat_result -> unit
