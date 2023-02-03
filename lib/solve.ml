open Types

(** The state of a SAT query. *)
type sat_state = {
  formula : formula;  (** The current formula *)
  variables : varset;  (** Unassigned variables *)
  interpretation : assignment;  (** Assigned variables *)
}

(** Replace a variable with a concrete value in a formula.

    [substitute form lit val] replaces each instance of [lit] in the formula
    [form] with the boolean value [value], and each instance of [- lit] with
    [not value]. *)
let substitute (f : formula) (l : literal) (value : bool) : formula =
  let subst (cl : clause) (l : literal) (value : bool) : clause =
    if clause_contains (if value then l else neg l) cl
    then clause_of_literal_list [lit_of_int 0]
    else eliminate_literal l cl in
  let form = formula_map (fun c -> subst c l value) f in
  strip_satisfied_clauses form

(** Add a variable assignment in all relevant structures.

    [add_assignment l v st] returns a new state which is identical to st except
    that the variable [l] has been given the value [v]. Concretely, this
    substitutes [v] for [l] in the formula, removes [l] from the set of
    unassigned variables, and adds the assignment [l -> v] to the list of
    current variable assignments.
  *)
let add_assignment (l : literal) (v : bool) (st : sat_state) : sat_state =
  { formula = substitute st.formula l v;
    variables = remove_variable l st.variables;
    interpretation = add_interpretation l v st.interpretation }

(** Assign all literals from unit clauses.

    [propagate_unit_clauses st] creates a new state in which each variable
    which appears alone in a clause has been assigned. If a clause contains
    only a single literal, then in order for that clause to be satisfied, the
    literal must be true. For example, if our formula contains the clause
    [!x1], then the variable [x1] must be assigned [false] in order for the
    formula to be satisfied. This assignment may cause another clause to become
    a unit clause, so [propogate_unit_clauses] recurses until no more unit
    clauses exist in the formula. For example (by slight abuse of notation)
    {[propogate_unit_clauses (!x1 && (x1 || x2) && (!x2 || !x3) && (x4 || x5))
        = propagate_unit_clauses (x2 && (!x2 || !x3) && (x4 || x5))
        = propagate_unit_clauses (!x3 && (x4 || x5))
        = propagate_unit_clauses (x4 || x5)
        = (x4 || x5)]}
    while emitting the assignments [x1 -> false, x2 -> true, x3 -> false].
  *)
let rec propagate_unit_clauses (st : sat_state) : sat_state =
  (* [find_unit_clause] identifies a literal which appears along in a clause,
     if one exists. *)
  let rec find_unit_clause (cls : clause list) : literal option =
    match cls with
    | [] -> Option.none
    | h :: t -> match get_unit_literal h with
                | None -> find_unit_clause t
                | l -> l in
  match find_unit_clause (get_clauses st.formula) with
  | None -> st  (* No unit clauses, we're finished. *)
  | Some l ->   (* There is a unit clause, assign it and recur. *)
      if is_negated l
      then propagate_unit_clauses (add_assignment (neg l) false st)
      else propagate_unit_clauses (add_assignment l true st)

(** Assign any literals which appear pure in the formula.

    [propagate_pure_literals st] generates a new state in which any literal
    which appears only positive or only negative in the formula is assigned
    appropriately. Such literals are said to be "pure" in the formula. For
    example, suppose a variable [x1] appears in the formula, but its negation
    [!x1] does not appear. Then we can assign [x1] to [true] because this
    cannot introduce a [false] term anywhere in the formula. Similarly, if
    [!x1] appears but not [x1], then we may assign [x1] to [false].
  *)
let rec propagate_pure_literals (st : sat_state) : sat_state =
  (* [pure_value] determines whether a specific literal appears pure in the
     formula *)
  let pure_value (l : literal) (f : formula) : bool option =
    let signs = List.filter_map (clause_sign l) (get_clauses f) in
    (* [signs] gives the sign of [l] in each clause of the formula *)
    if List.for_all Fun.id signs  (* [l] is pure positive. *)
    then Option.some true
    else if List.for_all not signs  (* [l] is pure negative. *)
         then Option.some false
         else Option.none in  (* [l] is not pure. *)
  match varset_find_first (fun x -> Option.is_some (pure_value x st.formula))
                          st.variables with
  | None -> st  (* No literals are pure, we're done. *)
  | Some l ->  (* Some literal appears pure in the formula. *)
      let v = Option.get (pure_value l st.formula) in
      propagate_pure_literals (add_assignment l v st)

(** The main workhorse of the solver.

    [recurse cfg st] is the main loop in the SAT solver. It implements the
    DPLL algorithm. At each iteration, we first perform any deterministic
    assignments we can make using unit propagation and pure literal propagation
    (assuming they are enabled in the configuration). Then, we check whether
    the formula is satisfied by the current assignment or whether it has
    reached a trivially unsatisfiable state. Finally, if there are no more
    deterministic assignments and the satisfiability of the formula is still
    unknown, then we choose one unassigned variable and assign it a value
    arbitrarily. If this value leads to an unsatisfiable formula, then we try
    the other assignment.
  *)
let rec recurse (cfg : sat_config) (st : sat_state) : sat_result =
  (* Perform deterministic assignments. *)
  let st1 = if cfg.unit_prop then propagate_unit_clauses st else st in
  let st2 = if cfg.pure_literal_prop
            then propagate_pure_literals st1
            else st1 in
  (* Check if we've solved the problem. *)
  if formula_satisfied st2.formula
  then make_sat_result true (Option.some st2.interpretation)
  else
    if formula_unsatisfiable st2.formula
    then make_sat_result false Option.none
    else
      (* Choose and assign a variable. *)
      let v = choose_arbitrary_variable st2.variables in
      let res = recurse cfg (add_assignment v true st2) in
      if is_satisfied res
      then res
      (* If the formula is not sat, try the other assignment for [v]. *)
      else recurse cfg (add_assignment v false st2)

let solve (form : formula) (cfg : sat_config) : sat_result =
  let vars = collect_formula_literals form in
  (* Preprocess the formula to make sure each variable only appears at most
     once within each clause. *)
  let f = remove_duplicates_within_clauses form in
  let st = { formula = f;
             variables = vars;
             interpretation = empty_assignment } in
  recurse cfg st
