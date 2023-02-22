open Types

(** A vertex in the implication graph.

    A vertex keeps track of one assignment along with the decision level at
    which that assignment was made.
  *)
type vertex = {
  variable : literal;  (** The variable that was assigned *)
  value : bool;  (** The value given to the variable *)
  decision_level : int;  (** The decision level of this implication *)
}

(** Create a new vertex for the decision graph.

    [make_vertex var vl dl] creates a vertex representing the assignment of
    value [vl] to variable [var] at decision level [dl].
let make_vertex (var : literal) (vl : bool) (dl : int) : vertex =
  { variable = var; value = vl; decision_level = dl; }
  *)

module VertexHash =
  struct
    type t = vertex
    let equal v1 v2 = v1.variable = v2.variable &&
                      v1.value = v2.value &&
                      v1.decision_level = v2.decision_level
    let compare v1 v2 =
      if v1.variable = v2.variable
      then if v1.value = v2.value
           then compare v1.decision_level v2.decision_level
           else compare v1.value v2.value
      else compare v1.variable v2.variable
    (* hash is based on szudzik.com/ElegantPairing.pdf *)
    let hash v =
      let x = int_of_lit v.variable in
      let y = v.decision_level in
      let szudzik = if x >= y then y * y + x else x * x + x + y in
      (2 * szudzik + (if v.value then 1 else 0)) land max_int
  end

module IntHash =
  struct
    type t = int
    let compare = compare
    let default = - 1
  end

(** A module for interacting with implication graphs.

    An implication graph has vertices labeled with assignments (represented by
    the [vertex] type) and edges labeled with integers representing clauses.
  *)
module IGraph = Graph.Persistent.Digraph.ConcreteLabeled(VertexHash)(IntHash)

(** The state of a SAT query. *)
type sat_state = {
  formula : formula;  (** The current formula *)
  variables : varset;  (** Unassigned variables *)
  interpretation : assignment;  (** Assigned variables *)
  unsat_clauses : ISet.t;  (** Clauses which are still unsatisfied. *)
  decision_level : int;  (** The current decision level *)
  watch_lits : ISet.t LMap.t;
  (** Map from literals to the clauses they watch *)
  graph : IGraph.t;  (** The implication graph *)
  conflict : bool;  (** True when a conflict has been detected *)
}

(** Create a fresh SAT state for a formula.

    [initialize_state f] creates a new state for the SAT solver with the
    formula [f] and all of the variables which appear in [f] unassigned.
  *)
let initialize_state (f : formula) =
  let choose_watch_literals (f : formula) : ISet.t LMap.t =
    let cl_list = List.map (fun (i, c) -> (i, choose_two_literals c))
                           (get_labeled_clauses f) in
    let add_cl (ci : int) (cur : ISet.t option) : ISet.t  option =
      match cur with
      | None -> Some (ISet.singleton ci)
      | Some c -> Some (ISet.add ci c) in
    let fold_fun (ci, (l1, l2)) acc =
      LMap.update l1 (add_cl ci) (LMap.update l2 (add_cl ci) acc) in
    List.fold_right fold_fun cl_list LMap.empty in
  { formula = f;
    variables = collect_formula_literals f;
    interpretation = empty_assignment;
    unsat_clauses = get_clause_indices f;
    decision_level = 0;
    watch_lits = choose_watch_literals f;
    graph = IGraph.empty;
    conflict = false;
  }

(** Determine whether the formula is satisfied in the current state. *)
let satisfied (st : sat_state) : bool =
  ISet.is_empty st.unsat_clauses

(** Choose decision variables arbitrarily. *)
let arbitrary_branching (st : sat_state) : literal * bool =
  let v = choose_arbitrary_variable st.variables in
  (v, True)

(** Update the SAT state after making a decision assignment. *)
let make_decision (var : literal) (value : bool) (st : sat_state) : sat_state =
  { st with
    variables = remove_variable var st.varset;
    interpretation = add_interpretation var value st.interpretation;
    decision_level = st.decision_level + 1;
  }

(** Propagate unit clauses and update SAT state.

    [propagate_units asgns st] checks whether the set of assignments defined by
    [asgns] causes any new unit clauses and assigns new literals accordingly.
  *)
let rec propagate_units (asgns : (literal * bool) list)
                        (st : sat_state) : sat_state =
  match asgns with
  | [] -> st
  | (var, value) :: t ->
      let st1 =
        { st with
          variables = remove_variable var;
          interpretation = add_interpretation var value st.interpretation;
        } in
      match LMap.find_opt var st1.watch_lits with
      | None -> propagate_units t st1
      | Some cis ->
          let process_clause ci s : ((literal * bool) option, sat_state) =
            match choose_watch_literals (get_clause ci st1.formula)
                                        st.interpretation with
            | [] -> (None, { st1 with conflict = true; }) (* conflict *)
            | [l] -> failwith "undefined"  (* unit clause *)
            | ls -> failwith "undefined"  (* assign new watch lits *)
          in
          let (nasgns, st2) =
            LSet.fold (fun c acc -> match process_clause c with
                                    | (None, st3) -> (acc, st3)
                                    | (Some asgn, st3) -> (asgn :: acc, st3))
                      cis t in
          propagate_units nasgns st2

(** Determine whether there is a conflict in the current implication graph. *)
let has_conflict (st : sat_state) : bool =
  st.conflict

(** Add a conflict clause if there is a conflict. *)
let analyze_conflict (st : sat_state) : int * sat_state =
  failwith "undefined"

(** Return to the given decision level.

    [backtrack_to dl st] unwinds all decisions and propagations back to
    decision level [dl] and changes the variable assignment which was made in
    that decision level.
  *)
let backtrack_to (dl : int) (st : sat_state) : sat_state =
  failwith "undefined"

let recurse (st : sat_state)
            (branch_heuristic : sat_state -> literal * bool) : sat_result =
  if satisfied st
  then make_sat_result true (Some st.interpretation)
  else
    let (var, value) = branch_heuristic st in
    let st1 = make_decision var value st in
    let st2 = propagate_units [(var, value)] st1 in
    if has_conflict st2
    then
      let (dl, st3 = add_conflict_clause st2) in
      recurse (backtrack_to dl st3) branch_heuristic
    else recurse st2 branch_heuristic

(** Add a variable assignment in all relevant structures.

    [add_assignment l v st] returns a new state which is identical to st
    except that the variable [l] has been given the value [v]. Concretely, this
    substitutes [v] for [l] in the formula, removes [l] from the set of
    unassigned variables, and adds the assignment [l -> v] to the list of
    current variable assignments.
  *)
let add_assignment (l : literal) (v : bool) (st : sat_state) : sat_state =
  { st with
    formula = substitute st.formula l v;
    variables = remove_variable l st.variables;
    interpretation = add_interpretation l v st.interpretation;
  }

(** Find a unit clause within a formula if one exists. *)
let find_unit_clause (f : formula) : (int * clause) option =
  formula_find (fun c -> Option.is_some (get_unit_literal c)) f

(** Assign all literals from unit clauses.

    [simplify_unit_clauses st] creates a new state in which each variable
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
let rec simplify_unit_clauses (st : sat_state) : sat_state =
  match find_unit_clause st.formula with
  | None -> st  (* No unit clauses, we're finished. *)
  | Some (_, c) ->   (* There is a unit clause, assign it and recur. *)
      let l = Option.get (get_unit_literal c) in
      if is_negated l
      then simplify_unit_clauses (add_assignment (neg l) false st)
      else simplify_unit_clauses (add_assignment l true st)

(** Assign any literals which appear pure in the formula.

    [simplify_pure_literals st] generates a new state in which any literal
    which appears only positive or only negative in the formula is assigned
    appropriately. Such literals are said to be "pure" in the formula. For
    example, suppose a variable [x1] appears in the formula, but its negation
    [!x1] does not appear. Then we can assign [x1] to [true] because this
    cannot introduce a [false] term anywhere in the formula. Similarly, if
    [!x1] appears but not [x1], then we may assign [x1] to [false].
  *)
let rec simplify_pure_literals (st : sat_state) : sat_state =
  (* [pure_value] determines whether a specific literal appears pure in the
     formula *)
  let pure_value (l : literal) (f : formula) : bool option =
    let signs = List.filter_map (clause_sign l) (get_clauses f) in
    (* [signs] gives the sign of [l] in each clause of the formula *)
    if List.for_all Fun.id signs  (* [l] is pure positive. *)
    then Some true
    else if List.for_all not signs  (* [l] is pure negative. *)
         then Some false
         else None in  (* [l] is not pure. *)
  match varset_find_first (fun x -> Option.is_some (pure_value x st.formula))
                          st.variables with
  | None -> st  (* No literals are pure, we're done. *)
  | Some l ->  (* Some literal appears pure in the formula. *)
      let v = Option.get (pure_value l st.formula) in
      simplify_pure_literals (add_assignment l v st)

(** Simplify a formula prior to the start of the solving algorithm.

    [simplify st] is a new SAT state where any pure literals have been assigned
    and any unit clauses which appear in the initial formula have been
    propagated.
  *)
let simplify (st : sat_state) : sat_state =
  let st1 = simplify_pure_literals st in
  simplify_unit_clauses st1

let solve (form : formula) : sat_result =
  (* Modify the formula to make sure each variable only appears at most
     once within each clause. *)
  let f = remove_duplicates_within_clauses form in
  let st = initialize_state f in
  recurse (simplify st) arbitrary_branching
