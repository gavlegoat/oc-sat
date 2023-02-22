module ISet = Set.Make(Int)

type literal = int

let lit_of_int (i : int) : literal = i

let int_of_lit (l : literal) : int = l

let is_negated (l : literal) : bool = int_of_lit l < 0

let neg (l : literal) : literal = lit_of_int (- int_of_lit l)

let base_literal (l : literal) : literal =
  if is_negated l then neg l else l

let print_literal (l : literal) : unit = print_int l

module Literal = struct
  type t = literal
  let compare = compare
end

module LSet = Set.Make(Literal)

type varset = LSet.t

let print_varset (vars : varset) : unit =
  LSet.iter (fun x -> print_int x ; print_string " ") vars

let choose_arbitrary_variable (vars : varset) : literal =
  LSet.choose vars

let remove_variable (l : literal) (vs : varset) : varset =
  LSet.remove l vs

let varset_find_first (pred : literal -> bool) (vs : varset) : literal option =
  LSet.find_first_opt pred vs

type clause = {
  literals : literal list;
}

let collect_clause_literals (cl : clause) : varset =
  LSet.of_list (List.map base_literal cl.literals)

let get_unit_literal (cl : clause) : literal option =
  match cl.literals with
  | [] -> None
  | h :: [] -> Some h
  | _ -> None

let clause_sign (l : literal) (cl : clause) : bool option =
  List.fold_right (fun v a -> if l = base_literal v
                              then match a with
                                   | None -> Some (not (is_negated v))
                                   | acc -> acc
                              else a) cl.literals None

let choose_two_literals (cl : clause) : literal * literal =
  match cl.literals with
  | h1 :: h2 :: t -> (base_literal h1, base_literal h2)
  | _ -> failwith "choose_two_literals: formula not simplified"

(** Replace each instance of a literal with a value in a clause.

    [clause_substitute cl l v] replaces each instance of [l] with [v] and
    each instance of [neg l] with [not v] in [cl]. If the clause becomes
    satisfied as a result, return None.
  *)
let clause_substitute (cl : clause) (l : literal) (v : bool) : clause option =
  if List.exists (fun lt -> lt = if v then l else neg l) cl.literals
  then None
  else Some {
    literals = List.filter (fun lt -> lt <> l && lt <> neg l) cl.literals
  }

module IMap = Map.Make(Int)

type formula = {
  clauses : clause IMap.t;
}

let get_clauses (f : formula) : clause list =
  let (_, cls) = List.split (List.of_seq (IMap.to_seq f.clauses)) in
  cls

let get_clause (ci : int) (f : formula) : clause =
  LMap.find ci f.clauses

let get_labeled_clauses (f : formula) : (int * clause) list =
  List.of_seq (IMap.to_seq f.clauses)

let collect_formula_literals (f : formula) : varset =
  IMap.fold (fun _ s1 s2 -> LSet.union s1 s2)
            (IMap.map collect_clause_literals f.clauses)
            LSet.empty

let remove_duplicates_within_clauses (_ : formula) : formula =
  failwith "undefined"

let substitute (f : formula) (l : literal) (v : bool) : formula =
  { clauses = IMap.filter_map (fun _ c -> clause_substitute c l v) f.clauses }

let formula_find (p : clause -> bool) (f : formula) : (int * clause) option =
  IMap.find_first_opt (fun i -> p (IMap.find i f.clauses)) f.clauses

let get_clause_indices (f : formula) : ISet.t =
  let (keys, _) = List.split (List.of_seq (IMap.to_seq f.clauses)) in
  ISet.of_list keys

module LMap = Map.Make(Literal)

type assignment = bool LMap.t

let empty_assignment : assignment =
  LMap.empty

let add_interpretation (v : literal) (b : bool) (i : assignment) : assignment =
  LMap.add v b i

let choose_watch_literals (cl : clause) (interp : assignment) : literal list =
  failwith "undefined"

type sat_result = {
  sat : bool;
  interp : assignment option;
}

let make_sat_result (s : bool) (itp : assignment option) : sat_result =
  { sat = s; interp = itp; }
