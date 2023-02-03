(* A literal is represented by an integer. Positive integers are the variables
 * of the formule and negative literals are their negations.
 *)
type literal = int

let lit_of_int (i : int) : literal = i
let int_of_lit (l : literal) : int = l
let lit_of_string (s : string) : literal = lit_of_int (int_of_string s)

let base_literal (lit : literal) : literal =
  if lit < 0 then - lit else lit

let neg (lit : literal) : literal = - lit

let is_negated (lit : literal) : bool = (int_of_lit lit) < 0

let print_literal (lit : literal) : unit =
  print_int lit

(* This module provides a comparison for literal maps and sets. *)
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

let clause_of_literal_list (lits : literal list) : clause =
  clause_remove_duplicates { literals = lits }

let satisfied_clause : clause = { literals = [lit_of_int 0] }

let clause_contains (v : literal) (cl : clause) : bool =
  List.exists (fun l -> l = v) cl.literals

let clause_sign (l : literal) (cl : clause) : bool option =
  List.fold_right (fun v a -> if l = base_literal v
                              then match a with
                                   | None -> Option.some (not (is_negated v))
                                   | acc -> acc
                              else a) cl.literals Option.none

let clause_remove_duplicates (cl : clause) : clause =
  let rec process_literals (lits : literal list)
                           (acc : literal list) : literal list =
    match lits with
    | [] -> List.rev acc
    | h :: t ->
        if List.exists (fun x -> x = neg h) t
        then [lit_of_int 0]
        else process_literals (List.filter (fun x -> x <> h) t) (h :: acc) in
  { literals = process_literals cl.literals [] }

let clause_empty (cl : clause) : bool =
  cl.literals = []

let eliminate_literal (v : literal) (cl : clause) : clause =
  { literals = List.filter (fun l -> v <> l && v <> neg l) cl.literals }

let get_unit_literal (cl : clause) : literal option =
  match cl.literals with
  | [] -> Option.none
  | h :: [] -> Option.some h
  | _ -> Option.none

let clause_satisfied (cl : clause) : bool =
  match cl.literals with
  | [] -> false
  | h :: _ -> int_of_lit h = 0

let collect_clause_literals (cl : clause) : varset =
  LSet.of_list (List.map base_literal cl.literals)

let print_clause (cl : clause) : unit =
  let rec print_lits (lits : literal list) : unit =
    match lits with
    | [] -> ()
    | h :: [] -> print_literal h
    | h :: t -> print_literal h ; print_string " | " ; print_lits t in
  print_lits cl.literals

(* A formula is a list of clauses, implicitly joined by conjunction. *)
type formula = {
  clauses : clause list;
}

let formula_of_clause_list (cls : clause list) : formula =
  { clauses = cls }

let formula_map (f : clause -> clause) (form : formula) : formula =
  { clauses = List.map f form.clauses }

let strip_satisfied_clauses (form : formula) : formula =
  { clauses = List.fold_right
                (fun c a -> if clause_satisfied c
                            then a
                            else c :: a) form.clauses [] }

let formula_satisfied (form : formula) : bool =
  form.clauses = []

let formula_unsatisfiable (form : formula) : bool =
  List.exists clause_empty form.clauses

let get_clauses (f : formula) : clause list = f.clauses

let collect_formula_literals (form : formula) : varset =
  List.fold_right LSet.union
                  (List.map collect_clause_literals form.clauses)
                  LSet.empty

let remove_duplicates_within_clauses (f : formula) : formula =
  strip_satisfied_clauses (formula_map clause_remove_duplicates f)

let print_formula (form : formula) : unit =
  let rec print_clauses (cls : clause list) : unit =
    match cls with
    | [] -> ()
    | h :: [] -> print_string "(" ; print_clause h ; print_string ")"
    | h :: t ->
        print_string "(" ;
        print_clause h ;
        print_string ")" ;
        print_string " & " ;
        print_clauses t in
  print_clauses form.clauses

module LMap = Map.Make(Literal)

type assignment = bool LMap.t

let empty_assignment : assignment =
  LMap.empty

let add_interpretation (v : literal) (b : bool) (i : assignment) : assignment =
  LMap.add v b i

type sat_config = {
  unit_prop : bool;
  pure_literal_prop : bool
}

type sat_result = {
  sat : bool;
  interpretation : assignment option;
}

let make_sat_result (s : bool) (interp : assignment option) : sat_result =
  { sat = s; interpretation = interp }

let is_satisfied (res : sat_result) : bool =
  res.sat

let get_var_assignment (l : literal) (res : sat_result) : bool option =
  match res.interpretation with
  | None -> Option.none
  | Some i -> LMap.find_opt l i

let print_assignment (res : sat_result) : unit =
  match res.interpretation with
  | None -> print_endline ""
  | Some i ->
      LMap.iter
        (fun l v -> print_literal l ;
                    print_string " -> " ;
                    Printf.printf "%b\n" v) i
