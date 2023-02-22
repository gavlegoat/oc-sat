open Sat.DPLL.Types
open Sat.DPLL.Solve

let form = parse_formula "test.cnf"
let config = { unit_prop = true;
               pure_literal_prop = true }
let res = solve form config
let () = if is_satisfied res
         then (print_endline "SAT" ; print_assignment res)
         else print_endline "UNSAT"
