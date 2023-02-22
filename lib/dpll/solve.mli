open Types

val solve : formula -> sat_config -> sat_result
(** Solve a SAT query.

    [solve form cfg] is the main entry point for the DPLL SAT solver. It takes
    a formula together with a set of configuration values and determines
    whether the formula is satisfiable.
  *)
