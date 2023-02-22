open Types

val solve : formula -> sat_result
(** Solve a SAT query.

    [solve form] is the main entry point for the CDCL SAT solver. It takes
    a formula together with a set of configuration values and determines
    whether the formula is satisfiable.
  *)
