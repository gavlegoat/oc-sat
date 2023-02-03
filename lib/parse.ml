open Types

let parse_formula (fn : string) : formula =
  let parse_clause (line : string) : clause =
    let lits = Str.split (Str.regexp "[ \t]+") line in
    clause_of_literal_list (List.map lit_of_string lits) in
  formula_of_clause_list
    (List.map parse_clause (Core.In_channel.read_lines fn))
