type exports

type imports

type t

type gen_config = {
  num_compartments : int;
  num_exported_funcs : int;
  num_imported_funcs : int;
  max_arg_count : int;
  debug : bool
}

type comp = int
type func = int

val random : gen_config -> Random.State.t -> t

val main : t -> func

val function_list : t -> func list

val compartment_list : t -> comp list

val export_list : t -> (comp * func list) list

val import_list : t -> (comp * (comp * func) list) list

val def_list : t -> (func * comp * AST.signature) list
