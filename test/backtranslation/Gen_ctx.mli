type exports
type imports
type t

type gen_config = {
  num_compartments : int;
  num_exported_funcs : int;
  num_imported_funcs : int;
  num_external_funcs : int;
  num_builtins : int;
  num_runtime_funcs : int;
  num_global_vars : int;
  global_var_max_size : int;
  max_arg_count : int;
  debug : bool;
}

type comp = int
type func = int
type var = int

val random : gen_config -> Random.State.t -> t
val main : t -> func
val function_list : t -> func list
val compartment_list : t -> comp list
val export_list : t -> (comp * func list) list
val import_list : t -> (comp * (comp * func) list) list
val def_list : t -> (func * comp * AST.signature) list

val var_list : t -> (comp * var * AST.init_data list * bool * bool) list

val external_funcs : t -> AST.external_function list
val builtins : t -> AST.external_function list
val runtime_funcs : t -> AST.external_function list

val get_asm_prog : t -> Asm.program
