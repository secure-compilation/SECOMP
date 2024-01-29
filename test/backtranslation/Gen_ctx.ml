module Map = Map.Make (Int)

type exports = int list Map.t
type imports = (int * int) list Map.t
type func_sigs = AST.signature Map.t
type extern = AST.external_function

type gen_config = {
  num_compartments : int;
  num_exported_funcs : int;
  num_imported_funcs : int;
  num_external_funcs : int;
  num_builtins : int;
  num_runtime_funcs: int;
  num_global_vars : int;
  global_var_max_size : int;
  max_arg_count : int;
  debug : bool;
  max_trace_len : int;
}

type t = {
  exports : exports;
  imports : imports;
  func_sigs : func_sigs;
  main : int;
  glob_vars : (int * AST.init_data list * bool * bool) list Map.t;
  external_funcs : extern list;
  builtins: extern list;
  runtime_funcs : extern list;
  config : gen_config;
}

type comp = int
type func = int
type var = int

let sample_typ =
  QCheck.Gen.frequencyl
    AST.
      [
        (1, Tint);
        (1, Tfloat);
        (1, Tlong);
        (1, Tsingle);
        (1, Tany32);
        (1, Tany64);
      ]

let sample_rettype =
  let open QCheck.Gen in
  let* f = float_range 0.0 1.0 in
  if f < 1.0 /. 6.0 then map (fun t -> AST.Tret t) sample_typ
  else
    frequencyl
      AST.
        [
          (1, Tint8signed);
          (1, Tint8unsigned);
          (1, Tint16signed);
          (1, Tint16unsigned);
          (1, Tvoid);
        ]

let sample_calling_convention allow_vararg =
  let open QCheck.Gen in
  let* cc_vararg =
    if allow_vararg
    then option ~ratio:0.1 (map Camlcoq.Z.of_uint small_nat)
    else return Option.none in
  (* TODO: what exactly is unproto and do we care for this testing? *)
  let* cc_unproto = return false in (*map (fun f -> f <= 0.1) (float_range 0.0 1.0) in*)
  let* cc_structret = map (fun f -> f <= 0.1) (float_range 0.0 1.0) in
  return ({ cc_vararg; cc_unproto; cc_structret } : AST.calling_convention)

let sample_signature config =
  let open QCheck.Gen in
  let* arg_types = list_size (int_bound config.max_arg_count) sample_typ in
  let* ret_type = sample_rettype in
  let* cc = sample_calling_convention (List.length arg_types > 0) in
  return AST.{ sig_args = arg_types; sig_res = ret_type; sig_cc = cc }

let sample_exports config graph =
  let open QCheck.Gen in
  let compartments = Graph.vertices graph in
  let n = Graph.size graph in
  let pool = List.init (n * config.num_exported_funcs) succ in
  let* funcs = Util.choose_disjoint n config.num_exported_funcs pool in
  return (Map.of_seq (List.to_seq (List.combine compartments funcs)))

let sample_init_data config =
  (* TODO: currently only ints are supported as init data in PrintAsm.ml.
     Once this is fixed, the code below can be extended to also generate
     the missing types of init data. *)
  let open QCheck.Gen in
  let int8 = map (fun i -> AST.Init_int8 (Camlcoq.Z.of_sint i)) small_int in
  let int16 = map (fun i -> AST.Init_int16 (Camlcoq.Z.of_sint i)) small_int in
  let int32 = map (fun i -> AST.Init_int32 (Camlcoq.Z.of_sint i)) small_int in
  let int64 = map (fun i -> AST.Init_int64 (Camlcoq.Z.of_sint i)) small_int in
  QCheck.Gen.frequency
  [
    (1, int8);
    (1, int16);
    (1, int32);
    (1, int64);
  ]

let sample_init_data_list config =
  QCheck.Gen.(list_size (int_bound config.global_var_max_size) (sample_init_data config))

let sample_global_vars config graph exports rand_state =
  let open QCheck.Gen in
  let compartments = Graph.vertices graph in
  let n = Graph.size graph in
  let all_funcs = List.concat_map snd (Map.bindings exports) in
  let max_func_ident = List.fold_left Int.max 0 all_funcs in
  let pool = List.init (n * config.num_global_vars) (fun i -> i + 1 + max_func_ident) in
  let read_only = (map (fun f -> f <= 0.3) (float_range 0.0 1.0)) in
  let volatile = (map (fun f -> f <= 0.3) (float_range 0.0 1.0)) in
  let pool_with_init_data = List.map (fun g -> (g, sample_init_data_list config rand_state, read_only rand_state, volatile rand_state)) pool in
  let glob_vars = Util.choose_disjoint n config.num_global_vars pool_with_init_data rand_state in
  Map.of_seq (List.to_seq (List.combine compartments glob_vars))

let sample_imports graph exports rand_state =
  let open QCheck.Gen in
  let distribute (x, ys) = List.map (fun y -> (x, y)) ys in
  let compartments = Graph.vertices graph in
  let imports self =
    compartments
    |> List.filter (fun other -> Graph.is_adjacent self other graph)
    (* int list *)
    |> List.map (fun other -> (other, Map.find other exports))
    (* (int * int list) list*)
    |> List.map (fun (other, funcs) -> (other, Util.sublist funcs rand_state))
    (* (int * int list) list *)
    |> List.concat_map distribute
    (* (int * int) list *)
  in
  Map.of_seq (List.to_seq (List.map (fun c -> (c, imports c)) compartments))

let sample_func_sigs config exports =
  let open QCheck.Gen in
  let compartments = List.map fst (Map.bindings exports) in
  let* main_comp = oneofl compartments in
  let* main = oneofl (Map.find main_comp exports) in
  let all_funcs = List.concat_map snd (Map.bindings exports) in
  let num_funcs = List.length all_funcs in
  let* sigs = list_repeat num_funcs (sample_signature config) in
  let sig_map = Map.of_seq (List.to_seq (List.combine all_funcs sigs)) in
  let main_sig =
    AST.{ sig_args = []; sig_res = Tret Tint; sig_cc = cc_default }
  in
  return (main, Map.add main main_sig sig_map)

let sample_external_funcs config =
  let open QCheck.Gen in
  let gen =
    let* name = list_size (map Int.succ small_nat) (char_range 'a' 'z') in
    let* suffix = list_size (return 4) (char_range '0' '9') in
    let unique_name = name @ ['_'] @ suffix in
    let* sign = sample_signature config in
    return (AST.EF_external (unique_name, sign)) in
  list_repeat config.num_external_funcs gen

let sample_builtins config =
  let open QCheck.Gen in
  let gen =
    let* name = list_size (map Int.succ small_nat) (char_range 'a' 'z') in
    let* sign = sample_signature config in
    return (AST.EF_builtin (name, sign)) in
  list_repeat config.num_builtins gen

let sample_runtime_funcs config =
  let open QCheck.Gen in
  let gen =
    let* name = list_size (map Int.succ small_nat) (char_range 'a' 'z') in
    let* sign = sample_signature config in
    return (AST.EF_runtime (name, sign)) in
  list_repeat config.num_runtime_funcs gen

let dump_exports exports =
  print_endline "Exports:";
  Map.iter
    (fun comp funcs ->
      Printf.printf "%d -> [%s]\n" comp
        (String.concat ", " (List.map string_of_int funcs)))
    exports

let dump_imports imports =
  let fmt = Printf.sprintf in
  print_endline "Imports:";
  Map.iter
    (fun self imps ->
      Printf.printf "%d <- [%s]\n" self
        (String.concat ", " (List.map (fun (c, f) -> fmt "%d.%d" c f) imps)))
    imports

let random config =
  let open QCheck.Gen in
  let* graph = Graph.random config.num_compartments in
  let* exports = sample_exports config graph in
  let* imports = sample_imports graph exports in
  let* external_funcs = sample_external_funcs config in
  let* builtins = sample_builtins config in
  let* runtime_funcs = sample_runtime_funcs config in
  let* main, func_sigs = sample_func_sigs config exports in
  let* glob_vars = sample_global_vars config graph exports in
  if config.debug then (
    Graph.dump graph;
    dump_exports exports;
    dump_imports imports)
  else ();
  return { exports; imports; func_sigs; main; glob_vars; external_funcs; builtins; runtime_funcs; config }

let main ctx = ctx.main
let function_list ctx = List.concat_map snd (Map.bindings ctx.exports)
let compartment_list ctx = List.map fst (Map.bindings ctx.imports)
let export_list ctx = Map.bindings ctx.exports
let import_list ctx = Map.bindings ctx.imports

let def_list ctx =
  let sig_of f = Map.find f ctx.func_sigs in
  List.concat_map
    (fun (c, fs) -> List.map (fun f -> (f, c, sig_of f)) fs)
    (export_list ctx)

let var_list ctx =
  List.concat_map
    (fun (comp, vars) -> List.map
      (fun (id, init_datas, read_only, volatile) -> (comp, id, init_datas, read_only, volatile))
      vars)
    (Map.bindings ctx.glob_vars)

let external_funcs ctx = ctx.external_funcs
let builtins ctx = ctx.builtins
let runtime_funcs ctx = ctx.runtime_funcs

let build_prog_defs ctx =
  let raw_gvars = var_list ctx in
  let gvars =
    List.map
      (fun (c, v, init, read_only, volatile) ->
        let globvar = AST.{
          gvar_info = ();
          gvar_comp = AST.COMP.Comp (Camlcoq.P.of_int c);
          gvar_init = init;
          gvar_readonly = read_only;
          gvar_volatile = volatile;
        }
        in
        (Camlcoq.P.of_int v, AST.Gvar globvar)
      )
      raw_gvars
  in
  let raw_defs = def_list ctx in
  let gfuns =
    List.map
      (fun (f, c, s) ->
        let coq_func =
          ({ fn_comp = AST.COMP.Comp (Camlcoq.P.of_int c); fn_sig = s; fn_code = [] }
            : Asm.coq_function)
        in
        let fundef = AST.Internal coq_func in
        (Camlcoq.P.of_int f, AST.Gfun fundef))
      raw_defs
  in
  gvars @ gfuns

let build_prog_public ctx =
  List.map Camlcoq.P.of_int (function_list ctx) @
  List.map (fun (_, v, _, _, _) -> Camlcoq.P.of_int v) (var_list ctx)

let build_prog_main ctx = Camlcoq.P.of_int (main ctx)

let build_prog_pol ctx =
  let open Maps in
  let policy_export = ref PTree.empty in
  let exports = export_list ctx in
  List.iter
    (fun (raw_comp, raw_funcs) ->
      let funcs = List.map Camlcoq.P.of_int raw_funcs in
      let comp = Camlcoq.P.of_int raw_comp in
      policy_export := PTree.set comp funcs !policy_export)
    exports;
  let policy_import = ref PTree.empty in
  let imports = import_list ctx in
  List.iter
    (fun (comp, imps) ->
      let imps =
        List.map (fun (c, f) -> (AST.COMP.Comp (Camlcoq.P.of_int c), Camlcoq.P.of_int f)) imps
      in
      let comp = Camlcoq.P.of_int comp in
      if imps <> [] then policy_import := PTree.set comp imps !policy_import
      else ())
    imports;
  let policy =
    ({ policy_comps = PTree.empty; policy_export = !policy_export; policy_import = !policy_import }
      : AST.Policy.t)
  in
  policy

let get_asm_prog ctx =
  let prog_defs = build_prog_defs ctx in
  let prog_public = build_prog_public ctx in
  let prog_main = build_prog_main ctx in
  let prog_pol = build_prog_pol ctx in
  AST.{ prog_defs; prog_public; prog_main; prog_pol }

let get_config ctx = ctx.config
