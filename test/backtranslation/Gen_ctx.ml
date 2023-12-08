module Map = Map.Make (Int)

type exports = int list Map.t
type imports = (int * int) list Map.t
type func_sigs = AST.signature Map.t

type t = {
  exports : exports;
  imports : imports;
  func_sigs : func_sigs;
  main : int;
}

type gen_config = {
  num_compartments : int;
  num_exported_funcs : int;
  num_imported_funcs : int;
  max_arg_count : int;
  debug : bool;
}

type comp = int
type func = int

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
  let* cc_unproto = map (fun f -> f <= 0.1) (float_range 0.0 1.0) in
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
  let* main, func_sigs = sample_func_sigs config exports in
  if config.debug then (
    Graph.dump graph;
    dump_exports exports;
    dump_imports imports)
  else ();
  return { exports; imports; func_sigs; main }

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
