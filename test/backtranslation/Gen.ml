let memory_chunk =
  QCheck.Gen.frequencyl
    AST.
  [
    (1, Mint8signed);
    (1, Mint8unsigned);
    (1, Mint16signed);
    (1, Mint16unsigned);
    (1, Mint32);
    (1, Mint64);
    (1, Mfloat32);
    (1, Mfloat64);
    (1, Many32);
    (1, Many64);
  ]

(* TODO: move these and others to a common file because they are also needed in Gen_ctx *)
let positive = QCheck.Gen.(map (fun i -> Camlcoq.P.of_int (i + 1)) small_nat)
let coq_Z = QCheck.Gen.(map (fun i -> Camlcoq.Z.of_sint i) small_signed_int)
let ident = positive
let compartment = QCheck.Gen.map (fun p -> AST.COMP.Comp p) positive
let ptrofs = QCheck.Gen.map (fun i -> Integers.Ptrofs.of_int i) coq_Z
let char_list = QCheck.Gen.(small_list (char_range 'a' 'z'))

let binary_float =
  let open QCheck.Gen in
  let open Binary in
  let zero = map (fun b -> B754_zero b) bool in
  let infinity = map (fun b -> B754_infinity b) bool in
  let nan = map (fun (b, p) -> B754_nan (b, p)) (pair bool positive) in
  let finite =
    map (fun (b, p, z) -> B754_finite (b, p, z)) (triple bool positive coq_Z)
  in
  frequency [ (1, zero); (1, infinity); (1, nan); (1, finite) ]

let mem_val ctx =
  let open QCheck.Gen in
  QCheck.Gen.frequency
    Memdata.[
      (1, return Undef);
      (1, map (fun b -> Byte b) coq_Z);
      (* TODO: add support for fragment memory values *)
    ]

let vundef _ = QCheck.Gen.return Values.Vundef

let vint _ = QCheck.Gen.map (fun i -> Values.Vint i) coq_Z

let vlong _ = QCheck.Gen.map (fun i -> Values.Vlong i) coq_Z

let vfloat _ = QCheck.Gen.map (fun f -> Values.Vfloat f) binary_float

let vsingle _ = QCheck.Gen.map (fun f -> Values.Vsingle f) binary_float

let vptr ctx =
  let open QCheck.Gen in
  let glob_vars = List.map (fun (_, v, _, _, _) -> v) (Gen_ctx.var_list ctx) in
  let* ident = map Camlcoq.P.of_int (oneofl glob_vars) in
  let asm_prog = Gen_ctx.get_asm_prog ctx in
  let genv = Globalenvs.Genv.globalenv asm_prog in
  let block = match Globalenvs.Genv.find_symbol genv ident with
    | None -> failwith "Fatal error: cannot find block for symbol for vptr."
    | Some b -> b
  in
  let* ptrofs = ptrofs in
  return (Values.Vptr (block, ptrofs))

let coq_val ctx =
  QCheck.Gen.frequency
    [
      (1, vundef ctx);
      (1, vint ctx);
      (1, vlong ctx);
      (1, vfloat ctx);
      (1, vsingle ctx);
      (1, vptr ctx);
    ]

let mem_delta_storev curr_comp ctx =
  let open QCheck.Gen in
  let* chunk = memory_chunk in
  let glob_vars = List.filter_map (fun (_, v, _, read_only, _) -> if read_only then Option.none else Option.some v) (Gen_ctx.var_list ctx) in
  let* ident = map Camlcoq.P.of_int (oneofl glob_vars) in

  let asm_prog = Gen_ctx.get_asm_prog ctx in
  let genv = Globalenvs.Genv.globalenv asm_prog in
  let block = match Globalenvs.Genv.find_symbol genv ident with
    | None -> failwith "Fatal error: cannot find block for symbol for mem_delta"
    | Some b -> b
  in
  let* offset = ptrofs in
  let addr = Values.Vptr (block, offset) in
  let* value = coq_val ctx in
  let comp = AST.COMP.Comp (Camlcoq.P.of_int curr_comp) in
  return (MemoryDelta.Coq_mem_delta_kind_storev (((chunk, addr), value), comp))

let mem_delta_store curr_comp ctx =
  let open QCheck.Gen in
  let* chunk = memory_chunk in
  let glob_vars = List.filter_map (fun (_, v, _, read_only, _) -> if read_only then Option.none else Option.some v) (Gen_ctx.var_list ctx) in
  let* block = map Camlcoq.P.of_int (oneofl glob_vars) in
  let* offset = ptrofs in
  let* value = coq_val ctx in
  let comp = AST.COMP.Comp (Camlcoq.P.of_int curr_comp) in
  return (MemoryDelta.Coq_mem_delta_kind_store ((((chunk, block), offset), value), comp))

let mem_delta_bytes curr_comp ctx =
  let open QCheck.Gen in
  let* block = positive in
  let* offset = ptrofs in
  let* bytes = small_list (mem_val ctx) in
  let comp = AST.COMP.Comp (Camlcoq.P.of_int curr_comp) in
  return (MemoryDelta.Coq_mem_delta_kind_bytes (((block, offset), bytes), comp))

let mem_delta_alloc curr_comp ctx =
  let open QCheck.Gen in
  let* lower = map Camlcoq.Z.of_uint small_nat in
  let* len = map Camlcoq.Z.of_uint small_nat in
  let comp = AST.COMP.Comp (Camlcoq.P.of_int curr_comp) in
  return (MemoryDelta.Coq_mem_delta_kind_alloc ((comp, lower), Camlcoq.Z.add lower len))

let mem_delta_free curr_comp ctx =
  let open QCheck.Gen in
  let* block = positive in
  let* lower = map Camlcoq.Z.of_uint small_nat in
  let* len = map Camlcoq.Z.of_uint small_nat in
  let comp = AST.COMP.Comp (Camlcoq.P.of_int curr_comp) in
  return (MemoryDelta.Coq_mem_delta_kind_free (((block, lower), Camlcoq.Z.add lower len), comp))

let mem_delta_kind curr_comp ctx =
  QCheck.Gen.frequency
    [
      (* TODO: actually, only storev deltas are considered in BT. Check this and simplify the code *)
      (1, mem_delta_storev curr_comp ctx);
      (*(1, mem_delta_store curr_comp ctx);*)
      (*(1, mem_delta_bytes curr_comp ctx);
      (1, mem_delta_alloc curr_comp ctx);
      (1, mem_delta_free curr_comp ctx);*)
    ]

let mem_delta curr_comp ctx rand_state =
  let mem_delta = QCheck.Gen.small_list (mem_delta_kind curr_comp ctx) rand_state in
  Stats.register_mem_delta mem_delta; mem_delta

let ef_external ctx = QCheck.Gen.oneofl (Gen_ctx.external_funcs ctx)

let ef_builtin ctx = QCheck.Gen.oneofl (Gen_ctx.builtins ctx)

let ef_runtime ctx = QCheck.Gen.oneofl (Gen_ctx.runtime_funcs ctx)

let ef_vload _ =
  let open QCheck.Gen in
  (* TODO: are there any requirement we must meet? *)
  let* memory_chunk = memory_chunk in
  return (AST.EF_vload (memory_chunk))

let ef_vstore _ =
  let open QCheck.Gen in
  (* TODO: are there any requirements we must meet? *)
  let* memory_chunk = memory_chunk in
  return (AST.EF_vstore (memory_chunk))

let ef_malloc _ = QCheck.Gen.return AST.EF_malloc
let ef_free _ = QCheck.Gen.return AST.EF_free

let ef_memcpy _ =
  let open QCheck.Gen in
  (* TODO: are there any requirements we must meet? *)
  let* z1 = coq_Z in
  let* z2 = coq_Z in
  return (AST.EF_memcpy (z1, z2))

let ef_annot _ = failwith "ef_annot is not implemented"

let ef_annot_val _ = failwith "ef_annot_val is not implemented"

let ef_inline_asm _ = failwith "ef_inline_asm is not implemented"

let ef_debug _ = failwith "ef_debug is not implemented"

let external_function ctx =
  QCheck.Gen.frequency
    [
      (1, ef_external ctx);
      (1, ef_builtin ctx);
      (1, ef_runtime ctx);
      (* TODO: perhaps enable these if they are required
      (1000, ef_vload ctx);
      (1, ef_vstore ctx);
      (1, ef_malloc ctx);
      (1, ef_free ctx);
      (1, ef_memcpy ctx);
      (0, ef_annot ctx);
      (0, ef_annot_val ctx);
      (0, ef_inline_asm ctx);
      (0, ef_debug ctx);
       *)
    ]

(* TODO: perhaps differentiate between signed/unsigned and positive/negative values? *)
let ev_int = QCheck.Gen.map (fun i -> Events.EVint i) coq_Z
let ev_float = QCheck.Gen.map (fun f -> Events.EVfloat f) binary_float
let ev_long = QCheck.Gen.map (fun l -> Events.EVlong l) coq_Z
let ev_single = QCheck.Gen.map (fun f -> Events.EVfloat f) binary_float

let value_of_typ t =
  let open QCheck.Gen in
  let open AST in
  match t with
  | Tint -> ev_int
  | Tfloat -> ev_float
  | Tlong -> ev_long
  | Tsingle -> ev_single
  (* TODO: are ev_int and ev_long the correct values for these *)
  | Tany32 -> ev_int
  | Tany64 -> ev_long

let args_for_sig sign rand_state =
  List.map (fun t -> value_of_typ t rand_state) sign.AST.sig_args

let ret_val_for_sig sign =
  let open AST in
  (* TODO: implement me properly *)
  match sign.sig_res with
  | Tint8signed -> ev_int
  | Tint8unsigned -> ev_int
  | Tint16signed -> ev_int
  | Tint16unsigned -> ev_int
  (* TODO: what is actually a valid value of type void? *)
  | Tvoid -> ev_int
  | Tret t -> value_of_typ t

let bundle_call_ret ctx curr_comp rand_state =
  let open QCheck.Gen in
  let pool = ctx
             |> Gen_ctx.import_list
             |> List.assoc curr_comp in
  match pool with
  | [] -> Option.none (* there is no imported function we could possibly call *)
  | _ ->
     let trgt_comp, trgt_func = oneofl pool rand_state in
     let sign = (match
                   (List.find_map
                      (fun (f, c, s) ->
                        if f = trgt_func && c = trgt_comp then Option.some s else Option.none)
                      (Gen_ctx.def_list ctx)) with
                 | Option.None -> failwith "Cannot lookup signature for imported function"
                 | Option.Some s -> s) in
     let args = args_for_sig sign rand_state in
     let ret_val = ret_val_for_sig sign rand_state in
     let subtrace_call = [] in
     let subtrace_ret = [] in
     let mdelta_call = mem_delta curr_comp ctx rand_state in
     let mdelta_ret = mem_delta trgt_comp ctx rand_state in
     let call = BtInfoAsm.Bundle_call (subtrace_call, Camlcoq.P.of_int trgt_func, args, sign, mdelta_call) in
     let ret = BtInfoAsm.Bundle_return (subtrace_ret, ret_val, mdelta_ret) in
     Option.some (call, ret, trgt_comp)

let bundle_builtin ctx rand_state =
  let open QCheck.Gen in
  let subtrace = [] in
  let func = external_function ctx rand_state in
  let () = Stats.register_external_function func in
  let sign = AST.ef_sig func in
  let args = args_for_sig sign rand_state in
  let mdelta = [] in
  BtInfoAsm.Bundle_builtin (subtrace, func, args, mdelta)

let bundle_trace ctx rand_state =
  let open QCheck.Gen in
  let size = int_range 0 ((Gen_ctx.get_config ctx).max_trace_len / 2) rand_state in
  let rec bundle_trace_aux curr_comp = function
    | 0 -> []
    | n -> (
      let f = float_range 0.0 1.0 rand_state in
      match f with
      (* TODO: also generate builtin events in the trace (for now the test fails) *)
      | _ when f <= 0.7 -> (
        match bundle_call_ret ctx curr_comp rand_state with
        | Option.None -> []
        | Option.Some (call, ret, trgt_comp) ->
           let between = bundle_trace_aux trgt_comp (n-1) in
           List.concat [[call]; between; [ret]])
      | _ ->
         let b = bundle_builtin ctx rand_state in
         b :: bundle_trace_aux curr_comp (n-1)
    )
  in
  let main_comp = 1 in (* TODO: get the compartment of the main function *)
  List.mapi (fun i be -> (Camlcoq.P.of_int (i+1), be)) (bundle_trace_aux main_comp size)
