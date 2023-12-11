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

let positive = QCheck.Gen.(map (fun i -> Camlcoq.P.of_int (i + 1)) small_nat)
let coq_Z = QCheck.Gen.(map (fun i -> Camlcoq.Z.of_sint i) small_signed_int)
let ident = positive
let compartment = positive
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

(*
let eventval =
  let open QCheck.Gen in
  let open Events in
  let evint = map (fun i -> EVint i) coq_Z in
  let evlong = map (fun i -> EVlong i) coq_Z in
  let evfloat = map (fun f -> EVfloat f) binary_float in
  let evsingle = map (fun f -> EVfloat f) binary_float in
  let evptr_global =
    map (fun (i, p) -> EVptr_global (i, p)) (pair ident ptrofs)
  in
  frequency
    [ (1, evint); (1, evlong); (1, evfloat); (1, evsingle); (1, evptr_global) ]

let event_syscall size =
  let open QCheck.Gen in
  let* name = char_list in
  let* args = list_size size eventval in
  let* ret_val = eventval in
  return (Events.Event_syscall (name, args, ret_val))

let event_vload =
  let open QCheck.Gen in
  let* mem_chunk = memory_chunk in
  let* ident = ident in
  let* ptr = ptrofs in
  let* value = eventval in
  return (Events.Event_vload (mem_chunk, ident, ptr, value))

let event_vstore =
  let open QCheck.Gen in
  let* mem_chunk = memory_chunk in
  let* ident = ident in
  let* ptr = ptrofs in
  let* value = eventval in
  return (Events.Event_vstore (mem_chunk, ident, ptr, value))

let event_annot size =
  let open QCheck.Gen in
  let* name = char_list in
  let* values = list_size size eventval in
  return (Events.Event_annot (name, values))

let event_call src_compartment trgt_compartment size =
  let open QCheck.Gen in
  let* ident = ident in
  let* args = list_size size eventval in
  return (Events.Event_call (src_compartment, trgt_compartment, ident, args))

let event_return src_compartment trgt_compartment =
  let open QCheck.Gen in
  let* ret_val = eventval in
  return (Events.Event_return (src_compartment, trgt_compartment, ret_val))

(* TODO: also generate other mem_deltas *)
let mem_delta = QCheck.Gen.return []

(* QCheck generator for an event trace *)

let trace rand_state =
  let open QCheck.Gen in
  (* ensure that no empty traces are generated *)
  let size = small_nat rand_state + 1 in
  let rec gen_trace_aux = function
    | 0 -> []
    | n -> (
        let f = float_range 0.0 1.0 rand_state in
        match f with
        | _ when f < 0.6 ->
            let n1, n2 = nat_split2 (n - 1) rand_state in
            let src_compartment = compartment rand_state in
            let trgt_compartment = compartment rand_state in
            let arg_count = int_bound 5 in
            let call =
              [
                event_call src_compartment trgt_compartment arg_count rand_state;
              ]
            in
            let between = gen_trace_aux n1 in
            let ret =
              [ event_return src_compartment trgt_compartment rand_state ]
            in
            let after = gen_trace_aux n2 in
            List.concat [ call; between; ret; after ]
        | _ when f < 0.7 ->
            let arg_count = int_bound 5 in
            event_syscall arg_count rand_state :: gen_trace_aux (n - 1)
        | _ when f < 0.8 -> event_vload rand_state :: gen_trace_aux (n - 1)
        | _ when f < 0.9 -> event_vstore rand_state :: gen_trace_aux (n - 1)
        | _ ->
            let size = int_bound 5 in
            event_annot size rand_state :: gen_trace_aux (n - 1))
  in
  gen_trace_aux size

*)

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
      (1, ef_vload ctx);
      (1, ef_vstore ctx);
      (1, ef_malloc ctx);
      (1, ef_free ctx);
      (1, ef_memcpy ctx);
      (* TODO: enable these after the corresponding functions are implemented *)
      (* (0, ef_annot ctx);
      (0, ef_annot_val ctx);
      (0, ef_inline_asm ctx);
      (0, ef_debug ctx);*)
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
     let mdelta_call = [] in
     let mdelta_ret = [] in
     let call = BtInfoAsm.Bundle_call (subtrace_call, Camlcoq.P.of_int trgt_func, args, sign, mdelta_call) in
     let ret = BtInfoAsm.Bundle_return (subtrace_ret, ret_val, mdelta_ret) in
     Option.some (call, ret, trgt_comp)

let bundle_builtin ctx rand_state =
  let open QCheck.Gen in
  let subtrace = [] in
  let func = external_function ctx rand_state in
  let sign = AST.ef_sig func in
  let args = args_for_sig sign rand_state in
  let mdelta = [] in
  BtInfoAsm.Bundle_builtin (subtrace, func, args, mdelta)

let bundle_trace ctx rand_state =
  let open QCheck.Gen in
  let size = small_nat rand_state in
  let rec bundle_trace_aux curr_comp = function
    | 0 -> []
    | n -> (
      let f = float_range 0.0 1.0 rand_state in
      match f with
      | _ when f < 0.8 -> (
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

let build_prog_defs ctx =
  let gvars = [] in
  let raw_defs = Gen_ctx.def_list ctx in
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
  List.map Camlcoq.P.of_int (Gen_ctx.function_list ctx)

let build_prog_main ctx = Camlcoq.P.of_int (Gen_ctx.main ctx)

let build_prog_pol ctx =
  let open Maps in
  let policy_export = ref PTree.empty in
  let exports = Gen_ctx.export_list ctx in
  List.iter
    (fun (raw_comp, raw_funcs) ->
      let funcs = List.map Camlcoq.P.of_int raw_funcs in
      let comp = Camlcoq.P.of_int raw_comp in
      policy_export := PTree.set comp funcs !policy_export)
    exports;
  let policy_import = ref PTree.empty in
  let imports = Gen_ctx.import_list ctx in
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
    ({ policy_export = !policy_export; policy_import = !policy_import }
      : AST.Policy.t)
  in
  policy

let asm_program =
  let open QCheck.Gen in
  let config =
    Gen_ctx.
      {
        num_compartments = 3;
        num_exported_funcs = 5;
        num_imported_funcs = 3;
        num_external_funcs = 4;
        num_builtins = 4;
        num_runtime_funcs = 4;
        max_arg_count = 2;
        debug = true;
      }
  in
  let* ctx = Gen_ctx.random config in
  let prog_defs = build_prog_defs ctx in
  let prog_public = build_prog_public ctx in
  let prog_main = build_prog_main ctx in
  let prog_pol = build_prog_pol ctx in
  let asm_prog =
    ({ prog_defs; prog_public; prog_main; prog_pol } : Asm.program)
  in
  return (asm_prog, ctx)
