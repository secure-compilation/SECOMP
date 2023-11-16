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

(* let ef_external =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* name = char_list in
   let* signature = signature in
   return (AST.EF_external (compartment, name, signature)) *)

(* let ef_builtin =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* name = char_list in
   let* signature = signature in
   return (AST.EF_builtin (compartment, name, signature)) *)

(* let ef_runtime =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* name = char_list in
   let* signature = signature in
   return (AST.EF_runtime (compartment, name, signature)) *)

(* let ef_vload =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* memory_chunk = memory_chunk in
   return (AST.EF_vload (compartment, memory_chunk)) *)

(* let ef_vstore =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* memory_chunk = memory_chunk in
   return (AST.EF_vload (compartment, memory_chunk)) *)

(* let ef_malloc = QCheck.Gen.map (fun c -> AST.EF_malloc c) compartment *)
(* let ef_free = QCheck.Gen.map (fun c -> AST.EF_free c) compartment *)

(* let ef_memcpy =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* z1 = coq_Z in
   let* z2 = coq_Z in
   return (AST.EF_memcpy (compartment, z1, z2)) *)

(* let ef_annot =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* p = positive in
   let* text = char_list in
   let* type_list = list_size small_nat typ in
   return (AST.EF_annot (compartment, p, text, type_list)) *)

(* let ef_annot_val =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* p = positive in
   let* text = char_list in
   let* typ = typ in
   return (AST.EF_annot_val (compartment, p, text, typ)) *)

(* let ef_inline_asm =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* text = char_list in
   let* signature = signature in
   let* code = list_size small_nat char_list in
   return (AST.EF_inline_asm (compartment, text, signature, code)) *)

(* let ef_debug =
   let open QCheck.Gen in
   let* compartment = compartment in
   let* p = positive in
   let* ident = ident in
   let* type_list = list_size small_nat typ in
   return (AST.EF_debug (compartment, p, ident, type_list)) *)

(* let external_function =
   QCheck.Gen.frequency
     [
       (1, ef_external);
       (1, ef_builtin);
       (1, ef_runtime);
       (1, ef_vload);
       (1, ef_vstore);
       (1, ef_malloc);
       (1, ef_free);
       (1, ef_memcpy);
       (1, ef_annot);
       (1, ef_annot_val);
       (1, ef_inline_asm);
       (1, ef_debug);
     ] *)

(* let bundle_call =
   let open QCheck.Gen in
   let* trace = trace in
   let* ident = ident in
   let* args = list_size (int_bound 5) eventval in
   let* sign = signature in
   let* mem_delta = mem_delta in
   return (BtInfoAsm.Bundle_call (trace, ident, args, sign, mem_delta)) *)

(* let bundle_return =
   let open QCheck.Gen in
   let* trace = trace in
   let* ret_val = eventval in
   let* mem_delta = mem_delta in
   return (BtInfoAsm.Bundle_return (trace, ret_val, mem_delta)) *)

(* let bundle_builtin =
   let open QCheck.Gen in
   let* trace = trace in
   let* ext_fun = external_function in
   let* args = list_size (int_bound 5) eventval in
   let* mem_delta = mem_delta in
   return (BtInfoAsm.Bundle_builtin (trace, ext_fun, args, mem_delta)) *)

(* let bundle_event =
   QCheck.Gen.frequency
     [ (1, bundle_call); (1, bundle_return); (1, bundle_builtin) ] *)

let bundle_trace _ = QCheck.Gen.return []
(* let open QCheck.Gen in
   list_size small_nat (pair ident bundle_event) *)

let build_prog_defs ctx =
  let gvars = [] in
  let raw_defs = Gen_ctx.def_list ctx in
  let gfuns =
    List.map
      (fun (f, c, s) ->
        let coq_func =
          ({ fn_comp = Camlcoq.P.of_int c; fn_sig = s; fn_code = [] }
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
        List.map (fun (c, f) -> (Camlcoq.P.of_int c, Camlcoq.P.of_int f)) imps
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
        num_compartments = 1;
        num_exported_funcs = 1;
        num_imported_funcs = 1;
        max_arg_count = 1;
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
