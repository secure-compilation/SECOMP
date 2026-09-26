(* Regression test for the back-translation: its output must be accepted by
   the compiler, which is what Assumption 1 requires of the back-translation
   ([backtranslation_compiles] in security/RSC.v).  See issue #13.

   Each check back-translates an Asm program and an informative trace with
   [Backtranslation.gen_program] and compiles the resulting Clight program
   itself with [Compiler.transf_clight_program].  test_backtranslation
   instead prints the generated program as C, patches the text and
   recompiles it with ccomp, whose C front end re-derives the declared types,
   and the Asm programs it generates declare no external functions and have
   no void results.  Together, this hid issue #13.

   There are four groups of checks:

   - declarations: external functions with pointer, void and small-integer
     types, with the empty trace;
   - stores: retained stores of every chunk and kind of value.  Each must
     compile, and must be replayed if and only if the well-formedness
     relation on informative traces applies it: the store is to a public
     symbol, by the current compartment, and its value matches its chunk.
     This includes stores by the bottom and top compartments, which a
     flows-to test in either direction would accept, and stores in the
     return event of another compartment's function;
   - builtins: volatile loads and stores, annotations, and an external
     function called as a builtin, once after retained stores;
   - programs: the compartmentalized C programs in ../compartments and
     ./programs, each with the empty trace and with a synthetic trace in which
     main calls every function.  For the synthetic trace we also check that
     every call site has the type of its callee's declaration, as Clight's
     call rule requires.  Compilation does not check this.

   Besides compiling the generated code, the test only counts its replayed
   stores, builtins and call sites, and checks the call-site types.  It does
   not check what the generated code computes.

   Build and run it from this directory after building CompCert, as described
   in README.md.  The C programs are preprocessed as ccomp does, with the
   configuration file named by COMPCERT_CONFIG, which [make run_test_compiles]
   sets to ../../compcert.ini.  The test exits with status 1 if a check fails,
   and with status 2 if COMPCERT_CONFIG is not set or no C programs are
   found. *)

open Camlcoq

(* Checks and reporting *)

let total = ref 0
let failed = ref 0

(* Run the checks of one group, printing each failure and a summary. *)
let group name (checks: (string * (unit -> (unit, string) result)) list) =
  let passed = List.fold_left (fun passed (what, check) ->
    let result =
      try check () with e -> Error ("exception " ^ Printexc.to_string e) in
    match result with
    | Ok () -> passed + 1
    | Error msg -> Printf.printf "FAIL %s: %s: %s\n%!" name what msg; passed)
    0 checks in
  let n = List.length checks in
  total := !total + n;
  failed := !failed + (n - passed);
  Printf.printf "%s: %d of %d checks passed\n%!" name passed n

let ( let* ) = Result.bind

(* Error messages are printed as ccomp prints them. *)
let string_of_errmsg m = Format.asprintf "%a" Driveraux.print_error m

(* The register allocator is an OCaml oracle that can also raise an
   exception, which [group] reports. *)
let compile (cl: Clight.program) =
  match Compiler.transf_clight_program cl with
  | Errors.OK _ -> Ok ()
  | Errors.Error m -> Error (string_of_errmsg m)

(* Inspecting the generated code *)

let rec fold_stmt f acc s =
  let acc = f acc s in
  match s with
  | Clight.Ssequence (a, b) | Clight.Sloop (a, b) | Clight.Sifthenelse (_, a, b) ->
      fold_stmt f (fold_stmt f acc a) b
  | Clight.Slabel (_, s) -> fold_stmt f acc s
  | Clight.Sswitch (_, ls) -> fold_labeled f acc ls
  | _ -> acc
and fold_labeled f acc = function
  | Clight.LSnil -> acc
  | Clight.LScons (_, s, rest) -> fold_labeled f (fold_stmt f acc s) rest

(* Fold [f] over the statements of the internal functions accepted by
   [only]. *)
let fold_code ?(only = fun _ -> true) f acc (cl: Clight.program) =
  List.fold_left (fun acc (id, gd) -> match gd with
    | AST.Gfun (Ctypes.Internal fn) when only id -> fold_stmt f acc fn.Clight.fn_body
    | _ -> acc) acc cl.Ctypes.prog_defs

let count ?only p cl = fold_code ?only (fun n s -> if p s then n + 1 else n) 0 cl

(* Stores through a pointer are the replayed stores. *)
let is_store = function Clight.Sassign (Clight.Ederef _, _) -> true | _ -> false
let is_builtin = function Clight.Sbuiltin _ -> true | _ -> false

let expect_count what p ?only expected cl =
  let n = count ?only p cl in
  if n = expected then Ok ()
  else Error (Printf.sprintf "%d %s in the generated code instead of %d" n what expected)

(* Building Asm programs *)

let sg args res =
  { AST.sig_args = args; AST.sig_res = res; AST.sig_cc = AST.cc_default }
let external_fun name s = AST.Gfun (AST.External (AST.EF_external (name, s)))
let runtime_fun name s = AST.Gfun (AST.External (AST.EF_runtime (name, s)))

(* The runtime helpers that the C front end declares in every program, and
   that instruction selection requires. *)
let helpers =
  let f_l = sg [AST.Xfloat] AST.Xlong and l_f = sg [AST.Xlong] AST.Xfloat
  and l_s = sg [AST.Xlong] AST.Xsingle
  and ll_l = sg [AST.Xlong; AST.Xlong] AST.Xlong
  and li_l = sg [AST.Xlong; AST.Xint] AST.Xlong in
  List.map (fun (name, s) -> (intern_string name, runtime_fun name s))
    [ "__compcert_i64_dtos", f_l; "__compcert_i64_dtou", f_l;
      "__compcert_i64_stod", l_f; "__compcert_i64_utod", l_f;
      "__compcert_i64_stof", l_s; "__compcert_i64_utof", l_s;
      "__compcert_i64_sdiv", ll_l; "__compcert_i64_udiv", ll_l;
      "__compcert_i64_smod", ll_l; "__compcert_i64_umod", ll_l;
      "__compcert_i64_shl", li_l; "__compcert_i64_shr", li_l;
      "__compcert_i64_sar", li_l; "__compcert_i64_umulh", ll_l;
      "__compcert_i64_smulh", ll_l ]

let empty_policy =
  { AST.Policy.policy_comps = Maps.PTree.empty;
    policy_export = Maps.PTree.empty;
    policy_import = Maps.PTree.empty;
    policy_syscalls = Maps.PTree.empty }

let comp1 = AST.COMP.Comp (P.of_int 1) and comp2 = AST.COMP.Comp (P.of_int 2)
let internal_fun comp s =
  AST.Gfun (AST.Internal { Asm.fn_comp = comp; Asm.fn_sig = s; Asm.fn_code = [] })
let main_id = intern_string "main"
let main_sig = sg [] AST.Xint

(* A program made of [main], of compartment [comp1], the given definitions
   and the runtime helpers. *)
let program defs public : Asm.program =
  { AST.prog_defs = ((main_id, internal_fun comp1 main_sig) :: defs) @ helpers;
    AST.prog_public = main_id :: public;
    AST.prog_main = main_id;
    AST.prog_pol = empty_policy }

(* A global variable of 16 bytes of the given compartment *)
let variable comp =
  AST.Gvar { AST.gvar_info = (); AST.gvar_comp = comp;
             AST.gvar_init = [AST.Init_space (Z.of_sint 16)];
             AST.gvar_readonly = false; AST.gvar_volatile = false }

(* Addresses [&id + offset], with a nonzero offset.  The test checks only
   that the generated address arithmetic compiles, not that it computes
   the right address. *)
let offset = Integers.Ptrofs.repr (Z.of_sint 8)
let address prog id =
  let ge = Globalenvs.Genv.globalenv (fun _ -> AST.COMP.Coq_bottom') prog in
  match Globalenvs.Genv.find_symbol ge id with
  | Some b -> Values.Vptr (b, offset)
  | None -> failwith ("no block for " ^ extern_atom id)

(* A retained store, given by its chunk, address, value and compartment *)
let store (ch, ptr, v, cp) =
  MemoryDelta.Coq_mem_delta_kind_storev (((ch, ptr), v), cp)

let one_float = Floats.Float.of_int (Integers.Int.repr (Z.of_sint 1))
let one_single = Floats.Float32.of_int (Integers.Int.repr (Z.of_sint 1))

(* Declarations *)

let declaration_checks =
  List.map (fun (what, (id, def)) ->
    (what, fun () ->
      compile (Backtranslation.gen_program [] (program [ (id, def) ] [ id ]))))
  [ "free: a pointer parameter and a void result",
      (intern_string "free", AST.Gfun (AST.External AST.EF_free));
    "fgets: pointer and int parameters and a pointer result",
      (intern_string "fgets",
       external_fun "fgets" (sg [AST.Xptr; AST.Xint; AST.Xptr] AST.Xptr));
    "__compcert_va_int32: a pointer parameter",
      (intern_string "__compcert_va_int32",
       runtime_fun "__compcert_va_int32" (sg [AST.Xptr] AST.Xint));
    "h: a signed char result",
      (intern_string "h", external_fun "h" (sg [] AST.Xint8signed));
    "k: signed char, unsigned short and _Bool parameters",
      (intern_string "k", external_fun "k"
         (sg [AST.Xint8signed; AST.Xint16unsigned; AST.Xbool] AST.Xint));
    "m: unsigned char and short parameters and an unsigned char result",
      (intern_string "m", external_fun "m"
         (sg [AST.Xint8unsigned; AST.Xint16signed] AST.Xint8unsigned)) ]
  @ [ "runtime helpers only", fun () ->
        compile (Backtranslation.gen_program [] (program [] [])) ]

(* Stores *)

(* [main] calls the external [sys] once, after retained stores.  The global
   variables [buf] and [priv] belong to [main]'s compartment, and only [buf]
   is public. *)
let buf_id = intern_string "buf" and priv_id = intern_string "priv"
let sys_id = intern_string "sys"
let sys_sig = sg [] AST.Xint
let store_program =
  program
    [ buf_id, variable comp1; priv_id, variable comp1;
      sys_id, external_fun "sys" sys_sig ]
    [ buf_id; sys_id ]
let buf_ptr = address store_program buf_id
let priv_ptr = address store_program priv_id

let check_stores stores expected () =
  let tr = [ main_id, BtInfoAsm.Bundle_call ([], sys_id, [], sys_sig, List.map store stores) ] in
  let cl = Backtranslation.gen_program tr store_program in
  let* () = compile cl in
  expect_count "replayed stores" is_store expected cl

let chunks = AST.[
  "Mint8signed", Mint8signed; "Mint8unsigned", Mint8unsigned;
  "Mint16signed", Mint16signed; "Mint16unsigned", Mint16unsigned;
  "Mint32", Mint32; "Mint64", Mint64; "Mfloat32", Mfloat32;
  "Mfloat64", Mfloat64; "Mbool", Mbool; "Many32", Many32; "Many64", Many64 ]
let values = [
  "Vint 1", Values.Vint (Z.of_sint 1); "Vlong 1", Values.Vlong (Z.of_sint 1);
  "Vfloat 1.0", Values.Vfloat one_float; "Vsingle 1.0", Values.Vsingle one_single;
  "Vptr buf", buf_ptr; "Vundef", Values.Vundef ]

(* The chunk/value check of the well-formedness relation, written out
   independently of wf_chunk_val_b in security/MemoryDelta.v. *)
let well_formed ch v = match v, ch with
  | Values.Vint _, (AST.Mbool | AST.Mint8signed | AST.Mint8unsigned
                   | AST.Mint16signed | AST.Mint16unsigned | AST.Mint32) -> true
  | Values.Vlong _, AST.Mint64 -> true
  | Values.Vfloat _, AST.Mfloat64 -> true
  | Values.Vsingle _, AST.Mfloat32 -> true
  | _ -> false

(* [main] calls [f], a function of compartment [comp2] with its own public
   buffer [fbuf].  [f] returns after one retained store to [fbuf] by
   compartment [cp], which is replayed in [f] if [cp] is [f]'s compartment,
   and not replayed otherwise. *)
let f_id = intern_string "f" and fbuf_id = intern_string "fbuf"
let f_sig = sg [] AST.Xint
let callee_program =
  program [ f_id, internal_fun comp2 f_sig; fbuf_id, variable comp2 ] [ f_id; fbuf_id ]
let check_return_store cp expected () =
  let fbuf_ptr = address callee_program fbuf_id in
  let tr = [ main_id, BtInfoAsm.Bundle_call ([], f_id, [], f_sig, []);
             f_id, BtInfoAsm.Bundle_return ([], Events.EVint (Z.of_sint 0),
                     [ store (AST.Mint32, fbuf_ptr, Values.Vint (Z.of_sint 1), cp) ]) ] in
  let cl = Backtranslation.gen_program tr callee_program in
  let* () = compile cl in
  let* () = expect_count "replayed stores" is_store expected cl in
  expect_count "replayed stores in f" is_store ~only:(fun id -> id = f_id) expected cl

let store_checks =
  let one = Values.Vint (Z.of_sint 1) in
  List.concat_map (fun (cn, ch) -> List.map (fun (vn, v) ->
    (cn ^ " " ^ vn,
     check_stores [ (ch, buf_ptr, v, comp1) ] (if well_formed ch v then 1 else 0)))
    values) chunks
  @ [ "Mint32 Vint 1 by another compartment",
      check_stores [ (AST.Mint32, buf_ptr, one, comp2) ] 0;
      (* bottom flows to every compartment and every compartment flows to
         top, so a flows-to test in either direction would replay one of
         these two stores *)
      "Mint32 Vint 1 by the bottom compartment",
      check_stores [ (AST.Mint32, buf_ptr, one, AST.COMP.Coq_bottom') ] 0;
      "Mint32 Vint 1 by the top compartment",
      check_stores [ (AST.Mint32, buf_ptr, one, AST.COMP.Coq_top') ] 0;
      "Mint32 Vint 1 to a global variable that is not public",
      check_stores [ (AST.Mint32, priv_ptr, one, comp1) ] 0;
      (* all retained stores of an event are replayed, not only the first *)
      "100 stores of Mint64 Vlong",
      check_stores (List.init 100 (fun k ->
        (AST.Mint64, buf_ptr, Values.Vlong (Z.of_sint k), comp1))) 100;
      "store by f's compartment in the return event of f",
      check_return_store comp2 1;
      "store by main's compartment in the return event of f",
      check_return_store comp1 0 ]

(* Builtins *)

(* [main] performs one builtin, whose arguments are given as event values.
   Pointers point into [buf]. *)
let buf_arg = Events.EVptr_global (buf_id, offset)
let check_builtin ?(stores = []) ?(replayed = 0) ef args () =
  let tr = [ main_id, BtInfoAsm.Bundle_builtin ([], ef, args, List.map store stores) ] in
  let cl = Backtranslation.gen_program tr store_program in
  let* () = compile cl in
  let* () = expect_count "builtins" is_builtin 1 cl in
  expect_count "replayed stores" is_store replayed cl

let chunk_value = function
  | AST.Mint64 -> Events.EVlong (Z.of_sint 1)
  | AST.Mfloat32 -> Events.EVsingle one_single
  | AST.Mfloat64 -> Events.EVfloat one_float
  | _ -> Events.EVint (Z.of_sint 1)

let builtin_checks =
  let int1 = Events.EVint (Z.of_sint 1) and long1 = Events.EVlong (Z.of_sint 1) in
  (* No volatile access at Many32 or Many64 produces an event: eventval_match
     in common/Events.v has no case for Tany32 and Tany64. *)
  let volatile_chunks =
    List.filter (fun (_, ch) -> ch <> AST.Many32 && ch <> AST.Many64) chunks in
  List.map (fun (cn, ch) ->
    ("volatile load " ^ cn, check_builtin (AST.EF_vload ch) [ buf_arg ])) volatile_chunks
  @ List.map (fun (cn, ch) ->
    ("volatile store " ^ cn,
     check_builtin (AST.EF_vstore ch) [ buf_arg; chunk_value ch ])) volatile_chunks
  @ [ "volatile store of a pointer with Mint64",
      check_builtin (AST.EF_vstore AST.Mint64) [ buf_arg; buf_arg ];
      "annotation with int, long and pointer arguments",
      check_builtin (AST.EF_annot (P.of_int 1, "a %1 %2 %3", [AST.Tint; AST.Tlong; AST.coq_Tptr]))
        [ int1; long1; buf_arg ];
      "annotation with double and float arguments",
      check_builtin (AST.EF_annot (P.of_int 1, "a %1 %2", [AST.Tfloat; AST.Tsingle]))
        [ Events.EVfloat one_float; Events.EVsingle one_single ];
      "annotation without arguments",
      check_builtin (AST.EF_annot (P.of_int 1, "a", [])) [];
      "annotated int value",
      check_builtin (AST.EF_annot_val (P.of_int 1, "v", AST.Tint)) [ int1 ];
      "external function with signed char, pointer and double parameters",
      check_builtin (AST.EF_external ("e", sg [AST.Xint8signed; AST.Xptr; AST.Xfloat] AST.Xint))
        [ int1; buf_arg; Events.EVfloat one_float ];
      (* a well-formed store, which is replayed, and an ill-formed one *)
      "external function after retained stores",
      check_builtin (AST.EF_external ("e", sg [AST.Xint] AST.Xint)) [ int1 ]
        ~stores:[ (AST.Mint32, buf_ptr, Values.Vint (Z.of_sint 1), comp1);
                  (AST.Mint8signed, buf_ptr, Values.Vfloat one_float, comp1) ]
        ~replayed:1 ]

(* C programs *)

let zero = Z.of_sint 0

(* An argument of the given type.  Pointers point to [ptr], a public global
   variable, if it is given, and are the null pointer otherwise. *)
let arg_value ptr = function
  | AST.Xptr ->
      (match ptr with
       | Some id -> Events.EVptr_global (id, Integers.Ptrofs.zero)
       | None -> Events.EVlong zero)
  | AST.Xlong | AST.Xany64 -> Events.EVlong zero
  | AST.Xfloat -> Events.EVfloat Floats.Float.zero
  | AST.Xsingle -> Events.EVsingle Floats.Float32.zero
  | _ -> Events.EVint zero

(* A returned value of the given type.  A function with a void result still
   returns the integer register a0 in Asm. *)
let result_value = function
  | AST.Xlong | AST.Xany64 | AST.Xptr -> Events.EVlong zero
  | AST.Xfloat -> Events.EVfloat Floats.Float.zero
  | AST.Xsingle -> Events.EVsingle Floats.Float32.zero
  | _ -> Events.EVint zero

(* A synthetic informative trace for a program compiled from C: main calls
   every external and every other internal function once, and each internal
   callee returns once.  The first call is preceded by two retained stores to
   each public buffer of main's compartment: a well-formed one and an
   ill-formed one. *)
let synthetic_trace (prog: Asm.program) =
  let ge = Globalenvs.Genv.globalenv (fun _ -> AST.COMP.Coq_bottom') prog in
  let main = prog.AST.prog_main in
  let main_comp = match List.assoc_opt main prog.AST.prog_defs with
    | Some (AST.Gfun (AST.Internal f)) -> Some f.Asm.fn_comp
    | _ -> None in
  let public id = List.mem id prog.AST.prog_public in
  let buffers = List.filter_map (fun (id, gd) -> match gd with
    | AST.Gvar v when public id && not v.AST.gvar_readonly
                      && Some v.AST.gvar_comp = main_comp -> Some id
    | _ -> None) prog.AST.prog_defs in
  let ptr = List.find_map (fun (id, gd) -> match gd with
    | AST.Gvar _ when public id -> Some id
    | _ -> None) prog.AST.prog_defs in
  let stores = match main_comp with
    | None -> []
    | Some cp -> List.concat_map (fun id ->
        match Globalenvs.Genv.find_symbol ge id with
        | None -> []
        | Some b ->
            let a = Values.Vptr (b, Integers.Ptrofs.zero) in
            [ store (AST.Mint8unsigned, a, Values.Vint (Z.of_sint 1), cp);
              store (AST.Mint8signed, a, Values.Vfloat one_float, cp) ])
        buffers in
  let events = List.concat_map (fun (id, gd) -> match gd with
    | AST.Gfun (AST.External ef) ->
        let s = AST.ef_sig ef in
        [ main, BtInfoAsm.Bundle_call ([], id, List.map (arg_value ptr) s.AST.sig_args, s, []) ]
    | AST.Gfun (AST.Internal f) when id <> main ->
        let s = f.Asm.fn_sig in
        (* A call to an internal function appears in an informative trace
           only when it crosses compartments, and then no argument is a
           pointer: premise NPTR of ir_step_cross_call_internal in
           security/BtInfoAsm.v. *)
        [ main, BtInfoAsm.Bundle_call ([], id, List.map (arg_value None) s.AST.sig_args, s, []);
          id, BtInfoAsm.Bundle_return ([], result_value s.AST.sig_res, []) ]
    | _ -> []) prog.AST.prog_defs in
  match events with
  | (f, BtInfoAsm.Bundle_call (t, g, args, s, _)) :: rest ->
      (f, BtInfoAsm.Bundle_call (t, g, args, s, stores)) :: rest
  | events -> events

let declared_type = function
  | Ctypes.Internal f -> Clight.type_of_function f
  | Ctypes.External (_, args, res, cc) -> Ctypes.Tfunction (args, res, cc)

let has_prefix p s =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

(* Clight's call rule requires the type at a call site to be the type of the
   callee's declaration, type_of_fundef in cfrontend/Clight.v.  The generated
   code calls functions by name, with one call site for each of the [calls]
   calls in the trace; a call through any other expression is reported,
   since this check could not see its type. *)
let check_call_types calls (cl: Clight.program) =
  let defs = cl.Ctypes.prog_defs in
  let sites = fold_code (fun acc -> function
    | Clight.Scall (_, callee, _) -> callee :: acc
    | _ -> acc) [] cl in
  let wrong = List.filter_map (function
    | Clight.Evar (id, ty) ->
        (match List.assoc_opt id defs with
         | Some (AST.Gfun fd) when ty = declared_type fd -> None
         | Some (AST.Gfun fd) ->
             Some (extern_atom id,
                   Printf.sprintf " (called at type %s, declared with type %s)"
                     (PrintCsyntax.name_type ty) (PrintCsyntax.name_type (declared_type fd)))
         | _ -> Some (extern_atom id, " (not a function of the program)"))
    | _ -> Some ("a callee that is not a function name", "")) sites in
  (* The source's functions first, then the runtime helpers and builtins
     that the C front end declares in every program *)
  let rank s =
    if has_prefix "__builtin_" s then 2 else if has_prefix "__compcert_" s then 1 else 0 in
  let wrong = List.sort_uniq (fun (a, _) (b, _) -> compare (rank a, a) (rank b, b)) wrong in
  if List.length sites <> calls then
    Error (Printf.sprintf "%d call sites for %d calls in the trace" (List.length sites) calls)
  else match wrong with
    | [] -> Ok ()
    | (name, types) :: others ->
        let shown = List.filteri (fun i _ -> i < 4) others in
        Error (Printf.sprintf "the call sites of %d callees differ from their declaration: %s%s%s%s"
                 (List.length wrong) name types
                 (String.concat "" (List.map (fun (n, _) -> ", " ^ n) shown))
                 (if List.length others > 4 then ", ..." else ""))

(* Compile a C file to Asm, preprocessing it as ccomp does. *)
let asm_of_c_file file =
  Diagnostics.reset ();
  let ifile = Filename.temp_file "test_compiles" ".i" in
  Fun.protect ~finally:(fun () -> try Sys.remove ifile with Sys_error _ -> ())
    (fun () ->
      (* The preprocessor and the C front end print their errors on stderr
         and raise [Diagnostics.Abort]. *)
      match (Frontend.preprocess file ifile; Frontend.parse_c_file file ifile) with
      | exception Diagnostics.Abort ->
          Error "preprocessing or the C front end failed, see the messages on stderr"
      | csyntax ->
          match Compiler.transf_c_program csyntax with
          | Errors.OK asm -> Ok asm
          | Errors.Error m -> Error ("the C program does not compile: " ^ string_of_errmsg m))

let program_checks (name, file) =
  let asm = lazy (asm_of_c_file file) in
  [ name ^ ", empty trace", (fun () ->
      let* prog = Lazy.force asm in
      compile (Backtranslation.gen_program [] prog));
    name ^ ", synthetic trace", (fun () ->
      let* prog = Lazy.force asm in
      let trace = synthetic_trace prog in
      let calls = List.length (List.filter (function
        | (_, BtInfoAsm.Bundle_call _) -> true
        | _ -> false) trace) in
      let cl = Backtranslation.gen_program trace prog in
      let* () = compile cl in
      check_call_types calls cl) ]

let setup_error msg =
  prerr_endline ("test_compiles: " ^ msg);
  exit 2

(* The C files of a directory, relative to this executable's directory.
   Files produced by ../compartments/Makefile and hidden files, such as
   editor lock files, are skipped. *)
let c_files dir =
  let here = Filename.dirname Sys.executable_name in
  let files =
    try Sys.readdir (Filename.concat here dir) |> Array.to_list
    with Sys_error msg -> setup_error msg in
  match files
        |> List.filter (fun f -> Filename.check_suffix f ".c" && f.[0] <> '.'
                                 && not (Filename.check_suffix f ".parsed.c"))
        |> List.sort compare with
  | [] -> setup_error ("no C programs in " ^ dir)
  | fs -> List.map (fun f -> (Filename.concat dir f, Filename.concat here (Filename.concat dir f))) fs

let () =
  (* Without it, CompCert would use the compcert.ini next to this
     executable, which is meant for test_backtranslation and preprocesses
     with the host's cc. *)
  if Sys.getenv_opt "COMPCERT_CONFIG" = None then
    setup_error "set COMPCERT_CONFIG to the compcert.ini of the CompCert build, \
                 ../../compcert.ini, or run make run_test_compiles";
  let programs = c_files "../compartments" @ c_files "programs" in
  Frontend.init ();
  group "declarations" declaration_checks;
  group "stores" store_checks;
  group "builtins" builtin_checks;
  group "programs" (List.concat_map program_checks programs);
  if !failed = 0 then Printf.printf "all %d checks passed\n" !total
  else begin
    Printf.printf "%d of %d checks failed\n" !failed !total;
    exit 1
  end
