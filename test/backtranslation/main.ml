(* Format failing test cases for output *)
let print_ident i = Printf.sprintf "%d" (Camlcoq.P.to_int i)

let print_event e =
  ignore (Format.flush_str_formatter ());
  Interp.print_event Format.str_formatter e;
  "  " ^ Format.flush_str_formatter ()

let print_trace t =
  Printf.sprintf "[\n%s\n  ]" (String.concat "\n" (List.map print_event t))

let print_eventval_list el =
  ignore (Format.flush_str_formatter ());
  Interp.print_eventval_list Format.str_formatter el;
  "  " ^ Format.flush_str_formatter ()

let print_bundle_event e =
  let open BtInfoAsm in
  let fmt = Printf.sprintf in
  match e with
  | id, Bundle_call (trace, ident, args, sign, mem_delta) ->
      fmt "%s:\n  %s\n  %s\n  %s" (print_ident id) (print_trace trace)
        (print_ident ident) (print_eventval_list args)
  | id, Bundle_return (trace, ret_val, mem_delta) -> "bundle return"
  | id, Bundle_builtin (trace, ext_fun, args, mem_delta) -> "bundle builtin"

let print_bundle_trace _ = "printing not implemented"
(* String.concat "\n" (List.map print_bundle_event t) *)

let print_c_light_program prog =
  let version = PrintClight.Clight1 in
  ignore (Format.flush_str_formatter ());
  PrintClight.print_program version Format.str_formatter prog;
  print_endline (Format.flush_str_formatter ())

let print_compiler_errors errors =
  let open Errors in
  let fmt = Printf.printf in
  List.iter
    (fun e ->
      match e with
      | CTX p | POS p -> fmt "%d" (Camlcoq.P.to_int p)
      | MSG chars -> List.iter (fun c -> fmt "%c" c) chars)
    errors

(* Run QCheck testing *)

let property_under_test asm_prog bundled_trace =
  let src_program = Backtranslation.gen_program bundled_trace asm_prog in
  let () = print_c_light_program src_program in
  match Compiler.transf_clight_program src_program with
  | Errors.Error error_list ->
      print_compiler_errors error_list;
      false
  | Errors.OK _ -> true

let bundle_trace ctx =
  QCheck.make ~print:print_bundle_trace (Gen.bundle_trace ctx)

let test_backtranslation asm_prog ctx =
  QCheck.Test.make ~count:1 ~name:"backtranslation" (bundle_trace ctx)
    (property_under_test asm_prog)

let _ =
  let () = Random.self_init () in
  let rand_state = Random.get_state () in
  let asm_prog, ctx = Gen.asm_program rand_state in
  let () = PrintAsm.print_program_asm Out_channel.stdout asm_prog in
  QCheck_runner.run_tests [ test_backtranslation asm_prog ctx ]
