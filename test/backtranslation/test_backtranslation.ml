(* QCheck testing *)
let property_under_test asm_prog bundled_trace =
  let () = print_endline (Show.show_bundle_trace bundled_trace) in
  let source_name = "out.c" in
  let ccomp_cmd = "../../ccomp -quiet -c > /dev/null 2> /dev/null" in
  let src_program = Backtranslation.gen_program bundled_trace asm_prog in
  let () = Export.c_light_prog src_program source_name in
  let status = Unix.system (ccomp_cmd ^ " " ^ source_name) in
  match status with
  | WEXITED code -> code = 0
  | WSIGNALED _ | WSTOPPED _ -> false

let bundle_trace ctx =
  QCheck.make ~print:Show.show_bundle_trace (Gen.bundle_trace ctx)

let test_backtranslation asm_prog ctx =
  QCheck.Test.make ~count:1 ~name:"backtranslation" (bundle_trace ctx)
    (property_under_test asm_prog)

let parse_args () =
  let usage_msg = "test_backtranslation [-seed n] [-verbose]" in
  let seed = ref 0 in
  let debug = ref false in
  let anon_fun _ = failwith "Unnamed arguments are not supported" in
  let speclist =
    [
      ("-seed", Arg.Set_int seed, "Initial random seed");
      ("-debug", Arg.Set debug, "Provide debug output")
    ] in
  let () = Arg.parse speclist anon_fun usage_msg in
  (!seed, !debug)

(* Main *)
let _ =
  let (seed, debug) = parse_args () in
  let config =
    Gen_ctx.
      {
        num_compartments = 3;
        num_exported_funcs = 5;
        num_imported_funcs = 3;
        num_external_funcs = 4;
        num_builtins = 4;
        num_runtime_funcs = 4;
        num_global_vars = 4;
        global_var_max_size = 4;
        max_arg_count = 2;
        debug = debug;
      }
  in
  let () =
    if seed = 0
    then
      (Random.self_init ();
      let s = Random.full_int 10000 in
      Printf.printf "seed = %d\n" s;
      Random.init s)
    else Random.init seed
  in
  let rand_state = Random.get_state () in
  let ctx = Gen_ctx.random config rand_state in
  let asm_prog = Gen_ctx.get_asm_prog ctx in
  if debug then PrintAsm.print_program_asm Out_channel.stdout asm_prog else ();
  QCheck_runner.run_tests ~verbose:true ~rand:rand_state [ test_backtranslation asm_prog ctx ]
