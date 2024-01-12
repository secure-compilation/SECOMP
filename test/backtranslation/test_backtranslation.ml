(* QCheck testing *)
let property_under_test asm_prog bundled_trace =
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

let test_backtranslation name asm_prog ctx =
  QCheck.Test.make ~count:1 ~name:name (bundle_trace ctx)
    (property_under_test asm_prog)

let parse_args () =
  let usage_msg = "test_backtranslation [-seed n] [-verbose] [-num_traces n] [-num_asm_progs n]" in
  let seed = ref 0 in
  let debug = ref false in
  let num_traces = ref 10 in
  let num_asm_progs = ref 10 in
  let anon_fun _ = failwith "Unnamed arguments are not supported" in
  let speclist =
    [
      ("-seed", Arg.Set_int seed, "Initial random seed");
      ("-debug", Arg.Set debug, "Provide debug output");
      ("-num_traces", Arg.Set_int num_traces, "Set the number of traces tested per ASM program (default = 10)");
      ("-num_asm_progs", Arg.Set_int num_asm_progs, "Set the number of ASM programs (default = 10)")
    ] in
  let () = Arg.parse speclist anon_fun usage_msg in
  (!seed, !debug, !num_traces, !num_asm_progs)

(* Main *)
let _ =
  let (seed, debug, num_traces, num_asm_progs) = parse_args () in
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
      let s = Random.full_int (Int.shift_left 1 32) in
      Printf.printf "Root seed = %d\n" s;
      Random.init s)
    else Random.init seed
  in
  let discard_out = Out_channel.open_text "/dev/null" in
  let failure_seeds = ref [] in
  let pass_counter = ref 0 in
  let fail_counter = ref 0 in
  let num_tests = num_asm_progs * num_traces in
  let print_results () =
    Printf.printf "\n%d/%d passed\n%d/%d failed\n" !pass_counter num_tests !fail_counter num_tests;
    if List.length !failure_seeds = 0
    then ()
    else (Printf.printf "Failures:\n";
          List.iter (fun (a_s, t_s) -> Printf.printf "\tasm_seed = %d, trace_seed = %d\n" a_s t_s) !failure_seeds) in
  let handle_abort _ =
    print_results ();
    Out_channel.flush Out_channel.stdout;
    exit (~-1) in
  Sys.set_signal Sys.sigint (Sys.Signal_handle handle_abort);
  Sys.set_signal Sys.sigquit (Sys.Signal_handle handle_abort);
  for i = 0 to num_asm_progs - 1 do
    let bound = Int.shift_left 1 32 in
    let asm_seed = Random.full_int bound in
    let trace_root_seed = Random.full_int bound in
    let () = Random.init asm_seed in
    let rand_state = Random.get_state () in
    let ctx = Gen_ctx.random config rand_state in
    let asm_prog = Gen_ctx.get_asm_prog ctx in
    for j = 0 to num_traces - 1 do
      Printf.printf "\rTesting %d / %d asm_progs, %d / %d traces" (i+1) num_asm_progs (j+1) num_traces; Out_channel.flush Out_channel.stdout;
      let () = Random.init (trace_root_seed + j) in
      let trace_seed = Random.full_int bound in
      let () = Random.init trace_seed in
      let name = Printf.sprintf "\ttest_backtranslation (trace_seed = %d)" trace_seed in
      if 0 = QCheck_runner.run_tests ~out:discard_out ~rand:rand_state [ test_backtranslation name asm_prog ctx ]
      then pass_counter := !pass_counter + 1
      else (failure_seeds := (asm_seed, trace_seed) :: !failure_seeds; fail_counter := !fail_counter + 1);
      Out_channel.flush Out_channel.stdout
    done
  done;
  print_results();
  Out_channel.close discard_out
