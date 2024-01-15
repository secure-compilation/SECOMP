(* QCheck testing *)
let property_under_test asm_prog bundled_trace =
  let () = Stats.register_trace bundled_trace in
  let () = Stats.register_asm_prog asm_prog in
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
  QCheck.Test.make ~count:1 (bundle_trace ctx) (property_under_test asm_prog)


(* Command line options and configurations *)
let root_seed = ref 0
let asm_seed = ref 0
let trace_seed = ref 0
let debug = ref false
let num_traces = ref 10
let num_asm_progs = ref 10
let mode = ref "test"

let parse_args () =
  let usage_msg = "test_backtranslation [-root_seed n] [-asm_seed n] [-trace_seed n] [-num_traces n] [-num_asm_progs n] [-vebose]" in
  let anon_fun _ = failwith "Unnamed arguments are not supported" in
  let speclist =
    [
      ("-root_seed", Arg.Set_int root_seed, "Root seed for all randomness");
      ("-asm_seed", Arg.Set_int asm_seed, "Seed for an ASM program (implies -num_asm_progs = 1)");
      ("-trace_seed", Arg.Set_int trace_seed, "Seed for a trace (implies -num_traces = 1)");
      ("-num_traces", Arg.Set_int num_traces, "Set the number of traces tested per ASM program (default = 10)");
      ("-num_asm_progs", Arg.Set_int num_asm_progs, "Set the number of ASM programs (default = 10)");
      ("-verbose", Arg.Set debug, "Provide more verbose debug output")
    ] in
  let () = Arg.parse speclist anon_fun usage_msg in
  if !asm_seed != 0 then num_asm_progs := 1;
  if !trace_seed != 0 then num_traces := 1;
  if !asm_seed != 0 && !trace_seed != 0 && !root_seed != 0 then mode := "reproduction"

let gen_config rand_state =
  let open QCheck in
  Gen_ctx.
  {
    num_compartments = Gen.int_range 3 100 rand_state;
    num_exported_funcs = Gen.int_range 5 100 rand_state;
    num_imported_funcs = Gen.int_range 3 100 rand_state;
    num_external_funcs = Gen.int_range 2 100 rand_state;
    num_builtins = Gen.int_range 2 50 rand_state;
    num_runtime_funcs = Gen.int_range 2 50 rand_state;
    num_global_vars = Gen.int_range 2 50 rand_state;
    global_var_max_size = Gen.int_range 4 100 rand_state;
    max_arg_count = 10;
    debug = !debug;
    max_trace_len = 10;
  }

(* Test mode: runs multiple (random) tests to find possible bugs *)
let test_mode _ =
  let () = Printf.printf "*************\n* Test Mode *\n*************\n" in
  let () =
    if !root_seed = 0
    then (Random.self_init (); root_seed := Random.bits ())
  in
  let () = Random.init !root_seed in
  let () = Printf.printf "Root seed = %d\n\n" !root_seed in
  let config = gen_config (Random.get_state ()) in
  let discard_out = Out_channel.open_text "/dev/null" in
  let failure_seeds = ref [] in
  let pass_counter = ref 0 in
  let fail_counter = ref 0 in
  let num_tests = !num_asm_progs * !num_traces in
  let print_results () =
    Printf.printf "\n%d/%d passed\n%d/%d failed\n" !pass_counter num_tests !fail_counter num_tests;
    Stats.print_stats ();
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
  for i = 0 to !num_asm_progs - 1 do
    let asm_seed =
      if !asm_seed = 0
      then Random.bits ()
      else !asm_seed
    in
    let () = Random.init asm_seed in
    let rand_state = Random.get_state () in
    let ctx = Gen_ctx.random config rand_state in
    let asm_prog = Gen_ctx.get_asm_prog ctx in
    for j = 0 to !num_traces - 1 do
      Printf.printf "\rTesting %d / %d asm_progs, %d / %d traces" (i+1) !num_asm_progs (j+1) !num_traces; Out_channel.flush Out_channel.stdout;
      let trace_seed =
        if !trace_seed = 0
        then Random.bits ()
        else !trace_seed
      in
      let () = Random.init trace_seed in
      let rand_state = Random.get_state () in
      if 0 = QCheck_runner.run_tests ~out:discard_out ~rand:rand_state [ test_backtranslation asm_prog ctx ]
      then pass_counter := !pass_counter + 1
      else (failure_seeds := (asm_seed, trace_seed) :: !failure_seeds; fail_counter := !fail_counter + 1);
      Out_channel.flush Out_channel.stdout
    done
  done;
  print_results();
  Out_channel.close discard_out

(* Reproduction mode: reproduces a single (failing) tests for debugging and analysis *)
let reproduction_mode _ =
  let () = Printf.printf "*********************\n* Reproduction Mode *\n*********************\n" in
  let () = assert (!root_seed != 0) in
  let () = assert (!trace_seed != 0) in
  let () = assert (!asm_seed != 0) in
  let () = Printf.printf "Root seed = %d\nASM seed = %d\nTrace seed = %d\n" !root_seed !trace_seed !asm_seed in
  let () = Random.init !root_seed in
  let config = gen_config (Random.get_state ()) in
  let discard_out = Out_channel.open_text "/dev/null" in
  let pass_counter = ref 0 in
  let fail_counter = ref 0 in
  let num_tests = 1 in
  let print_results () =
    Printf.printf "\n%d/%d passed\n%d/%d failed\n" !pass_counter num_tests !fail_counter num_tests;
    Stats.print_stats ()
  in
  let () = Random.init !asm_seed in
  let rand_state = Random.get_state () in
  let ctx = Gen_ctx.random config rand_state in
  let asm_prog = Gen_ctx.get_asm_prog ctx in
  let () = Random.init !trace_seed in
  let rand_state = Random.get_state () in
  if 0 = QCheck_runner.run_tests ~out:discard_out ~rand:rand_state [ test_backtranslation asm_prog ctx ]
  then pass_counter := !pass_counter + 1
  else fail_counter := !fail_counter + 1;
  print_results ();
  Out_channel.flush Out_channel.stdout;
  Out_channel.close discard_out

(* Main *)
let _ =
  let () = parse_args () in
  match !mode with
  | "test" -> test_mode ()
  | "reproduction" -> reproduction_mode ()
  | _ -> failwith "Unknown mode"

