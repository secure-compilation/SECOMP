let export_c_light_program prog main file_name =
  let version = PrintClight.Clight1 in
  let code =
    ignore (Format.flush_str_formatter ());
    PrintClight.print_program version Format.str_formatter prog;
    Format.flush_str_formatter () in
  Out_channel.with_open_text (file_name ^ ".raw") (fun c -> output_string c code);
  let regex_main = Str.regexp ("\\$" ^ string_of_int main ^ "(") in
  let code_with_main = Str.global_replace regex_main "main(" code in
  let regex = Str.regexp "\\$\\([0-9]+\\)" in
  let clean_code = Str.global_replace regex "ident_\\1" code_with_main in
  Out_channel.with_open_text file_name (fun c -> output_string c clean_code)

(* Run QCheck testing *)

let property_under_test asm_prog bundled_trace =
  let source_name = "out.c" in
  let ccomp_cmd = "../../ccomp -quiet > /dev/null" in
  let src_program = Backtranslation.gen_program bundled_trace asm_prog in
  let main = Camlcoq.P.to_int asm_prog.prog_main in
  let () = export_c_light_program src_program main source_name in
  let status = Unix.system (ccomp_cmd ^ " " ^ source_name) in
  match status with
  | WEXITED code -> code = 0
  | WSIGNALED _ | WSTOPPED _ -> false

let bundle_trace ctx =
  QCheck.make ~print:Print.print_bundle_trace (Gen.bundle_trace ctx)

let test_backtranslation asm_prog ctx =
  QCheck.Test.make ~count:10 ~name:"backtranslation" (bundle_trace ctx)
    (property_under_test asm_prog)

let _ =
  let () = Random.self_init () in
  let rand_state = Random.get_state () in
  let asm_prog, ctx = Gen.asm_program rand_state in
  (*let () = PrintAsm.print_program_asm Out_channel.stdout asm_prog in*)
  QCheck_runner.run_tests [ test_backtranslation asm_prog ctx ]
