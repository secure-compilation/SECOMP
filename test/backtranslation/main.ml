(*
  - call and return should be easy to get from regular trace
  - generation of builtin should also be possible, effectively <primitive enum>
  - mem_delta = mem_delta_kind list
    - perhaps for the beginning we can set everything to empty list?
  - mem_delta_kind = <primitive enum>
*)

(*
       For asm_prog we need
       - (fundef, unit) AST.program
       - fundef = coq_function AST.fundef
         - coq_function = compartment * signature * code
         - code = instruction list
         - AST.fundef = external function | internal coq_function
         - external function = <"primitive" enum>
*)

(* Run QCheck testing *)

let property_under_test asm_prog bundled_trace =
  let src_program = Backtranslation.gen_program bundled_trace asm_prog in
  match Compiler.transf_clight_program src_program with
  | Errors.Error _ -> false
  | Errors.OK _ -> true

let print_bundle_trace t =
  String.concat "\n" (List.map (fun _ -> "TODO: implement me") t)

let bundle_trace = QCheck.make ~print:print_bundle_trace Gen.bundle_trace

let test_backtranslation asm_prog =
  QCheck.Test.make ~count:1 ~name:"backtranslation" bundle_trace
    (property_under_test asm_prog)

let _ =
  let () = Random.self_init () in
  let rand_state = Random.get_state () in
  let asm_prog = Gen.asm_program rand_state in
  QCheck_runner.run_tests [ test_backtranslation asm_prog ]
