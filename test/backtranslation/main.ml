let event_to_string _ =
  ignore (Format.flush_str_formatter ());
  (* TODO: reenable this once the build issues are resolved and we can depend on Interp (and its transitive
     dependecies) again *)
  (* Interp.print_event Format.str_formatter e; *)
  Format.flush_str_formatter ()

let print_trace t = String.concat "\n" (List.map event_to_string t)
let trace = QCheck.make ~print:print_trace Gen.trace

let dump_exports exports =
  let open Printf in
  printf "Exports:\n";
  Array.iteri
    (fun i es ->
      printf "%i --> [%s]\n" i (String.concat "," (List.map (sprintf "%i") es)))
    exports

let dump_imports imports =
  let open Printf in
  printf "Imports:\n";
  for self = 0 to Array.length imports - 1 do
    for other = 0 to Array.length imports - 1 do
      if List.length imports.(self).(other) = 0 then ()
      else
        printf "%i <-- %i: [%s]\n" self other
          (String.concat ","
             (List.map (fun f -> sprintf "%d" f) imports.(self).(other)))
    done
  done

let () =
  let () = Random.self_init () in
  let rand_state = Random.get_state () in
  let graph, exports, imports = Gen.policy rand_state in
  let () =
    Out_channel.with_open_text "graph.dot" (fun f ->
        output_string f (Graph.to_dot graph))
  in
  let _ = Unix.system "dot -Tpng graph.dot > graph.png" in
  let () = print_endline "Generated graph.png" in
  dump_exports exports;
  dump_imports imports

(*
  - call and return should be easy to get from regular trace
  - generation of builtin should also be possible, effectively <primitive enum>
  - mem_delta = mem_delta_kind list
    - perhaps for the beginning we can set everything to empty list?
  - mem_delta_kind = <primitive enum>
*)
(* let bundle_trace trace = failwith "TODO: implement me"

   let property_under_test trace =
     let bundled_trace = failwith "TODO: implement me" in
     (*
       For asm_prog we need
       - (fundef, unit) AST.program
       - fundef = coq_function AST.fundef
         - coq_function = compartment * signature * code
         - code = instruction list
         - signature = typ list * rettype * calling_convention
         - calling_convention = <primitive struct>
         - typ = <primitive enum>
         - rettype = <primitive enum>
         - AST.fundef = external function | internal coq_function
         - external function = <"primitive" enum>

       - we definitely need a policy object (--> from my graph approach)
       -
     *)
     let prog_defs = failwith "TODO: implement me" in
     let prog_public = failwith "TODO: implement me" in
     let prog_main = failwith "TODO: implement me" in
     let prog_pol = failwith "TODO: implement me" in
     let asm_prog = { prog_defs; prog_public; prog_main; prog_pol } : ASM.program in
     let src_program = Backtranslation.gen_program bundled_trace asm_prog in
     match Compiler.trans_clight_program src_program with
     | Errors.Error _ -> false
     | Errors.Ok _ -> true
*)

(* Run QCheck testing *)
(* let test_backtranslation =
     QCheck.Test.make ~count:1 ~name:"backtranslation is correct" trace (fun _ ->
         false)

   let _ = QCheck_runner.run_tests [ test_backtranslation ] *)
