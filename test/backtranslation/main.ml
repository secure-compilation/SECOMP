let () =
  let _ = Events.coq_E0 in
  print_endline "Hello, world"

let test =
  QCheck.Test.make ~count:1000 ~name:"list_rev_is_involutive"
    QCheck.(list small_nat)
    (fun l -> List.rev (List.rev l) = l)

(* we can check right now the property... *)
let _ = QCheck_runner.run_tests [test]

(* QCheck generators for types *)

let event_val () =
  let n = QCheck.small_int in
  let g = QCheck.get_gen n in
  let rand_state = Random.get_state () in
  g rand_state

let mk_syscall () =
  let name = [] in
  let args = [] in
  let ret_val = Events.EVint (Camlcoq.Z.of_uint 1) in
  Events.Event_syscall (name, args, ret_val)

let mk_vload () =
  let mem_chunk = AST.Mfloat32 in
   let ident = Camlcoq.P.of_int 82 in
   let ptr = Integers.Ptrofs.of_int (Camlcoq.Z.of_uint 15) in
   let value = Events.EVint (Camlcoq.Z.of_uint 29) in
   Events.Event_vload (mem_chunk, ident, ptr, value)

let mk_vstore () =
  let mem_chunk = AST.Mint16unsigned in
  let ident = Camlcoq.P.of_int 41 in
  let ptr = Integers.Ptrofs.of_int (Camlcoq.Z.of_uint 0) in
  let value = Events.EVint (Camlcoq.Z.of_uint 61) in
  Events.Event_vstore (mem_chunk, ident, ptr, value)

let mk_annot () =
  let name = [] in
  let values = [] in
  Events.Event_annot (name, values)

let mk_call () =
  let src_compartment = Camlcoq.P.of_int 13 in
  let trgt_compartment = Camlcoq.P.of_int 54 in
  let ident = Camlcoq.P.of_int 90 in
  let args = [] in
  Events.Event_call (src_compartment, trgt_compartment, ident, args)

let mk_return () =
  let src_compartment = Camlcoq.P.of_int 32 in
  let trgt_compartment = Camlcoq.P.of_int 62 in
  let ret_val = Events.EVint (Camlcoq.Z.of_uint 3) in
  Events.Event_return (src_compartment, trgt_compartment, ret_val)

let () =
  let sys_call = mk_syscall () in
  let vload = mk_vload () in
  let vstore = mk_vstore () in
  let annot = mk_annot () in
  let call = mk_call () in
  let ret = mk_return () in
  let print e = Interp.print_event Format.std_formatter e in
  List.iter (fun e -> print e; Printf.printf "\n") [sys_call; vload; vstore; annot; call; ret]

(*
   type ident = positive
   
   type compartment = positive
   
    type memory_chunk = <simple enum>

    type Ptrofs.int = coq_Z

    type float = binary64

    type float32 = binary32

  Camlcoq


    BinInt.to_pos : coq_Z -> positive


    camlint_of_coqint

    coqint_of_camlint
   
*)