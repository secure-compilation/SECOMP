let () =
  let _ = Events.coq_E0 in
  print_endline "Hello, world"

let test =
  QCheck.Test.make ~count:1000 ~name:"list_rev_is_involutive"
    QCheck.(list small_nat)
    (fun l -> List.rev (List.rev l) = l)

(* we can check right now the property... *)
let _ = QCheck_runner.run_tests [test]




(* QCheck arbitrary "instances" for relevant base types *)

let memory_chunk : AST.memory_chunk QCheck.arbitrary = QCheck.oneofl AST.[Mint8signed; Mint8unsigned; Mint16signed; Mint16unsigned; Mint32; Mint64; Mfloat32; Mfloat64; Many32; Many64]

let positive : BinNums.positive QCheck.arbitrary = QCheck.(map (fun i -> Camlcoq.P.of_int i) small_int)

let coq_Z : BinNums.coq_Z QCheck.arbitrary = QCheck.(map (fun i -> Camlcoq.Z.of_sint i) small_int)

let ident : AST.ident QCheck.arbitrary = positive

let compartment : AST.compartment QCheck.arbitrary = positive

let ptrofs : Integers.Ptrofs.int QCheck.arbitrary = QCheck.map (fun i -> Integers.Ptrofs.of_int i) coq_Z

let name : (char list) QCheck.arbitrary = QCheck.(small_list printable_char)

let binary_float : Floats.float QCheck.arbitrary =
  let open QCheck in
  let open Binary in
  let zero = map (fun b -> B754_zero b) bool in
  let infinity = map (fun b -> B754_infinity b) bool in
  let nan = map (fun (b, p) -> B754_nan (b, p)) (pair bool positive) in
  let finite = map (fun (b, p, z) -> B754_finite (b, p, z)) (triple bool positive coq_Z) in
  oneof [zero; infinity; nan; finite]

let eventval : Events.eventval QCheck.arbitrary =
  let open QCheck in
  let open Events in
  let evint = map (fun i -> EVint (Camlcoq.Z.of_sint i)) small_int in
  let evlong = map (fun i -> EVlong (Camlcoq.Z.of_sint i)) small_int in
  let evfloat = map (fun f -> EVfloat f) binary_float in
  let evsingle = map (fun f -> EVfloat f) binary_float in
  let evptr_global = map (fun (i, p) -> EVptr_global (i, p)) (pair ident ptrofs) in
  oneof [evint; evlong; evfloat; evsingle; evptr_global]

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

let trace rand_state =
  let open QCheck.Gen in
  let len = small_nat rand_state in
  let rec trace_aux = function
  | 0 -> []
  | n ->
    let f = float_range 0.0 1.0 rand_state in
    if f < 0.6
    then mk_call () :: (List.append (trace_aux (n-1)) [mk_return ()])
    else mk_syscall () :: trace_aux (n-1) in
  trace_aux len

let () = print_endline "hah"

let event_to_string e =
  ignore (Format.flush_str_formatter ());
  Interp.print_event Format.str_formatter e;
  Format.flush_str_formatter ()

let () =
  let rand_state = Random.get_state () in
  let t = trace rand_state in
  print_endline (String.concat "\n" (List.map event_to_string t))

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