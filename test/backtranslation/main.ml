(* QCheck generators for relevant base types *)

let memory_chunk : AST.memory_chunk QCheck.Gen.t =
  QCheck.Gen.frequencyl
    AST.
      [
        (1, Mint8signed);
        (1, Mint8unsigned);
        (1, Mint16signed);
        (1, Mint16unsigned);
        (1, Mint32);
        (1, Mint64);
        (1, Mfloat32);
        (1, Mfloat64);
        (1, Many32);
        (1, Many64);
      ]

let positive : BinNums.positive QCheck.Gen.t =
  QCheck.Gen.(map (fun i -> Camlcoq.P.of_int (i + 1)) small_nat)

let coq_Z : BinNums.coq_Z QCheck.Gen.t =
  QCheck.Gen.(map (fun i -> Camlcoq.Z.of_sint i) small_signed_int)

let ident : AST.ident QCheck.Gen.t = positive
let compartment : AST.compartment QCheck.Gen.t = positive

let ptrofs : Integers.Ptrofs.int QCheck.Gen.t =
  QCheck.Gen.map (fun i -> Integers.Ptrofs.of_int i) coq_Z

let name : char list QCheck.Gen.t = QCheck.Gen.(small_list (char_range 'a' 'z'))

let binary_float : Floats.float QCheck.Gen.t =
  let open QCheck.Gen in
  let open Binary in
  let zero = map (fun b -> B754_zero b) bool in
  let infinity = map (fun b -> B754_infinity b) bool in
  let nan = map (fun (b, p) -> B754_nan (b, p)) (pair bool positive) in
  let finite =
    map (fun (b, p, z) -> B754_finite (b, p, z)) (triple bool positive coq_Z)
  in
  frequency [ (1, zero); (1, infinity); (1, nan); (1, finite) ]

let eventval : Events.eventval QCheck.Gen.t =
  let open QCheck.Gen in
  let open Events in
  let evint = map (fun i -> EVint (Camlcoq.Z.of_sint i)) small_signed_int in
  let evlong = map (fun i -> EVlong (Camlcoq.Z.of_sint i)) small_signed_int in
  let evfloat = map (fun f -> EVfloat f) binary_float in
  let evsingle = map (fun f -> EVfloat f) binary_float in
  let evptr_global =
    map (fun (i, p) -> EVptr_global (i, p)) (pair ident ptrofs)
  in
  frequency
    [ (1, evint); (1, evlong); (1, evfloat); (1, evsingle); (1, evptr_global) ]

let gen_syscall rand_state =
  let name = name rand_state in
  let arg_count = QCheck.Gen.int_bound 5 in
  let args = QCheck.Gen.list_size arg_count eventval rand_state in
  let ret_val = eventval rand_state in
  Events.Event_syscall (name, args, ret_val)

let gen_vload rand_state =
  let mem_chunk = memory_chunk rand_state in
  let ident = ident rand_state in
  let ptr = ptrofs rand_state in
  let value = eventval rand_state in
  Events.Event_vload (mem_chunk, ident, ptr, value)

let gen_vstore rand_state =
  let mem_chunk = memory_chunk rand_state in
  let ident = ident rand_state in
  let ptr = ptrofs rand_state in
  let value = eventval rand_state in
  Events.Event_vstore (mem_chunk, ident, ptr, value)

let gen_annot rand_state =
  let name = name rand_state in
  let len = QCheck.Gen.int_bound 5 in
  let values = QCheck.Gen.list_size len eventval rand_state in
  Events.Event_annot (name, values)

let gen_call src_compartment trgt_compartment rand_state =
  let ident = ident rand_state in
  let arg_count = QCheck.Gen.int_bound 5 in
  let args = QCheck.Gen.list_size arg_count eventval rand_state in
  Events.Event_call (src_compartment, trgt_compartment, ident, args)

let gen_return src_compartment trgt_compartment rand_state =
  let ret_val = eventval rand_state in
  Events.Event_return (src_compartment, trgt_compartment, ret_val)

let gen_trace rand_state =
  let open QCheck.Gen in
  let len = small_nat rand_state + 1 in
  (* no empty traces will be generated *)
  let rec gen_trace_aux = function
    | 0 -> []
    | n -> (
        let f = float_range 0.0 1.0 rand_state in
        match f with
        | _ when f < 0.6 ->
            let n1, n2 = nat_split2 (n - 1) rand_state in
            let src_compartment = compartment rand_state in
            let trgt_compartment = compartment rand_state in
            let call =
              [ gen_call src_compartment trgt_compartment rand_state ]
            in
            let between = gen_trace_aux n1 in
            let ret =
              [ gen_return src_compartment trgt_compartment rand_state ]
            in
            let after = gen_trace_aux n2 in
            List.concat [ call; between; ret; after ]
        | _ when f < 0.7 -> gen_syscall rand_state :: gen_trace_aux (n - 1)
        | _ when f < 0.8 -> gen_vload rand_state :: gen_trace_aux (n - 1)
        | _ when f < 0.9 -> gen_vstore rand_state :: gen_trace_aux (n - 1)
        | _ -> gen_annot rand_state :: gen_trace_aux (n - 1))
  in
  gen_trace_aux len

let test =
  QCheck.Test.make ~count:1000 ~name:"list_rev_is_involutive"
    QCheck.(list small_nat)
    (fun l -> List.rev (List.rev l) = l)

(* we can check right now the property... *)
let _ = QCheck_runner.run_tests [ test ]

let event_to_string e =
  ignore (Format.flush_str_formatter ());
  Interp.print_event Format.str_formatter e;
  Format.flush_str_formatter ()

let () =
  let rand_state = Random.get_state () in
  let t = gen_trace rand_state in
  print_endline (String.concat "\n" (List.map event_to_string t))
