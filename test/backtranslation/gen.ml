let memory_chunk =
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

let positive = QCheck.Gen.(map (fun i -> Camlcoq.P.of_int (i + 1)) small_nat)
let coq_Z = QCheck.Gen.(map (fun i -> Camlcoq.Z.of_sint i) small_signed_int)
let ident = positive
let compartment = positive
let ptrofs = QCheck.Gen.map (fun i -> Integers.Ptrofs.of_int i) coq_Z
let char_list = QCheck.Gen.(small_list (char_range 'a' 'z'))

let binary_float =
  let open QCheck.Gen in
  let open Binary in
  let zero = map (fun b -> B754_zero b) bool in
  let infinity = map (fun b -> B754_infinity b) bool in
  let nan = map (fun (b, p) -> B754_nan (b, p)) (pair bool positive) in
  let finite =
    map (fun (b, p, z) -> B754_finite (b, p, z)) (triple bool positive coq_Z)
  in
  frequency [ (1, zero); (1, infinity); (1, nan); (1, finite) ]

let eventval =
  let open QCheck.Gen in
  let open Events in
  let evint = map (fun i -> EVint i) coq_Z in
  let evlong = map (fun i -> EVlong i) coq_Z in
  let evfloat = map (fun f -> EVfloat f) binary_float in
  let evsingle = map (fun f -> EVfloat f) binary_float in
  let evptr_global =
    map (fun (i, p) -> EVptr_global (i, p)) (pair ident ptrofs)
  in
  frequency
    [ (1, evint); (1, evlong); (1, evfloat); (1, evsingle); (1, evptr_global) ]

let event_syscall size =
  let open QCheck.Gen in
  let* name = char_list in
  let* args = list_size size eventval in
  let* ret_val = eventval in
  return (Events.Event_syscall (name, args, ret_val))

let event_vload =
  let open QCheck.Gen in
  let* mem_chunk = memory_chunk in
  let* ident = ident in
  let* ptr = ptrofs in
  let* value = eventval in
  return (Events.Event_vload (mem_chunk, ident, ptr, value))

let event_vstore =
  let open QCheck.Gen in
  let* mem_chunk = memory_chunk in
  let* ident = ident in
  let* ptr = ptrofs in
  let* value = eventval in
  return (Events.Event_vstore (mem_chunk, ident, ptr, value))

let event_annot size =
  let open QCheck.Gen in
  let* name = char_list in
  let* values = list_size size eventval in
  return (Events.Event_annot (name, values))

let event_call src_compartment trgt_compartment size =
  let open QCheck.Gen in
  let* ident = ident in
  let* args = list_size size eventval in
  return (Events.Event_call (src_compartment, trgt_compartment, ident, args))

let event_return src_compartment trgt_compartment =
  let open QCheck.Gen in
  let* ret_val = eventval in
  return (Events.Event_return (src_compartment, trgt_compartment, ret_val))

(* QCheck generator for an event trace *)

let trace rand_state =
  let open QCheck.Gen in
  (* ensure that no empty traces are generated *)
  let size = small_nat rand_state + 1 in
  let rec gen_trace_aux = function
    | 0 -> []
    | n -> (
        let f = float_range 0.0 1.0 rand_state in
        match f with
        | _ when f < 0.6 ->
            let n1, n2 = nat_split2 (n - 1) rand_state in
            let src_compartment = compartment rand_state in
            let trgt_compartment = compartment rand_state in
            let arg_count = int_bound 5 in
            let call =
              [
                event_call src_compartment trgt_compartment arg_count rand_state;
              ]
            in
            let between = gen_trace_aux n1 in
            let ret =
              [ event_return src_compartment trgt_compartment rand_state ]
            in
            let after = gen_trace_aux n2 in
            List.concat [ call; between; ret; after ]
        | _ when f < 0.7 ->
            let arg_count = int_bound 5 in
            event_syscall arg_count rand_state :: gen_trace_aux (n - 1)
        | _ when f < 0.8 -> event_vload rand_state :: gen_trace_aux (n - 1)
        | _ when f < 0.9 -> event_vstore rand_state :: gen_trace_aux (n - 1)
        | _ ->
            let size = int_bound 5 in
            event_annot size rand_state :: gen_trace_aux (n - 1))
  in
  gen_trace_aux size

let sublist list rand_state =
  match list with
  | [] -> []
  | [ x ] -> [ x ]
  | xs ->
      let open QCheck.Gen in
      let len = List.length xs in
      let len_sublist = int_bound (len - 1) rand_state + 1 in
      (* len sublist is random in [1,len] *)
      let shuffled_list = shuffle_l xs rand_state in
      List.of_seq (Seq.take len_sublist (List.to_seq shuffled_list))

let exports graph rand_state =
  let open QCheck.Gen in
  let n = Graph.size graph in
  (* map succ to ensure that each compartment exports at least one function *)
  let sample = list_size (map succ (int_bound 15)) small_nat in
  Array.init n (fun _ -> List.sort_uniq Int.compare (sample rand_state))

let imports graph exports rand_state =
  let open QCheck.Gen in
  let n = Graph.size graph in
  let imports = Array.make_matrix n n [] in
  (* imports.(self).(other) contains a list of all functions that compartment self imports from compartment other *)
  for self = 0 to n - 1 do
    for other = 0 to n - 1 do
      if Graph.is_adjacent self other graph then
        let all_exports = exports.(other) in
        imports.(self).(other) <-
          List.sort Int.compare (sublist all_exports rand_state)
      else ()
    done
  done;
  imports

let policy rand_state =
  let max_graph_size = 10 in
  let adj_list = Graph.random max_graph_size rand_state in
  let exports = exports adj_list rand_state in
  let imports = imports adj_list exports rand_state in
  (adj_list, exports, imports)
