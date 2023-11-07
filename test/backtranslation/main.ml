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
  let evint = map (fun i -> EVint i) coq_Z in
  let evlong = map (fun i -> EVlong i) coq_Z in
  let evfloat = map (fun f -> EVfloat f) binary_float in
  let evsingle = map (fun f -> EVfloat f) binary_float in
  let evptr_global =
    map (fun (i, p) -> EVptr_global (i, p)) (pair ident ptrofs)
  in
  frequency
    [ (1, evint); (1, evlong); (1, evfloat); (1, evsingle); (1, evptr_global) ]

let gen_syscall size : Events.event QCheck.Gen.t =
  let open QCheck.Gen in
  let* name = name in
  let* args = list_size size eventval in
  let* ret_val = eventval in
  return (Events.Event_syscall (name, args, ret_val))

let gen_vload : Events.event QCheck.Gen.t =
  let open QCheck.Gen in
  let* mem_chunk = memory_chunk in
  let* ident = ident in
  let* ptr = ptrofs in
  let* value = eventval in
  return (Events.Event_vload (mem_chunk, ident, ptr, value))

let gen_vstore : Events.event QCheck.Gen.t =
  let open QCheck.Gen in
  let* mem_chunk = memory_chunk in
  let* ident = ident in
  let* ptr = ptrofs in
  let* value = eventval in
  return (Events.Event_vstore (mem_chunk, ident, ptr, value))

let gen_annot size : Events.event QCheck.Gen.t =
  let open QCheck.Gen in
  let* name = name in
  let* values = list_size size eventval in
  return (Events.Event_annot (name, values))

let gen_call src_compartment trgt_compartment size : Events.event QCheck.Gen.t =
  let open QCheck.Gen in
  let* ident = ident in
  let* args = list_size size eventval in
  return (Events.Event_call (src_compartment, trgt_compartment, ident, args))

let gen_return src_compartment trgt_compartment : Events.event QCheck.Gen.t =
  let open QCheck.Gen in
  let* ret_val = eventval in
  return (Events.Event_return (src_compartment, trgt_compartment, ret_val))

(* QCheck generator for an event trace *)

let gen_trace rand_state =
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
              [ gen_call src_compartment trgt_compartment arg_count rand_state ]
            in
            let between = gen_trace_aux n1 in
            let ret =
              [ gen_return src_compartment trgt_compartment rand_state ]
            in
            let after = gen_trace_aux n2 in
            List.concat [ call; between; ret; after ]
        | _ when f < 0.7 ->
            let arg_count = int_bound 5 in
            gen_syscall arg_count rand_state :: gen_trace_aux (n - 1)
        | _ when f < 0.8 -> gen_vload rand_state :: gen_trace_aux (n - 1)
        | _ when f < 0.9 -> gen_vstore rand_state :: gen_trace_aux (n - 1)
        | _ ->
            let size = int_bound 5 in
            gen_annot size rand_state :: gen_trace_aux (n - 1))
  in
  gen_trace_aux size

let gen_graph max_size rand_state : (int * int) list = 
  let open QCheck.Gen in
  let n = int_bound max_size rand_state + 1 in
  let adjacency = Array.make_matrix n n 0 in
  for i = 0 to (n - 1) do 
    let row = int_bound (n - 1) rand_state in
    let col = int_bound (n - 1) rand_state in
    let () = adjacency.(row).(col) <- 1 in
    let () = adjacency.(col).(row) <- 1 in
    ()
  done;
  let result = ref [] in
  for row = 0 to n - 1 do
    for col = 0 to n - 1 do
      if adjacency.(row).(col) <> 0
        then result := (Int.min row col, Int.max row col) :: !result
        else ()
    done
  done;
  let compare (x1, x2) (y1, y2) = if Int.compare x1 y1 = 0 then Int.compare x2 y2 else Int.compare x1 y1 in
  List.sort_uniq compare !result

let make_consecutive edge_list : (int * int) list =
  let vertices = List.sort_uniq (Int.compare) (List.map fst edge_list @ List.map snd edge_list) in
  let new_idcs = List.mapi (fun idx elt -> (elt, idx)) vertices in
  List.map (fun (src, trgt) -> (List.assoc src new_idcs, List.assoc trgt new_idcs)) edge_list

let scc edge_list : (int * int) list =
  match edge_list with
  | [] -> []
  | (root, _) :: es ->
    let did_update = ref true in
    let reachable = ref [root] in
    while !did_update do
      did_update := false;
      for i = 0 to List.length edge_list - 1 do
        let (src, trgt) = List.nth edge_list i in
          if List.mem src !reachable && not (List.mem trgt !reachable)
            then
            (reachable := trgt :: !reachable; did_update := true)
          else
            (if List.mem trgt !reachable && not (List.mem src !reachable)
              then
            (reachable := src :: !reachable;
            did_update := true)
           else
              ())
      done;
    done;
    List.filter (fun (src, trgt) -> List.exists (fun n -> n = src || n = trgt) !reachable) edge_list

type graph = (int * (int list)) list

let convert_graph edge_list =
  let vertices = List.sort_uniq Int.compare (List.map fst edge_list @ List.map snd edge_list) in
  let neighbors v = List.sort_uniq Int.compare (List.filter_map (fun (w1, w2) -> 
    if w1 = v && not (w2 = v)
    then Option.some w2
    else 
      (if not (w1 = v) && w2 = v
        then Option.some w1
        else Option.none))
 edge_list) in
  List.map (fun v -> (v, neighbors v)) vertices

let sample_exports graph rand_state =
  let open QCheck.Gen in
  let n = List.length graph in
  (* map succ to ensure that each compartment exports at least one function *)
  let sample = list_size (map succ (int_bound 15)) small_nat in
  Array.init n (fun _ -> List.sort_uniq Int.compare (sample rand_state))

let sample_sublist list rand_state =
  match list with
  | [] -> []
  | [x] -> [x]
  | xs ->
    let open QCheck.Gen in
    let len = List.length xs in
    let len_sublist = int_bound (len - 1) rand_state + 1 in
    (* len sublist is random in [1,len] *)
    let shuffled_list = shuffle_l xs rand_state in
    List.of_seq (Seq.take len_sublist (List.to_seq shuffled_list))

let sample_imports graph exports rand_state =
  let open QCheck.Gen in
  let vertices = List.map fst graph in
  let has_neighbor v w = List.mem w (List.assoc v graph) in
  let n = List.length vertices in
  let imports = Array.make_matrix n n [] in
  (* imports.(self).(other) contains a list of all functions that compartment self imports from compartment other *)
  for self = 0 to n - 1 do
    for other = 0 to n - 1 do
      if has_neighbor self other
      then begin
        let all_exports = exports.(other) in
        imports.(self).(other) <- List.sort Int.compare (sample_sublist all_exports rand_state)
      end
      else ()
    done
  done;
  imports

let sample_env rand_state =
  let max_graph_size = 10 in
  let edge_list = gen_graph max_graph_size rand_state in
  let scc = make_consecutive (scc edge_list) in
  let adj_list = convert_graph scc in
  let exports = sample_exports adj_list rand_state in
  let imports = sample_imports adj_list exports rand_state in
  (adj_list, exports, imports)

let graph_to_dot adj_list =
  let fmt = Printf.sprintf in
  let edges = List.concat_map (fun (src, trgts) -> List.map (fun t -> if src < t then (src, t) else (t, src)) trgts) adj_list in
  let compare (x1, y1) (x2, y2) = if Int.compare x1 x2 = 0 then Int.compare y1 y2 else Int.compare x1 x2 in
  let edges = List.sort_uniq compare edges in
  let string_of_edge (src, trgt) = fmt "  %d -- %d;" src trgt in
  fmt "graph {\n%s\n}" (String.concat "\n" (List.map string_of_edge edges))

(* let event_to_string e =
  ignore (Format.flush_str_formatter ());
  Interp.print_event Format.str_formatter e;
  Format.flush_str_formatter ()

let print_trace t = String.concat "\n" (List.map event_to_string t)
let trace = QCheck.make ~print:print_trace gen_trace

(* Run QCheck testing *)
let test_backtranslation =
  QCheck.Test.make ~count:1 ~name:"backtranslation is correct" trace (fun _ ->
      false)

let _ = QCheck_runner.run_tests [ test_backtranslation ] *)

let dump_exports exports =
  let open Printf in
  printf "Exports:\n";
  Array.iteri (fun i es -> printf "%i --> [%s]\n" i (String.concat "," (List.map (sprintf "%i") es))) exports

let dump_imports imports =
  let open Printf in
  printf "Imports:\n";
  for self = 0 to Array.length imports - 1 do
    for other = 0 to Array.length imports - 1 do
      if List.length imports.(self).(other) = 0
        then ()
    else 
      printf "%i <-- %i: [%s]\n" self other (String.concat "," (List.map (fun f -> sprintf "%d" f) imports.(self).(other)))
    done
  done

let () =
    let () = Random.self_init () in
    let rand_state = Random.get_state () in
    let (graph, exports, imports) = sample_env rand_state in
    let () = Out_channel.with_open_text "graph.dot" (fun f -> output_string f (graph_to_dot graph)) in
    let _ = Unix.system "dot -Tpng graph.dot > graph.png" in
    let () = print_endline "Generated graph.png" in
    dump_exports exports; dump_imports imports
