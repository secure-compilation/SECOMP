type t = (int * int list) list

let gen_graph max_size rand_state : (int * int) list =
  let open QCheck.Gen in
  let n = int_bound max_size rand_state + 1 in
  let adjacency = Array.make_matrix n n 0 in
  for i = 0 to n - 1 do
    let row = int_bound (n - 1) rand_state in
    let col = int_bound (n - 1) rand_state in
    let () = adjacency.(row).(col) <- 1 in
    let () = adjacency.(col).(row) <- 1 in
    ()
  done;
  let result = ref [] in
  for row = 0 to n - 1 do
    for col = 0 to n - 1 do
      if adjacency.(row).(col) <> 0 then
        result := (Int.min row col, Int.max row col) :: !result
      else ()
    done
  done;
  let compare (x1, x2) (y1, y2) =
    if Int.compare x1 y1 = 0 then Int.compare x2 y2 else Int.compare x1 y1
  in
  List.sort_uniq compare !result

let normalize edge_list : (int * int) list =
  let vertices =
    List.sort_uniq Int.compare (List.map fst edge_list @ List.map snd edge_list)
  in
  let new_idcs = List.mapi (fun idx elt -> (elt, idx + 1)) vertices in
  List.map
    (fun (src, trgt) -> (List.assoc src new_idcs, List.assoc trgt new_idcs))
    edge_list

let scc edge_list : (int * int) list =
  match edge_list with
  | [] -> []
  | (root, _) :: es ->
      let did_update = ref true in
      let reachable = ref [ root ] in
      while !did_update do
        did_update := false;
        for i = 0 to List.length edge_list - 1 do
          let src, trgt = List.nth edge_list i in
          if List.mem src !reachable && not (List.mem trgt !reachable) then (
            reachable := trgt :: !reachable;
            did_update := true)
          else if List.mem trgt !reachable && not (List.mem src !reachable) then (
            reachable := src :: !reachable;
            did_update := true)
          else ()
        done
      done;
      List.filter
        (fun (src, trgt) ->
          List.exists (fun n -> n = src || n = trgt) !reachable)
        edge_list

let convert_graph edge_list =
  let vertices =
    List.sort_uniq Int.compare (List.map fst edge_list @ List.map snd edge_list)
  in
  let neighbors v =
    List.sort_uniq Int.compare
      (List.filter_map
         (fun (w1, w2) ->
           if w1 = v && not (w2 = v) then Option.some w2
           else if (not (w1 = v)) && w2 = v then Option.some w1
           else Option.none)
         edge_list)
  in
  List.map (fun v -> (v, neighbors v)) vertices

let random size rand_state =
  rand_state |> gen_graph size |> scc |> normalize |> convert_graph

let size = List.length
let vertices = List.map fst

let is_adjacent self other graph =
  match List.assoc_opt self graph with
  | None -> false
  | Some neighbors -> List.mem other neighbors

let to_dot adj_list =
  let fmt = Printf.sprintf in
  let edges =
    List.concat_map
      (fun (src, trgts) ->
        List.map (fun t -> if src < t then (src, t) else (t, src)) trgts)
      adj_list
  in
  let compare (x1, y1) (x2, y2) =
    if Int.compare x1 x2 = 0 then Int.compare y1 y2 else Int.compare x1 x2
  in
  let edges = List.sort_uniq compare edges in
  let string_of_edge (src, trgt) = fmt "  %d -- %d;" src trgt in
  let string_of_vertex v = fmt "  %d;" v in
  fmt "graph {\n%s\n%s\n}"
    (String.concat "\n" (List.map string_of_vertex (vertices adj_list)))
    (String.concat "\n" (List.map string_of_edge edges))

let dump graph =
  Out_channel.with_open_text "graph.dot" (fun f ->
      output_string f (to_dot graph));
  let _ = Unix.system "dot -Tpng graph.dot > graph.png" in
  print_endline "Generated graph.png"
