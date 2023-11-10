let choose_disjoint n k xs rand_state =
  let open QCheck.Gen in
  let take n l = List.of_seq (Seq.take n (List.to_seq l)) in
  let drop n l = List.of_seq (Seq.drop n (List.to_seq l)) in
  let pool = ref xs in
  List.init n (fun _ ->
      let n = int_bound (k - 1) rand_state + 1 in
      let ns = take n !pool in
      pool := drop n !pool;
      ns)

let sublist list =
  match list with
  | [] -> failwith "Cannot sample non-empty subset of empty set"
  | [ x ] -> fun _ -> [ x ]
  | xs ->
      let open QCheck.Gen in
      let len = List.length xs in
      let* len_sublist = map succ (int_bound (len - 1)) in
      (* len sublist is random in [1,len] *)
      let* shuffled_list = shuffle_l xs in
      shuffled_list |> List.to_seq |> Seq.take len_sublist |> List.of_seq
      |> return
