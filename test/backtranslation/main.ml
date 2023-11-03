let () =
  let _ = Events.coq_E0 in
  print_endline "Hello, world"

let test =
  QCheck.Test.make ~count:1000 ~name:"list_rev_is_involutive"
    QCheck.(list small_nat)
    (fun l -> List.rev (List.rev l) = l)

(* we can check right now the property... *)
let _ = QCheck_runner.run_tests [test]