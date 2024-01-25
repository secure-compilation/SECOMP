let show_errmsg em =
  let open Errors in
  let fmt = Printf.sprintf in
  match em with
  | MSG m -> fmt "MSG: %s" (Camlcoq.camlstring_of_coqstring m)
  | CTX p -> fmt "CTX: %d" (Camlcoq.P.to_int p)
  | POS p -> fmt "POS: %d" (Camlcoq.P.to_int p)

let print mach_prog =
  match CapAsmgen.transf_program mach_prog with
  | Errors.Error msg -> List.iter (fun em -> Printf.printf "%s\n" (show_errmsg em)) msg
  | Errors.OK cap_asm_prog -> print_endline "OK"

