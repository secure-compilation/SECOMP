let rename_special_floating_point_values code =
  let r_inf = Str.regexp "\\(inf \| inff\\)" in
  let r_nan = Str.regexp "\\(nan \| nanf\\)" in
  code
  |> Str.global_replace r_inf "INFINITY"
  |> Str.global_replace r_nan "NAN"

let rename_main main code =
  let regex_main = Str.regexp ("\\$" ^ string_of_int main ^ "(") in
  Str.global_replace regex_main "main(" code

let rename_idents code =
  let regex = Str.regexp "\\$\\([0-9]+\\)" in
  Str.global_replace regex "ident_\\1" code

let prepend_header code =
  "#include <math.h>\n" ^ code

let fix_incomplete_types code =
  let r_internal = Str.regexp "^void \\(ident_[0-9]+ = {\\)" in
  let r_external = Str.regexp "^extern void" in
  code
  |> Str.global_replace r_internal "void* \\1"
  |> Str.global_replace r_external "extern void*"

let c_light_prog prog file_name =
  let vars_before_funcs (_, def1) (_, def2) =
    let open AST in
    match (def1, def2) with
    | (Gfun _, Gvar _) -> 1
    | (Gvar _, Gfun _) -> -1
    | _ -> 0
  in
  let prog = Ctypes.{ prog with prog_defs = List.sort vars_before_funcs prog.prog_defs } in
  let raw_code = Show.show_c_light_program prog in
  let main = Camlcoq.P.to_int prog.prog_main in
  let code =
    raw_code
    |> rename_main main
    |> rename_idents
    |> rename_special_floating_point_values
    |> prepend_header
    |> fix_incomplete_types in
  Out_channel.with_open_text (file_name ^ ".raw") (fun c -> output_string c raw_code);
  Out_channel.with_open_text file_name (fun c -> output_string c code)
