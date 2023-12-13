let rename_special_floating_point_values code =
  let r_inf = Str.regexp "inf" in
  let r_nan = Str.regexp "nan" in
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

let c_light_prog prog file_name =
  let version = PrintClight.Clight1 in
  let vars_before_funcs (_, def1) (_, def2) =
    let open AST in
    match (def1, def2) with
    | (Gfun _, Gvar _) -> 1
    | (Gvar _, Gfun _) -> -1
    | _ -> 0
  in
  let prog = Ctypes.{ prog with prog_defs = List.sort vars_before_funcs prog.prog_defs } in
  let raw_code =
    ignore (Format.flush_str_formatter ());
    PrintClight.print_program version Format.str_formatter prog;
    Format.flush_str_formatter () in
  let main = Camlcoq.P.to_int prog.prog_main in
  let code =
    raw_code
    |> rename_main main
    |> rename_idents
    |> rename_special_floating_point_values
    |> prepend_header in
  Out_channel.with_open_text (file_name ^ ".raw") (fun c -> output_string c raw_code);
  Out_channel.with_open_text file_name (fun c -> output_string c code)
