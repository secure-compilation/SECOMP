open AST
open Camlcoq

let int_reg_num_name r =
  CapAsm.(match r with
       | X1  -> "x1"  | X2  -> "x2"  | X3  -> "x3"
       | X4  -> "x4"  | X5  -> "x5"  | X6  -> "x6"  | X7  -> "x7"
       | X8  -> "x8"  | X9  -> "x9"  | X10 -> "x10" | X11 -> "x11"
       | X12 -> "x12" | X13 -> "x13" | X14 -> "x14" | X15 -> "x15"
       | X16 -> "x16" | X17 -> "x17" | X18 -> "x18" | X19 -> "x19"
       | X20 -> "x20" | X21 -> "x21" | X22 -> "x22" | X23 -> "x23"
       | X24 -> "x24" | X25 -> "x25" | X26 -> "x26" | X27 -> "x27"
       | X28 -> "x28" | X29 -> "x29" | X30 -> "x30" | X31 -> "x31"
       | X32 -> "x32"
  )

let print_option_capasm p f = function
  | Some x ->
     Format.fprintf p "Some@ ";
     f p x
  | None ->
     Format.fprintf p "None"

let print_list_capasm p f xs =
  Format.fprintf p "@[(";
  List.iter (fun x -> f p x; Format.fprintf p "@ ::@ ") xs;
  Format.fprintf p "nil)@]"

let print_Z_capasm p n =
  Format.fprintf p "%s" (Z.to_string n)

(* TODO to_string *)
let print_ident_capasm p id =
  Format.fprintf p "%ld" (P.to_int32 id)

let print_string_capasm p s =
  Format.fprintf p "\"%s\"%%string" (camlstring_of_coqstring s)

let print_typ_capasm p = function
  | Tint ->
     Format.fprintf p "Tint"
  | Tfloat ->
     Format.fprintf p "Tfloat"
  | Tlong ->
     Format.fprintf p "Tlong"
  | Tsingle ->
     Format.fprintf p "Tsingle"
  | Tany32 ->
     Format.fprintf p "Tany32"
  | Tany64 ->
     Format.fprintf p "Tany64"

let print_rettype_capasm p = function
  | Tret ty ->
     Format.fprintf p "Tret@ ";
     print_typ_capasm p ty
  | Tint8signed ->
     Format.fprintf p "Tint8signed"
  | Tint8unsigned ->
     Format.fprintf p "Tint8unsigned"
  | Tint16signed ->
     Format.fprintf p "Tint16signed"
  | Tint16unsigned ->
     Format.fprintf p "Tint16unsigned"
  | Tvoid ->
     Format.fprintf p "Tvoid"

let print_calling_convention_capasm p AST.{ cc_vararg; cc_unproto; cc_structret } =
  Format.fprintf p "{|@ cc_vararg@ :=@ ";
  print_option_capasm p print_Z_capasm cc_vararg;
  Format.fprintf p ";@ cc_unproto@ :=@ ";
  Format.pp_print_bool p cc_unproto;
  Format.fprintf p ";@ cc_structret@ :=@ ";
  Format.pp_print_bool p cc_structret;
  Format.fprintf p "|}@,"

let print_signature_capasm p AST.{ sig_args; sig_res; sig_cc } =
  Format.fprintf p "{|@ sig_args@ :=@ ";
  print_list_capasm p print_typ_capasm sig_args;
  Format.fprintf p ";@ sig_res@ :=@ ";
  print_rettype_capasm p sig_res;
  Format.fprintf p ";@ sig_cc@ :=@ ";
  print_calling_convention_capasm p sig_cc;
  Format.fprintf p "|}@,"

(* TODO parameterize on target, helpers hidden by module type *)
let print_ireg_capasm p r =
  Format.fprintf p "%s" (String.uppercase_ascii (int_reg_num_name r))

let print_ireg0_capasm p = function
  | CapAsm.X0 ->
     Format.fprintf p "X0";
  | CapAsm.X r ->
     Format.fprintf p "(X@ ";
     print_ireg_capasm p r;
     Format.fprintf p ")@,"

let print_offset_asm p = function
  | CapAsm.Ofsimm ofs ->
     Format.fprintf p "Ofsimm@ ";
     print_Z_capasm p ofs
  | CapAsm.Ofslow (id, ofs) ->
     Format.fprintf p "Ofslow@ (";
     print_ident_capasm p id;
     Format.fprintf p ",@ ";
     print_Z_capasm p ofs;
     Format.fprintf p ")@,"

(* TODO: complete the missing cases *)
let print_instruction_capasm p = function
  | CapAsm.Pallocframe (sz, pos) ->
     Format.fprintf p "Pallocframe@ ";
     print_Z_capasm p sz;
     Format.fprintf p "@ ";
     (* TODO function *)
     print_Z_capasm p pos;
  (* TODO: this instruction is not defined in CapAsm (yet?) *)
  (*  | CapAsm.Pfreeframe (sz, pos) ->
      Format.fprintf p "Pfreeframe@ ";
      print_Z_capasm p sz;
      Format.fprintf p "@ ";
      print_Z_capasm p pos *)
  | CapAsm.Paddiw (rd, rs, imm) ->
     Format.fprintf p "Paddiw@ ";
     print_ireg_capasm p rd;
     Format.fprintf p "@ ";
     print_ireg0_capasm p rs;
     Format.fprintf p "@ ";
     print_Z_capasm p imm
  (* TODO: this instruction has different arguments in CapAsm *)
  (*  | CapAsm.Pj_r (r, sg, iscl) ->
      Format.fprintf p "Pj_r@ ";
      print_ireg_capasm p r;
      Format.fprintf p "@ ";
      print_signature_capasm p sg;
      Format.fprintf p "@ ";
      Format.pp_print_bool p iscl *)
  | CapAsm.Pld (rd, ra, ofs, priv) ->
     Format.fprintf p "Pld@ ";
     print_ireg_capasm p rd;
     Format.fprintf p "@ ";
     print_ireg_capasm p ra;
     Format.fprintf p "@ (";
     print_offset_asm p ofs;
     Format.fprintf p ")@ ";
     Format.pp_print_bool p priv
  | CapAsm.Psw (rs, ra, ofs) ->
     Format.fprintf p "Psw@ ";
     print_ireg_capasm p rs;
     Format.fprintf p "@ ";
     print_ireg_capasm p ra;
     Format.fprintf p "@ (";
     print_offset_asm p ofs;
     Format.fprintf p ")@ ";
  | CapAsm.Psd (rs, ra, ofs) ->
     Format.fprintf p "Psd@ ";
     print_ireg_capasm p rs;
     Format.fprintf p "@ ";
     print_ireg_capasm p ra;
     Format.fprintf p "@ (";
     print_offset_asm p ofs;
     Format.fprintf p ")@ ";
  (* TODO: this instruction is not defined in CapAsm *)
  (*   | CapAsm.Ploadsymbol_high (rd, s, ofs) ->
       Format.fprintf p "Ploadsymbol_high@ ";
       print_ireg_capasm p rd;
       Format.fprintf p "@ ";
       print_ident_capasm p s;
       Format.fprintf p "@ ";
       print_Z_capasm p ofs;
       Format.fprintf p "@ "; *)
  | _ ->
     Format.fprintf p "<instr>"

let print_coq_function_asm p CapAsm.{ fn_comp; fn_sig; fn_code } =
  Format.fprintf p "{|@ fn_comp@ :=@ ";
  print_ident_capasm p fn_comp;
  Format.fprintf p ";@ fn_sig@ :=@ ";
  print_signature_capasm p fn_sig;
  Format.fprintf p ";@ fn_code@ :=@ ";
  print_list_capasm p print_instruction_capasm fn_code;
  Format.fprintf p "|}@,"

(* TODO cases *)
let print_external_function_asm p = function
  | EF_external (str, comp, fsig) ->
     Format.fprintf p "EF_external@ (";
     print_string_capasm p str;
     Format.fprintf p ",@ ";
     print_ident_capasm p comp;
     Format.fprintf p ",@ ";
     print_signature_capasm p fsig;
     Format.fprintf p ")"
  | EF_builtin (str, fsig) ->
     Format.fprintf p "EF_builtin@ (";
     print_string_capasm p str;
     Format.fprintf p ",@ ";
     print_signature_capasm p fsig;
     Format.fprintf p ")"
  | EF_runtime (str, fsig) ->
     Format.fprintf p "EF_runtime@ (";
     print_string_capasm p str;
     Format.fprintf p ",@ ";
     print_signature_capasm p fsig;
     Format.fprintf p ")"
  | _ ->
     failwith "unimplemented external function"
(* | EF_vload chunk ->
 *     Format.fprintf p "EF_vload _"
 * | EF_vstore chunk ->
 *     Format.fprintf p "EF_vstore _"
 * | EF_malloc ->
 *     Format.fprintf p "EF_malloc _"
 * | EF_free ->
 *     Format.fprintf p "EF_free _"
 * | EF_memcpy (n1, n2) ->
 *     Format.fprintf p "EF_memcpy _"
 * | EF_annot (lvl, str, tys) ->
 *     Format.fprintf p "EF_annot _"
 * | EF_annot_val (lvl, str, tys) ->
 *     Format.fprintf p "EF_annot_val _"
 * | EF_inline_asm (str, fsig, strs) ->
 *     Format.fprintf p "EF_inline_asm _"
 * | EF_debug (lvl, id, tys) ->
 *     Format.fprintf p "EF_debug _" *)

let print_fundef_asm p = function
  | Internal f ->
     Format.fprintf p "Internal@ @[";
     print_coq_function_asm p f;
     Format.fprintf p "@]@,"
  | External e ->
     Format.fprintf p "External@ (";
     print_external_function_asm p e;
     Format.fprintf p ")@,"

let print_init_data_asm p = function
  | Init_int8 n ->
     Format.fprintf p "Init_int8@ ";
     print_Z_capasm p n
  | Init_int16 n ->
     Format.fprintf p "Init_int816@ ";
     print_Z_capasm p n
  | Init_int32 n ->
     Format.fprintf p "Init_int32@ ";
     print_Z_capasm p n
  | Init_int64 n ->
     Format.fprintf p "Init_int64@ ";
     print_Z_capasm p n
  | _ ->
     failwith "unimplemented initial data"
(* | Init_float32 of float32
 * | Init_float64 of float
 * | Init_space of coq_Z
 * | Init_addrof of ident * Ptrofs.int *)

let print_globvar_asm
      p AST.{ (* gvar_info; *) gvar_comp; gvar_init; gvar_readonly; gvar_volatile } =
  (* TODO unit *)
  Format.fprintf p "{|@ gvar_info@ := tt;@ ";
  Format.fprintf p ";@ gvar_comp@ :=@ ";
  print_ident_capasm p gvar_comp;
  Format.fprintf p ";@ gvar_init@ :=@ ";
  print_list_capasm p print_init_data_asm gvar_init;
  Format.fprintf p ";@ gvar_readonly@ :=@ ";
  Format.pp_print_bool p gvar_readonly;
  Format.fprintf p ";@ gvar_volatile@ :=@ ";
  Format.pp_print_bool p gvar_volatile;
  Format.fprintf p "|}@,"

let print_globdef_asm p = function
  | Gfun f ->
     Format.fprintf p "Gfun@ @[(";
     print_fundef_asm p f;
     Format.fprintf p ")@]@,"
  | Gvar v ->
     Format.fprintf p "Gvar @[";
     print_globvar_asm p v;
     Format.fprintf p "@]@,"

let print_prog_def_asm p (id, glob) =
  Format.fprintf p "@[(";
  print_ident_capasm p id;
  Format.fprintf p ",@ ";
  print_globdef_asm p glob;
  Format.fprintf p ")@]@,"

let print_policy_exports_capasm p (comp_id, funcs) =
  Format.fprintf p "@[(%ld, " (P.to_int32 comp_id);
  print_list_capasm p print_ident_capasm funcs;
  Format.fprintf p ")@]"

let print_policy_imports_capasm p (comp_id, imports) =
  let print_aux p' (comp_id, func) = Format.fprintf p' "(%ld, %ld)" (P.to_int32 comp_id) (P.to_int32 func) in
  Format.fprintf p "@[(%ld, " (P.to_int32 comp_id);
  print_list_capasm p print_aux imports;
  Format.fprintf p ")@]"

let print_policy_asm p Policy.{ policy_export; policy_import } =
  let exports = Maps.PTree.elements policy_export in
  let imports = Maps.PTree.elements policy_import in
  Format.fprintf p "{|@ policy_export@ :=@ ";
  print_list_capasm p print_policy_exports_capasm exports;
  Format.fprintf p ";@ policy_import@ :=@ ";
  print_list_capasm p print_policy_imports_capasm imports;
  Format.fprintf p "|}@,"

let print_program_asm oc prog =
  let p = Format.formatter_of_out_channel oc in
  Format.fprintf p "@[{|@.prog_defs :=@.@[";
  print_list_capasm p print_prog_def_asm prog.prog_defs;
  Format.fprintf p "@];@.prog_public :=@.@[";
  print_list_capasm p print_ident_capasm prog.prog_public;
  Format.fprintf p "@];@.prog_main :=@.@[";
  print_ident_capasm p prog.prog_main;
  Format.fprintf p "@];@.prog_pol :=@.@[";
  print_policy_asm p prog.prog_pol;
  Format.fprintf p "|}@]@."

let show_errmsg em =
  let open Errors in
  let fmt = Printf.sprintf in
  match em with
  | MSG m -> fmt "MSG: %s" (Camlcoq.camlstring_of_coqstring m)
  | CTX p -> fmt "CTX: %d" (Camlcoq.P.to_int p)
  | POS p -> fmt "POS: %d" (Camlcoq.P.to_int p)

let print_cap_asm mach_prog =
  (* TODO: this function is called twice and thus also produces the file twice (in cwd and in runtime/) *)
  Out_channel.with_open_text "out.cap_asm" (fun oc ->
      match CapAsmgen.transf_program mach_prog with
      | Errors.Error msg -> List.iter (fun em -> Printf.fprintf oc "%s\n" (show_errmsg em)) msg
      | Errors.OK cap_asm_prog -> print_program_asm oc cap_asm_prog)

