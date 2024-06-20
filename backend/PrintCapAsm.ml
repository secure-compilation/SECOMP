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

let print_comp_capasm p = function
  | AST.COMP.Coq_bottom' -> Format.fprintf p "bottom"
  | AST.COMP.Coq_top' -> Format.fprintf p "top"
  | AST.COMP.Comp i -> print_ident_capasm p i

let print_bool_capasm p b =
  if b
  then Format.fprintf p "true"
  else Format.fprintf p "false"

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

let print_creg_capasm p = function
  | CapAsm.IRcap ir ->
     Format.fprintf p "(IRCap@ (";
     print_ireg_capasm p ir;
     Format.fprintf p "))"
  | CapAsm.PCcap -> Format.fprintf p "PCcap"
  | CapAsm.DDcap -> Format.fprintf p "DDcap"

let print_offset_capasm p = function
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
     print_offset_capasm p ofs;
     Format.fprintf p ")@ ";
     Format.pp_print_bool p priv
  | CapAsm.Psw (rs, ra, ofs) ->
     Format.fprintf p "Psw@ ";
     print_ireg_capasm p rs;
     Format.fprintf p "@ ";
     print_ireg_capasm p ra;
     Format.fprintf p "@ (";
     print_offset_capasm p ofs;
     Format.fprintf p ")@ ";
  | CapAsm.Psd (rs, ra, ofs) ->
     Format.fprintf p "Psd@ ";
     print_ireg_capasm p rs;
     Format.fprintf p "@ ";
     print_ireg_capasm p ra;
     Format.fprintf p "@ (";
     print_offset_capasm p ofs;
     Format.fprintf p ")@ "
  (* TODO: this instruction is not defined in CapAsm *)
  (*   | CapAsm.Ploadsymbol_high (rd, s, ofs) ->
       Format.fprintf p "Ploadsymbol_high@ ";
       print_ireg_capasm p rd;
       Format.fprintf p "@ ";
       print_ident_capasm p s;
       Format.fprintf p "@ ";
       print_Z_capasm p ofs;
       Format.fprintf p "@ "; *)

  | CapAsm.Pmv (d, s) ->
     Format.fprintf p "Pmv@ ";
     print_creg_capasm p d;
     Format.fprintf p "@ ";
     print_creg_capasm p s
  | CapAsm.Psltiw (d, s, i) -> Format.fprintf p "TODO: __Psltiw__"
  | CapAsm.Psltiuw (d, s, i) -> Format.fprintf p "TODO: __Psltiuw__"
  | CapAsm.Pandiw (d, s, i) -> Format.fprintf p "TODO: __Pandiw__"
  | CapAsm.Poriw (d, s, i) -> Format.fprintf p "TODO: __Poriw__"
  | CapAsm.Pxoriw (d, s, i) -> Format.fprintf p "TODO: __Pxoriw__"
  | CapAsm.Pslliw (d, s, i) -> Format.fprintf p "TODO: __Pslliw__"
  | CapAsm.Psrliw (d, s, i) -> Format.fprintf p "TODO: __Psrliw__"
  | CapAsm.Psraiw (d, s, i) -> Format.fprintf p "TODO: __Psraiw__"
  | CapAsm.Pluiw (d, i) -> Format.fprintf p "TODO: __Pluiw__"
  | CapAsm.Paddw (d, s1, s2) ->
     Format.fprintf p "Paddw@ ";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg0_capasm p s1;
     Format.fprintf p "@ ";
     print_ireg0_capasm p s2
  | CapAsm.Psubw (d, s1, s2) -> Format.fprintf p "TODO: __Psubw__"
  | CapAsm.Pmulw (d, s1, s2) -> Format.fprintf p "TODO: __Pmulw__"
  | CapAsm.Pmulhw (d, s1, s2) -> Format.fprintf p "TODO: __Pmulhw__"
  | CapAsm.Pmulhuw (d, s1, s2) -> Format.fprintf p "TODO: __Pmulhuw__"
  | CapAsm.Pdivw (d, s1, s2) -> Format.fprintf p "TODO: __Pdivw__"
  | CapAsm.Pdivuw (d, s1, s2) -> Format.fprintf p "TODO: __Pdivuw__"
  | CapAsm.Premw (d, s1, s2) -> Format.fprintf p "TODO: __Premw__"
  | CapAsm.Premuw (d, s1, s2) -> Format.fprintf p "TODO: __Premuw__"
  | CapAsm.Psltw (d, s1, s2) -> Format.fprintf p "TODO: __Psltw__"
  | CapAsm.Psltuw (d, s1, s2) -> Format.fprintf p "TODO: __Psltuw__"
  | CapAsm.Pseqw (d, s1, s2) -> Format.fprintf p "TODO: __Pseqw__"
  | CapAsm.Psnew (d, s1, s2) -> Format.fprintf p "TODO: __Psnew__"
  | CapAsm.Pandw (d, s1, s2) -> Format.fprintf p "TODO: __Pandw__"
  | CapAsm.Porw (d, s1, s2) -> Format.fprintf p "TODO: __Porw__"
  | CapAsm.Pxorw (d, s1, s2) -> Format.fprintf p "TODO: __Pxorw__"
  | CapAsm.Psllw (d, s1, s2) -> Format.fprintf p "TODO: __Psllw__"
  | CapAsm.Psrlw (d, s1, s2) -> Format.fprintf p "TODO: __Psrlw__"
  | CapAsm.Psraw (d, s1, s2) -> Format.fprintf p "TODO: __Psraw__"
  | CapAsm.Paddil (d, s, i) ->
     Format.fprintf p "Paddil@ ";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg0_capasm p s;
     Format.fprintf p "@ ";
     print_Z_capasm p i
  | CapAsm.Psltil (d, s, i) -> Format.fprintf p "TODO: __Psltil__"
  | CapAsm.Psltiul (d, s, i) -> Format.fprintf p "TODO: __Psltiul__"
  | CapAsm.Pandil (d, s, i) -> Format.fprintf p "TODO: __Pandil__"
  | CapAsm.Poril (d, s, i) -> Format.fprintf p "TODO: __Poril__"
  | CapAsm.Pxoril (d, s, i) -> Format.fprintf p "TODO: __Pxoril__"
  | CapAsm.Psllil (d, s, i) -> Format.fprintf p "TODO: __Psllil__"
  | CapAsm.Psrlil (d, s, i) -> Format.fprintf p "TODO: __Psrlil__"
  | CapAsm.Psrail (d, s, i) -> Format.fprintf p "TODO: __Psrail__"
  | CapAsm.Pluil (d, i) -> Format.fprintf p "TODO: __Pluil__"
  | CapAsm.Paddl (d, s1, s2) -> Format.fprintf p "TODO: __Paddl__"
  | CapAsm.Psubl (d, s1, s2) -> Format.fprintf p "TODO: __Psubl__"
  | CapAsm.Pmull (d, s1, s2) -> Format.fprintf p "TODO: __Pmull__"
  | CapAsm.Pmulhl (d, s1, s2) -> Format.fprintf p "TODO: __Pmulhl__"
  | CapAsm.Pmulhul (d, s1, s2) -> Format.fprintf p "TODO: __Pmulhul__"
  | CapAsm.Pdivl (d, s1, s2) -> Format.fprintf p "TODO: __Pdivl__"
  | CapAsm.Pdivul (d, s1, s2) -> Format.fprintf p "TODO: __Pdivul__"
  | CapAsm.Preml (d, s1, s2) -> Format.fprintf p "TODO: __Preml__"
  | CapAsm.Premul (d, s1, s2) -> Format.fprintf p "TODO: __Premul__"
  | CapAsm.Psltl (d, s1, s2) -> Format.fprintf p "TODO: __Psltl__"
  | CapAsm.Psltul (d, s1, s2) -> Format.fprintf p "TODO: __Psltul__"
  | CapAsm.Pseql (d, s1, s2) -> Format.fprintf p "TODO: __Pseql__"
  | CapAsm.Psnel (d, s1, s2) -> Format.fprintf p "TODO: __Psnel__"
  | CapAsm.Pandl (d, s1, s2) -> Format.fprintf p "TODO: __Pandl__"
  | CapAsm.Porl (d, s1, s2) -> Format.fprintf p "TODO: __Porl__"
  | CapAsm.Pxorl (d, s1, s2) -> Format.fprintf p "TODO: __Pxorl__"
  | CapAsm.Pslll (d, s1, s2) -> Format.fprintf p "TODO: __Pslll__"
  | CapAsm.Psrll (d, s1, s2) -> Format.fprintf p "TODO: __Psrll__"
  | CapAsm.Psral (d, s1, s2) -> Format.fprintf p "TODO: __Psral__"
  | CapAsm.Pcvtl2w (d, s) -> Format.fprintf p "TODO: __Pcvtl2w__"
  | CapAsm.Pcvtw2l (r) -> Format.fprintf p "TODO: __Pcvtw2l__"
  | CapAsm.Pj_l l ->
     Format.fprintf p "Pj_l@ ";
     print_ident_capasm p l
  | CapAsm.Pj_r r ->
     Format.fprintf p "Pj_r@ ";
     print_ireg_capasm p r
  | CapAsm.Pjal_r (r, sg, b) ->
     Format.fprintf p "Pjal_r@ ";
     print_ireg_capasm p r;
     Format.fprintf p "@ ";
     (* TODO: fix the clashing imports from CapAST and AST to print the signature here *)
     (* print_signature_capasm p sg; *)
     Format.fprintf p "@ ";
     print_bool_capasm p b
  | CapAsm.PCjal_r (r, s, _, _) -> Format.fprintf p "TODO: __PCjal_r__"
  | CapAsm.PCinvoke (r, s, b) ->
     Format.fprintf p "PCinvoke@ ";
     print_ireg0_capasm p r;
     Format.fprintf p "@ ";
     print_ireg0_capasm p s;
     Format.fprintf p "@ ";
     print_bool_capasm p b
  | CapAsm.Pbeqw (s1, s2, l) ->
     Format.fprintf p "Pbeqw@ ";
     print_ireg0_capasm p s1;
     Format.fprintf p "@ ";
     print_ireg0_capasm p s2
  | CapAsm.Pbnew (s1, s2, l) -> Format.fprintf p "TODO: __Pbnew__"
  | CapAsm.Pbltw (s1, s2, l) -> Format.fprintf p "TODO: __Pbltw__"
  | CapAsm.Pbltuw (s1, s2, l) -> Format.fprintf p "TODO: __Pbltuw__"
  | CapAsm.Pbgew (s1, s2, l) -> Format.fprintf p "TODO: __Pbgew__"
  | CapAsm.Pbgeuw (s1, s2, l) -> Format.fprintf p "TODO: __Pbgeuw__"
  | CapAsm.Pbeql (s1, s2, l) -> Format.fprintf p "TODO: __Pbeql__"
  | CapAsm.Pbnel (s1, s2, l) -> Format.fprintf p "TODO: __Pbnel__"
  | CapAsm.Pbltl (s1, s2, l) -> Format.fprintf p "TODO: __Pbltl__"
  | CapAsm.Pbltul (s1, s2, l) -> Format.fprintf p "TODO: __Pbltul__"
  | CapAsm.Pbgel (s1, s2, l) -> Format.fprintf p "TODO: __Pbgel__"
  | CapAsm.Pbgeul (s1, s2, l) -> Format.fprintf p "TODO: __Pbgeul__"
  | CapAsm.Plb (d, a, ofs, priv) -> Format.fprintf p "TODO: __Plb__"
  | CapAsm.Plbu (d, a, ofs, priv) -> Format.fprintf p "TODO: __Plbu__"
  | CapAsm.Plh (d, a, ofs, priv) -> Format.fprintf p "TODO: __Plh__"
  | CapAsm.Plhu (d, a, ofs, priv) -> Format.fprintf p "TODO: __Plhu__"
  | CapAsm.Plw (d, a, ofs, priv) -> Format.fprintf p "TODO: __Plw__"
  | CapAsm.Plw_a (d, a, ofs, priv) -> Format.fprintf p "TODO: __Plw_a__"
  | CapAsm.Pld_a (d, a, ofs, priv) -> Format.fprintf p "TODO: __Pld_a__"
  | CapAsm.Plcw (d, a, ofs, priv) -> Format.fprintf p "TODO: __Plcw__"
  | CapAsm.Plcd (d, a, ofs, priv) -> Format.fprintf p "TODO: __Plcd__"
  | CapAsm.Plcd_a (d, a, ofs, priv) -> Format.fprintf p "TODO: __Plcd_a__"
  | CapAsm.Psb (s, a, ofs) -> Format.fprintf p "TODO: __Psb__"
  | CapAsm.Psh (s, a, ofs) -> Format.fprintf p "TODO: __Psh__"
  | CapAsm.Psw_a (s, a, ofs) -> Format.fprintf p "TODO: __Psw_a__"
  | CapAsm.Psd_a (s, a, ofs) -> Format.fprintf p "TODO: __Psd_a__"
  | CapAsm.Pscw (s, a, ofs) -> Format.fprintf p "TODO: __Pscw__"
  | CapAsm.Pscd (s, a, ofs) -> Format.fprintf p "TODO: __Pscd__"
  | CapAsm.Pscd_a (s, a, ofs) -> Format.fprintf p "TODO: __Pscd_a__"
  | CapAsm.PClb (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PClb__"
  | CapAsm.PClbu (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PClbu__"
  | CapAsm.PClh (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PClh__"
  | CapAsm.PClhu (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PClhu__"
  | CapAsm.PClw (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PClw__"
  | CapAsm.PClw_a (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PClw_a__"
  | CapAsm.PCld (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PCld__"
  | CapAsm.PCld_a (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PCld_a__"
  | CapAsm.PClwc (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PClwc__"
  | CapAsm.PClcd (d, a, ofs, h, priv) ->
     Format.fprintf p "PClcd@ ";
     print_ireg_capasm p a;
     Format.fprintf p "@ ";
     print_ireg_capasm p a;
     Format.fprintf p "@ ";
     print_offset_capasm p ofs;
     Format.fprintf p "@ ";
     print_bool_capasm p h;
     Format.fprintf p "@ ";
     print_bool_capasm p priv
  | CapAsm.PClcd_a (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PClcd_a__"
  | CapAsm.PCsb (s, a, ofs, h) -> Format.fprintf p "TODO: __PCsb__"
  | CapAsm.PCsh (s, a, ofs, h) -> Format.fprintf p "TODO: __PCsh__"
  | CapAsm.PCsw (s, a, ofs, h) -> Format.fprintf p "TODO: __PCsw__"
  | CapAsm.PCsw_a (s, a, ofs, h) -> Format.fprintf p "TODO: __PCsw_a__"
  | CapAsm.PCsd (s, a, ofs, h) ->
     Format.fprintf p "PCsd@ ";
     print_ireg_capasm p s;
     Format.fprintf p "@ ";
     print_ireg_capasm p a;
     Format.fprintf p "@ ";
     print_offset_capasm p ofs;
     Format.fprintf p "@ ";
     print_bool_capasm p h;
  | CapAsm.PCsd_a (s, a, ofs, h) -> Format.fprintf p "TODO: __PCsd_a__"
  | CapAsm.PCscw (s, a, ofs, h) -> Format.fprintf p "TODO: __PCscw__"
  | CapAsm.PCscd (s, a, ofs, h) -> Format.fprintf p "TODO: __PCscd__"
  | CapAsm.PCscd_a (s, a, ofs, h) -> Format.fprintf p "TODO: __PCscd_a__"
  | CapAsm.PCfls (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PCfls__"
  | CapAsm.PCfss (s, a, ofs, h) -> Format.fprintf p "TODO: __PCfss__"
  | CapAsm.PCfld (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PCfld__"
  | CapAsm.PCfld_a (d, a, ofs, h, priv) -> Format.fprintf p "TODO: __PCfld_a__"
  | CapAsm.PCfsd (s, a, ofs, h) -> Format.fprintf p "TODO: __PCfsd__"
  | CapAsm.PCfsd_a (s, a, ofs, h) -> Format.fprintf p "TODO: __PCfsd_a__"
  | CapAsm.PCUlb (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUlb__"
  | CapAsm.PCUlbu (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUlbu__"
  | CapAsm.PCUlh (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUlh__"
  | CapAsm.PCUlhu (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUlhu__"
  | CapAsm.PCUlw (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUlw__"
  | CapAsm.PCUlw_a (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUlw_a__"
  | CapAsm.PCUld (d, a, rofs, ofs, h, priv) ->
     Format.fprintf p "PCUld@ ";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg_capasm p a;
     Format.fprintf p "@ ";
     print_ireg_capasm p rofs;
     Format.fprintf p "@ ";
     print_offset_capasm p ofs;
     Format.fprintf p "@ ";
     print_bool_capasm p h;
     Format.fprintf p "@ ";
     print_bool_capasm p priv
  | CapAsm.PCUld_a (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUld_a__"
  | CapAsm.PCUlwc (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUlwc__"
  | CapAsm.PCUlcd (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUlcd__"
  | CapAsm.PCUlcd_a (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUlcd_a__"
  | CapAsm.PCUsb (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUsb__"
  | CapAsm.PCUsh (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUsh__"
  | CapAsm.PCUsw (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUsw__"
  | CapAsm.PCUsw_a (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUsw_a__"
  | CapAsm.PCUsd (s, a, rofs, ofs, h) ->
     Format.fprintf p "PCUsd@ ";
     print_ireg_capasm p s;
     Format.fprintf p "@ ";
     print_ireg_capasm p a;
     Format.fprintf p "@ ";
     print_ireg_capasm p rofs;
     Format.fprintf p "@ ";
     print_offset_capasm p ofs;
     Format.fprintf p "@ ";
     print_bool_capasm p h
  | CapAsm.PCUsd_a (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUsd_a__"
  | CapAsm.PCUscw (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUscw__"
  | CapAsm.PCUscd (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUscd__"
  | CapAsm.PCUscd_a (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUscd_a__"
  | CapAsm.PCUfls (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUfls__"
  | CapAsm.PCUfss (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUfss__"
  | CapAsm.PCUfld (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUfld__"
  | CapAsm.PCUfld_a (d, a, rofs, ofs, h, priv) -> Format.fprintf p "TODO: __PCUfld_a__"
  | CapAsm.PCUfsd (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUfsd__"
  | CapAsm.PCUfsd_a (s, a, rofs, ofs, h) -> Format.fprintf p "TODO: __PCUfsd_a__"
  | CapAsm.PCgp (d, s) -> Format.fprintf p "TODO: __PCgp__"
  | CapAsm.PCgt (d, s) -> Format.fprintf p "TODO: __PCgt__"
  | CapAsm.PCgb_h (d, s) -> Format.fprintf p "TODO: __PCgb_h__"
  | CapAsm.PCge_h (d, s) -> Format.fprintf p "TODO: __PCge_h__"
  | CapAsm.PCgb_s (d, s) ->
     Format.fprintf p "PCgb_s@ ";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg_capasm p s
  | CapAsm.PCge_s (d, s) -> Format.fprintf p "TODO: __PCge_s__"
  | CapAsm.PCgg (d, s) -> Format.fprintf p "TODO: __PCgg__"
  | CapAsm.PCgs (d, s) ->
     Format.fprintf p "PCgs@ ";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg_capasm p s
  | CapAsm.PCga_h (d, s) -> Format.fprintf p "TODO: __PCga_h__"
  | CapAsm.PCga_s (d, s) -> Format.fprintf p "TODO: __PCga_s__"
  | CapAsm.PCgl_h (d, s) -> Format.fprintf p "TODO: __PCgl_h__"
  | CapAsm.PCgl_s (d, s) ->
     Format.fprintf p "PCgl_s";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg_capasm p s
  | CapAsm.PCseal (d, r1, r2) -> Format.fprintf p "TODO: __PCseal__"
  | CapAsm.PCunseal (d, r1, r2) -> Format.fprintf p "TODO: __PCunseal__"
  | CapAsm.PCpermand (d, r1, r2) ->
     Format.fprintf p "PCpermand@ ";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg_capasm p r1;
     Format.fprintf p "@ ";
     print_ireg_capasm p r2
  | CapAsm.PCsaddr_w (d, r1, r2) ->
     Format.fprintf p "PCsaddr_w@ ";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg_capasm p r1;
     Format.fprintf p "@ ";
     print_ireg_capasm p r2
  | CapAsm.PCsaddr_l (d, r1, r2) -> Format.fprintf p "TODO: __PCsaddr_l__"
  | CapAsm.PCiaddr_w (d, r1, r2) -> Format.fprintf p "TODO: __PCiaddr_w__"
  | CapAsm.PCiaddr_l (d, r1, r2) -> Format.fprintf p "TODO: __PCiaddr_l__"
  | CapAsm.PCiaddr_il (d, r1, imm) ->
     Format.fprintf p "PCiaddr_il@ ";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg0_capasm p r1;
     Format.fprintf p "@ ";
     print_Z_capasm p imm
  | CapAsm.PCiaddr_iw (d, r1, imm) -> Format.fprintf p "TODO: __PCiaddr_iw__"
  | CapAsm.PCsbase (d, r1, r2) -> Format.fprintf p "TODO: __PCsbase__"
  | CapAsm.PCsbase_il (d, r1, imm) -> Format.fprintf p "TODO: __PCsbase_il__"
  | CapAsm.PCsbase_iw (d, r1, imm) -> Format.fprintf p "TODO: __PCsbase_iw__"
  | CapAsm.PCCseal (d, r1, r2) -> Format.fprintf p "TODO: __PCCseal__"
  | CapAsm.PCseal_e (d, r) -> Format.fprintf p "TODO: __PCseal_e__"
  | CapAsm.PCpromote (d, r1) ->
     Format.fprintf p "PCpromote@ ";
     print_ireg_capasm p d;
     Format.fprintf p "@ ";
     print_ireg_capasm p r1
  | CapAsm.PCtoPtr_h (d, r1, r2) -> Format.fprintf p "TODO: __PCtoPtr_h__"
  | CapAsm.PCsub_h (d, r1, r2) -> Format.fprintf p "TODO: __PCsub_h__"
  | CapAsm.PCtoPtr_s (d, r1, r2) -> Format.fprintf p "TODO: __PCtoPtr_s__"
  | CapAsm.PCsub_s (d, r1, r2) -> Format.fprintf p "TODO: __PCsub_s__"
  | CapAsm.PCUtoPtr_h (d, r1, r2) -> Format.fprintf p "TODO: __PCUtoPtr_h__"
  | CapAsm.PCUtoPtr_s (d, r1, r2) -> Format.fprintf p "TODO: __PCUtoPtr_s__"
  | CapAsm.PCsubset (d, r1, r2) -> Format.fprintf p "TODO: __PCsubset__"
  | CapAsm.PCeex (d, r1, r2) -> Format.fprintf p "TODO: __PCeex__"
  | CapAsm.PCCclear imm -> Format.fprintf p "TODO: __PCCclear__"
  | CapAsm.PCCclearf imm -> Format.fprintf p "TODO: __PCCclearf__"
  | CapAsm.Pfmv (d, s) -> Format.fprintf p "TODO: __Pfmv__"
  | CapAsm.Pfls (d, a, ofs, b) -> Format.fprintf p "TODO: __Pfls__"
  | CapAsm.Pfss (s, a, ofs) -> Format.fprintf p "TODO: __Pfss__"
  | CapAsm.Pfnegs (d, s) -> Format.fprintf p "TODO: __Pfnegs__"
  | CapAsm.Pfabss (d, s) -> Format.fprintf p "TODO: __Pfabss__"
  | CapAsm.Pfadds (d, s1, s2) -> Format.fprintf p "TODO: __Pfadds__"
  | CapAsm.Pfsubs (d, s1, s2) -> Format.fprintf p "TODO: __Pfsubs__"
  | CapAsm.Pfmuls (d, s1, s2) -> Format.fprintf p "TODO: __Pfmuls__"
  | CapAsm.Pfdivs (d, s1, s2) -> Format.fprintf p "TODO: __Pfdivs__"
  | CapAsm.Pfeqs (d, s1, s2) -> Format.fprintf p "TODO: __Pfeqs__"
  | CapAsm.Pflts (d, s1, s2) -> Format.fprintf p "TODO: __Pflts__"
  | CapAsm.Pfles (d, s1, s2) -> Format.fprintf p "TODO: __Pfles__"
  | CapAsm.Pfcvtws (d, s) -> Format.fprintf p "TODO: __Pfcvtws__"
  | CapAsm.Pfcvtwus (d, s) -> Format.fprintf p "TODO: __Pfcvtwus__"
  | CapAsm.Pfcvtsw (d, s) -> Format.fprintf p "TODO: __Pfcvtsw__"
  | CapAsm.Pfcvtswu (d, s) -> Format.fprintf p "TODO: __Pfcvtswu__"
  | CapAsm.Pfcvtls (d, s) -> Format.fprintf p "TODO: __Pfcvtls__"
  | CapAsm.Pfcvtlus (d, s) -> Format.fprintf p "TODO: __Pfcvtlus__"
  | CapAsm.Pfcvtsl (d, s) -> Format.fprintf p "TODO: __Pfcvtsl__"
  | CapAsm.Pfcvtslu (d, s) -> Format.fprintf p "TODO: __Pfcvtslu__"
(* HOTFIX: These are commented out, because OCaml only supports up to 246 non-constant constructors! *)
(*
  | CapAsm.Pfld (d, a, ofs, b) -> Format.fprintf p "TODO: __Pfld__"
  | CapAsm.Pfld_a (d, a, ofs, b) -> Format.fprintf p "TODO: __Pfld_a__"
  | CapAsm.Pfsd (s, a, ofs) -> Format.fprintf p "TODO: __Pfsd__"
  | CapAsm.Pfsd_a (s, a, ofs) -> Format.fprintf p "TODO: __Pfsd_a__"
  | CapAsm.Pfnegd (d, s) -> Format.fprintf p "TODO: __Pfnegd__"
  | CapAsm.Pfabsd (d, s) -> Format.fprintf p "TODO: __Pfabsd__"
  | CapAsm.Pfaddd (d, s1, s2) -> Format.fprintf p "TODO: __Pfaddd__"
  | CapAsm.Pfsubd (d, s1, s2) -> Format.fprintf p "TODO: __Pfsubd__"
  | CapAsm.Pfmuld (d, s1, s2) -> Format.fprintf p "TODO: __Pfmuld__"
  | CapAsm.Pfdivd (d, s1, s2) -> Format.fprintf p "TODO: __Pfdivd__"
  | CapAsm.Pfeqd (d, s1, s2) -> Format.fprintf p "TODO: __Pfeqd__"
  | CapAsm.Pfltd (d, s1, s2) -> Format.fprintf p "TODO: __Pfltd__"
  | CapAsm.Pfled (d, s1, s2) -> Format.fprintf p "TODO: __Pfled__"
  | CapAsm.Pfcvtwd (d, s) -> Format.fprintf p "TODO: __Pfcvtwd__"
  | CapAsm.Pfcvtwud (d, s) -> Format.fprintf p "TODO: __Pfcvtwud__"
  | CapAsm.Pfcvtdw (d s) -> Format.fprintf p "TODO: __Pfcvtdw__"
  | CapAsm.Pfcvtdwu (d, s) -> Format.fprintf p "TODO: __Pfcvtdwu__"
  | CapAsm.Pfcvtld (d, s) -> Format.fprintf p "TODO: __Pfcvtld__"
  | CapAsm.Pfcvtlud (d, s) -> Format.fprintf p "TODO: __Pfcvtlud__"
  | CapAsm.Pfcvtdl (d s) -> Format.fprintf p "TODO: __Pfcvtdl__"
  | CapAsm.Pfcvtdlu (d, s) -> Format.fprintf p "TODO: __Pfcvtdlu__"
  | CapAsm.Pfcvtds (d, s) -> Format.fprintf p "TODO: __Pfcvtds__"
  | CapAsm.Pfcvtsd (d, s) -> Format.fprintf p "TODO: __Pfcvtsd__"
*)
  | CapAsm.Plabel lbl ->
     Format.fprintf p "Plabel@ ";
     print_ident_capasm p lbl;
  | CapAsm.Pptrbr (r, lbl1, lbl2) ->
     Format.fprintf p "Pptrbr@ ";
     print_ireg_capasm p r;
     Format.fprintf p "@ ";
     print_ident_capasm p lbl1;
     Format.fprintf p "@ ";
     print_ident_capasm p lbl2
  | CapAsm.Ploadli (rd, i) -> Format.fprintf p "TODO: __Ploadli__"
  | CapAsm.Ploadfi (rd, f) -> Format.fprintf p "TODO: __Ploadfi__"
  | CapAsm.Ploadsi (rd, f) -> Format.fprintf p "TODO: __Ploadsi__"
  | CapAsm.Pbtbl (r, tbl) -> Format.fprintf p "TODO: __Pbtbl__"
  | CapAsm.Pbuiltin (ef, args, res) -> Format.fprintf p "TODO: __Pbuiltin__"
  | CapAsm.Pfail -> Format.fprintf p "TODO: __Pfail__"
  | CapAsm.PCloadtag (_, _) -> Format.fprintf p "TODO: __PCloadtag__"
  | CapAsm.Pfence -> Format.fprintf p "TODO: __ Pfence__"
  | CapAsm.Pfmvxs (_, _) -> Format.fprintf p "TODO: __Pfence__"
  | CapAsm.Pfmvxd (_, _) -> Format.fprintf p "TODO: __Pfmvxd__"
  | CapAsm.Pfmins (_, _, _) -> Format.fprintf p "TODO: __Pfmins__"
  | CapAsm.Pfmaxs (_, _, _) -> Format.fprintf p "TODO: __Pfmaxs__"
  | CapAsm.Pfsqrts (_, _) -> Format.fprintf p "TODO: __Pfsqrts__"
  | CapAsm.Pfmadds (_, _, _, _) -> Format.fprintf p "TODO: __Pfmadds__"
  | CapAsm.Pfmsubs (_, _, _, _) -> Format.fprintf p "TODO: __Pfmsubs__"
  | CapAsm.Pfnmadds (_, _, _, _) -> Format.fprintf p "TODO: __Pfnmadds__"
  | CapAsm.Pfnmsubs (_, _, _, _) -> Format.fprintf p "TODO: __Pfnmsubs__"
(* HOTFIX: These are commented out, because OCaml only supports up to 246 non-constant constructors! *)
(*
  | CapAsm.Pfmind (_, _, _) -> Format.fprintf p "TODO: __Pfmind__"
  | CapAsm.Pfmaxd (_, _, _) -> Format.fprintf p "TODO: __Pfmaxd__"
  | CapAsm.Pfsqrtd (_, _) -> Format.fprintf p "TODO: __Pfsqrtd__"
  | CapAsm.Pfmaddd (_, _, _, _) -> Format.fprintf p "TODO: __Pfmaddd__"
  | CapAsm.Pfmsubd (_, _, _, _) -> Format.fprintf p "TODO: __Pfmsubd__"
  | CapAsm.Pfnmaddd (_, _, _, _) -> Format.fprintf p "TODO: __Pfnmaddd__"
  | CapAsm.Pfnmsubd (_, _, _, _) -> Format.fprintf p "TODO: __Pfnmsubd__"
*)
  | CapAsm.Pnop -> Format.fprintf p "TODO: __Pnop__"

let print_coq_function_asm p CapAsm.{ fn_comp; fn_sig; fn_code } =
  Format.fprintf p "{|@ fn_comp@ :=@ ";
  print_comp_capasm p fn_comp;
  Format.fprintf p ";@ fn_sig@ :=@ ";
  print_signature_capasm p fn_sig;
  Format.fprintf p ";@ fn_code@ :=@ ";
  print_list_capasm p print_instruction_capasm fn_code;
  Format.fprintf p "|}@,"

(* TODO cases *)
let print_external_function_asm p = function
  | EF_external (str, fsig) ->
     Format.fprintf p "EF_external@ (";
     print_string_capasm p str;
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
  print_comp_capasm p gvar_comp;
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
  let print_aux p' (comp_id, func) =
    Format.fprintf p' "(";
    print_comp_capasm p' comp_id;
    Format.fprintf p' "%ld" (P.to_int32 func)
  in
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

let print_program_capasm oc prog =
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

let destination : string option ref = ref None

let print_if prog =
   match !destination with
   | None -> ()
   | Some f ->
       let oc = open_out f in
       let _ = match CapAsmgen.transf_program prog with
         | Errors.Error msg -> Format.fprintf (Format.formatter_of_out_channel oc) "Fatal error: could not generate CapAsm for given program"
         | Errors.OK cap_asm_prog -> print_program_capasm oc cap_asm_prog
       in
       close_out oc