(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open AST
open Camlcoq
open PrintAsmaux
open Printf
open Sections
open TargetPrinter
open AisAnnot

module Printer(Target:TARGET) =
  struct

    let get_fun_addr name txt =
      let s = new_label ()
      and e = new_label () in
      Debug.add_fun_addr name txt (e,s);
      s,e

    let print_debug_label oc l =
      if !Clflags.option_g then
        fprintf oc "%a:\n" Target.label l
      else
        ()

    let print_location oc loc =
      if loc <> Cutil.no_loc then Target.print_file_line oc (fst loc) (snd loc)

    let splitlong b =
      if Archi.big_endian then
        (Int64.shift_right_logical b 32),
        (Int64.logand b 0xFFFFFFFFL)
      else
        (Int64.logand b 0xFFFFFFFFL),
        (Int64.shift_right_logical b 32)

    let emit_constants oc lit =
      if Hashtbl.length literal64_labels > 0 then begin
        Target.section oc (Sections.with_size 8 lit);
        Target.print_align oc 8;
        iter_literal64 (fun n lbl ->
            let (hi, lo) = splitlong n in
            fprintf oc "%a:	.long	0x%Lx, 0x%Lx\n" Target.label lbl hi lo)
      end;
      if Hashtbl.length literal32_labels > 0 then begin
        Target.section oc (Sections.with_size 4 lit);
        Target.print_align oc 4;
        iter_literal32 (fun n lbl ->
            fprintf oc "%a:	.long	0x%lx\n" Target.label lbl n);
      end;
      reset_literals ()

    let get_section_names name =
      match C2C.atom_sections name with
      | [t;l;j] -> (t, l, j)
      |    _    -> (Section_text, Section_literal 0, Section_jumptable)

    let print_function oc name fn =
      Hashtbl.clear current_function_labels;
      Debug.symbol_printed (extern_atom name);
      let (text, lit, jmptbl) = get_section_names name in
      Target.section oc text;
      let alignment =
        match !Clflags.option_falignfunctions with Some n -> n | None -> Target.default_falignment in
      Target.print_align oc alignment;
      if not (C2C.atom_is_static name) then
        fprintf oc "	.globl %a\n" Target.symbol name;
      Target.print_optional_fun_info oc;
      let s,e = if !Clflags.option_g then
        get_fun_addr name text
      else
        -1,-1 in
      print_debug_label oc s;
      fprintf oc "%a:\n" Target.symbol name;
      print_location oc (C2C.atom_location name);
      Target.cfi_startproc oc;
      Target.print_instructions oc fn;
      Target.cfi_endproc oc;
      print_debug_label oc e;
      Target.print_fun_info oc name;
      emit_constants oc lit;
      Target.print_jumptable oc jmptbl;
      if !Clflags.option_g then
        Hashtbl.iter (fun p i -> Debug.add_label name p i) current_function_labels

    let print_init oc init =
      let symbol_offset oc (symb,ofs) =
        Target.symbol oc symb;
        let ofs = camlint64_of_ptrofs ofs in
        if ofs <> 0L then fprintf oc " + %Ld" ofs in
      match init with
      | Init_int8 n ->
          fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
      | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
      | Init_int32 n ->
          fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
      | Init_int64 n ->
          let (hi, lo) = splitlong (camlint64_of_coqint n) in
          fprintf oc "	.long	0x%Lx, 0x%Lx\n" hi lo
      | Init_float32 n ->
          fprintf oc "	.long	0x%lx %s %.18g\n"
            (camlint_of_coqint (Floats.Float32.to_bits n))
            Target.comment (camlfloat_of_coqfloat32 n)
      | Init_float64 n ->
          let (hi, lo) =
            splitlong (camlint64_of_coqint (Floats.Float.to_bits n)) in
          fprintf oc "	.long	0x%Lx, 0x%Lx %s %.18g\n" hi lo
            Target.comment (camlfloat_of_coqfloat n)
      | Init_space n ->
          if Z.gt n Z.zero then
            fprintf oc "	.space	%s\n" (Z.to_string n)
      | Init_addrof(symb, ofs) ->
        fprintf oc "	%s	%a\n"
          Target.address
          symbol_offset (symb, ofs)


    let print_init_data oc name id =
      if Str.string_match PrintCsyntax.re_string_literal (extern_atom name) 0
          && List.for_all (function Init_int8 _ -> true | _ -> false) id
      then
        fprintf oc "	.ascii	\"%s\"\n" (PrintCsyntax.string_of_init id)
      else
        List.iter (print_init oc) id

    let print_var oc name v =
      match v.gvar_init with
      | [] -> ()
      | _  ->
          Debug.symbol_printed (extern_atom name);
          let sec =
            match C2C.atom_sections name with
            | [s] -> s
            |  _  -> Section_data Init
          and align =
            match C2C.atom_alignof name with
            | Some a -> a
            | None -> 8 in (* 8-alignment is a safe default *)
          let name_sec = Target.name_of_section sec in
          if name_sec <> "COMM" then begin
            fprintf oc "	%s\n" name_sec;
            Target.print_align oc align;
            if not (C2C.atom_is_static name) then
              fprintf oc "	.globl	%a\n" Target.symbol name;
            fprintf oc "%a:\n" Target.symbol name;
            print_init_data oc name v.gvar_init;
            Target.print_var_info oc name;
          end else
            let sz =
              match v.gvar_init with [Init_space sz] -> sz | _ -> assert false in
            Target.print_comm_symb oc sz name align

    let print_globdef oc (name,gdef) =
      match gdef with
      | Gfun (Internal code) ->
        if not (C2C.atom_is_iso_inline_definition name) then
          print_function oc name code
      | Gfun (External ef) ->   ()
      | Gvar v -> print_var oc name v

    let print_ais_annot oc =
      let annots = get_ais_annots () in
      if annots <> [] then begin
        Target.section oc Section_ais_annotation;
        let print_addr oc pp_addr addr =
          fprintf oc "	.byte 7,%d\n" (if Archi.ptr64 then 8 else 4);
          fprintf oc "	%s %a\n" Target.address pp_addr addr in
        let annot_part oc = function
          | AisAnnot.Label lbl  ->
            print_addr oc Target.label lbl
          | AisAnnot.Symbol symb ->
            print_addr oc Target.symbol symb
          | AisAnnot.String a -> fprintf oc "	.ascii %S\n" a in
        let annot oc str =
          List.iter (annot_part oc) str
        in
        List.iter (annot oc) annots
      end

    module DwarfTarget: DwarfTypes.DWARF_TARGET =
      struct
        let label = Target.label
        let section = Target.section
        let symbol = Target.symbol
        let comment = Target.comment
        let address = Target.address
      end

    module DebugPrinter = DwarfPrinter.DwarfPrinter (DwarfTarget)
  end

let print_program oc p =
  let module Target = (val (sel_target ()):TARGET) in
  let module Printer = Printer(Target) in
  Fileinfo.reset_filenames ();
  print_version_and_options oc Target.comment;
  Target.print_prologue oc;
  List.iter (Printer.print_globdef oc) p.prog_defs;
  Target.print_epilogue oc;
  Printer.print_ais_annot oc;
  if !Clflags.option_g then
    begin
      let atom_to_s s =
        let s = C2C.atom_sections s in
        match s with
        | [] -> Target.name_of_section Section_text
        | (Section_user (n,_,_))::_ -> n
        | a::_ ->
            Target.name_of_section a in
      match Debug.generate_debug_info atom_to_s (Target.name_of_section Section_text) with
      | None -> ()
      | Some db ->
          Printer.DebugPrinter.print_debug oc db
    end;
  Fileinfo.close_filenames ()

(* ... *)

(* module PrinterAsm(Target:TARGET) =
 *   struct *)

(* begin module contents *)

(* from TargetPrinter, internal *)
    (* let int_reg_num_name = function *)
    let int_reg_num_name r =
      Asm.(match r with
                     | X1  -> "x1"  | X2  -> "x2"  | X3  -> "x3"
      | X4  -> "x4"  | X5  -> "x5"  | X6  -> "x6"  | X7  -> "x7"
      | X8  -> "x8"  | X9  -> "x9"  | X10 -> "x10" | X11 -> "x11"
      | X12 -> "x12" | X13 -> "x13" | X14 -> "x14" | X15 -> "x15"
      | X16 -> "x16" | X17 -> "x17" | X18 -> "x18" | X19 -> "x19"
      | X20 -> "x20" | X21 -> "x21" | X22 -> "x22" | X23 -> "x23"
      | X24 -> "x24" | X25 -> "x25" | X26 -> "x26" | X27 -> "x27"
      | X28 -> "x28" | X29 -> "x29" | X30 -> "x30" | X31 -> "x31"
      )

let print_option_asm p f = function
  | Some x ->
      Format.fprintf p "Some@ ";
      f p x
  | None ->
      Format.fprintf p "None"

let print_list_asm p f xs =
  Format.fprintf p "@[(";
  List.iter (fun x -> f p x; Format.fprintf p "@ ::@ ") xs;
  Format.fprintf p "nil)@]"

let print_Z_asm p n =
  Format.fprintf p "%s" (Z.to_string n)

let print_float32_asm p n =
  Format.fprintf p "%.15Ff" (camlfloat_of_coqfloat32 n)
let print_float64_asm p n =
  Format.fprintf p "%.15F" (camlfloat_of_coqfloat n)

(* TODO to_string *)
let print_ident_asm p id =
  Format.fprintf p "%ld" (P.to_int32 id)


let string_of_ident_asm id =
  Int32.to_string (P.to_int32 id)

let print_comp_asm p c =
  match c with
  | COMP.Coq_bottom' -> Format.fprintf p "CompBottom"
  | COMP.Coq_top' -> Format.fprintf p "CompTop"
  | COMP.Comp id -> Format.fprintf p "Comp%ld" (P.to_int32 id)

let string_of_comp_asm c =
  match c with
  | COMP.Coq_bottom' -> "CompBottom"
  | COMP.Coq_top' -> "CompTop"
  | COMP.Comp id -> "Comp" ^ Int32.to_string (P.to_int32 id)

let print_string_asm p s =
  Format.fprintf p "\"%s\"%%string" (camlstring_of_coqstring s)

let print_typ_asm p = function
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

let print_rettype_asm p = function
  | Tret ty ->
      Format.fprintf p "Tret@ ";
      print_typ_asm p ty
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

let print_calling_convention_asm p AST.{ cc_vararg; cc_unproto; cc_structret } =
  Format.fprintf p "{|@ cc_vararg@ :=@ ";
  print_option_asm p print_Z_asm cc_vararg;
  Format.fprintf p ";@ cc_unproto@ :=@ ";
  Format.pp_print_bool p cc_unproto;
  Format.fprintf p ";@ cc_structret@ :=@ ";
  Format.pp_print_bool p cc_structret;
  Format.fprintf p "|}@,"

let print_signature_asm p AST.{ sig_args; sig_res; sig_cc } =
  Format.fprintf p "{|@ sig_args@ :=@ ";
  print_list_asm p print_typ_asm sig_args;
  Format.fprintf p ";@ sig_res@ :=@ ";
  print_rettype_asm p sig_res;
  Format.fprintf p ";@ sig_cc@ :=@ ";
  print_calling_convention_asm p sig_cc;
  Format.fprintf p "|}@,"

(* TODO parameterize on target, helpers hidden by module type *)
let print_ireg_asm p r =
  Format.fprintf p "%s" (String.uppercase_ascii (int_reg_num_name r))

let print_ireg0_asm p = function
  | Asm.X0 ->
      Format.fprintf p "X0";
  | Asm.X r ->
      Format.fprintf p "(X@ ";
      print_ireg_asm p r;
      Format.fprintf p ")@,"

let print_offset_asm p = function
  | Asm.Ofsimm ofs ->
      Format.fprintf p "Ofsimm@ ";
      print_Z_asm p ofs
  | Asm.Ofslow (id, ofs) ->
      Format.fprintf p "Ofslow@ (";
      print_ident_asm p id;
      Format.fprintf p ",@ ";
      print_Z_asm p ofs;
      Format.fprintf p ")@,"

(* TODO cases *)
(* TODO tuples *)
(* TODO offsets, smart parenthesis insertion *)
let print_instruction_asm p = function
  | Asm.Pallocframe (sz, pos) ->
      Format.fprintf p "Pallocframe@ ";
      print_Z_asm p sz;
      Format.fprintf p "@ ";
      (* TODO function *)
      print_Z_asm p pos;
  | Asm.Pfreeframe (sz, pos) ->
      Format.fprintf p "Pfreeframe@ ";
      print_Z_asm p sz;
      Format.fprintf p "@ ";
      print_Z_asm p pos
  | Asm.Paddiw (rd, rs, imm) ->
      Format.fprintf p "Paddiw@ ";
      print_ireg_asm p rd;
      Format.fprintf p "@ ";
      print_ireg0_asm p rs;
      Format.fprintf p "@ ";
      print_Z_asm p imm
  | Asm.Pj_r (r, sg, iscl) ->
      Format.fprintf p "Pj_r@ ";
      print_ireg_asm p r;
      Format.fprintf p "@ ";
      print_signature_asm p sg;
      Format.fprintf p "@ ";
      Format.pp_print_bool p iscl
  | Asm.Pld (rd, ra, ofs, priv) ->
      Format.fprintf p "Pld@ ";
      print_ireg_asm p rd;
      Format.fprintf p "@ ";
      print_ireg_asm p ra;
      Format.fprintf p "@ (";
      print_offset_asm p ofs;
      Format.fprintf p ")@ ";
      Format.pp_print_bool p priv;
      Format.fprintf p "@."
  | Asm.Psw (rs, ra, ofs) ->
      Format.fprintf p "Psw@ ";
      print_ireg_asm p rs;
      Format.fprintf p "@ ";
      print_ireg_asm p ra;
      Format.fprintf p "@ (";
      print_offset_asm p ofs;
      Format.fprintf p ")@ ";
  | Asm.Psd (rs, ra, ofs) ->
      Format.fprintf p "Psd@ ";
      print_ireg_asm p rs;
      Format.fprintf p "@ ";
      print_ireg_asm p ra;
      Format.fprintf p "@ (";
      print_offset_asm p ofs;
      Format.fprintf p ")@ ";
  | Asm.Ploadsymbol_high (rd, s, ofs) ->
      Format.fprintf p "Ploadsymbol_high@ ";
      print_ireg_asm p rd;
      Format.fprintf p "@ ";
      print_ident_asm p s;
      Format.fprintf p "@ ";
      print_Z_asm p ofs;
      Format.fprintf p "@ ";
  | _ ->
      Format.fprintf p "<instr>"

let print_coq_function_asm p Asm.{ fn_comp; fn_sig; fn_code } =
  Format.fprintf p "{|@ fn_comp@ :=@ ";
  print_comp_asm p fn_comp;
  Format.fprintf p ";@ fn_sig@ :=@ ";
  print_signature_asm p fn_sig;
  Format.fprintf p ";@ fn_code@ :=@ ";
  print_list_asm p print_instruction_asm fn_code;
  Format.fprintf p "|}@,"

(* TODO cases *)
let print_external_function_asm p = function
  | EF_external (str, fsig) ->
      Format.fprintf p "EF_external@ (";
      print_string_asm p str;
      Format.fprintf p ",@ ";
      print_signature_asm p fsig;
      Format.fprintf p ")"
  | EF_builtin (str, fsig) ->
      Format.fprintf p "EF_builtin@ (";
      print_string_asm p str;
      Format.fprintf p ",@ ";
      print_signature_asm p fsig;
      Format.fprintf p ")"
  | EF_runtime (str, fsig) ->
      Format.fprintf p "EF_runtime@ (";
      print_string_asm p str;
      Format.fprintf p ",@ ";
      print_signature_asm p fsig;
      Format.fprintf p ")"
  (* | _ -> *)
  (*     failwith "unimplemented external function" *)
  | EF_vload chunk ->
      Format.fprintf p "EF_vload _"
  | EF_vstore chunk ->
      Format.fprintf p "EF_vstore _"
  | EF_malloc ->
      Format.fprintf p "EF_malloc _"
  | EF_free ->
      Format.fprintf p "EF_free _"
  | EF_memcpy (n1, n2) ->
      Format.fprintf p "EF_memcpy _"
  | EF_annot (lvl, str, tys) ->
      Format.fprintf p "EF_annot _"
  | EF_annot_val (lvl, str, tys) ->
      Format.fprintf p "EF_annot_val _"
  | EF_inline_asm (str, fsig, strs) ->
      Format.fprintf p "EF_inline_asm _"
  | EF_debug (lvl, id, tys) ->
      Format.fprintf p "EF_debug _"

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
      print_Z_asm p n
  | Init_int16 n ->
      Format.fprintf p "Init_int816@ ";
      print_Z_asm p n
  | Init_int32 n ->
      Format.fprintf p "Init_int32@ ";
      print_Z_asm p n
  | Init_int64 n ->
      Format.fprintf p "Init_int64@ ";
      print_Z_asm p n
  | Init_float32 n ->
      Format.fprintf p "Init_float32@ ";
      print_float32_asm p n
  | Init_float64 n ->
      Format.fprintf p "Init_float64@ ";
      print_float64_asm p n
  | Init_space z ->
      Format.fprintf p "Init_space@ ";
      print_Z_asm p z
  | Init_addrof _ ->
      Format.fprintf p "Init_addrof@ "
  (* | _ -> *)
  (*     failwith "unimplemented initial data" *)
  (* | Init_float32 of float32
   * | Init_float64 of float
   * | Init_space of coq_Z
   * | Init_addrof of ident * Ptrofs.int *)

let print_globvar_asm
  p AST.{ (* gvar_info; *) gvar_comp; gvar_init; gvar_readonly; gvar_volatile } =
  (* TODO unit *)
  Format.fprintf p "{|@ gvar_info@ := tt;@ ";
  Format.fprintf p ";@ gvar_comp@ :=@ ";
  print_comp_asm p gvar_comp;
  Format.fprintf p ";@ gvar_init@ :=@ ";
  print_list_asm p print_init_data_asm gvar_init;
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
  print_ident_asm p id;
  Format.fprintf p ",@ ";
  print_globdef_asm p glob;
  Format.fprintf p ")@]@,"

let rec string_of_exports (exports: (AST.COMP.compartment' * BinNums.positive list) list): string =
  match exports with
  | [] -> "]"
  | (c, []) :: exports' -> string_of_exports exports'
  | (c, f :: t) :: exports' ->
    let rest = string_of_exports ((c, t) :: exports') in
    (string_of_comp_asm c ^ " exports " ^ string_of_ident_asm f ^ (if rest = "]" then "]" else "\n" ^ rest))


let rec string_of_imports (imports: (AST.COMP.compartment' * (AST.COMP.compartment' * BinNums.positive) list) list): string =
  match imports with
  | [] -> "]"
  | (c, []) :: imports' -> string_of_imports imports'
  | (c, (c', f) :: t) :: imports' ->
    let rest = string_of_imports ((c, t) :: imports') in
    (string_of_comp_asm c ^ " imports " ^ string_of_ident_asm f ^ " from " ^ string_of_comp_asm c' ^ (if rest = "]" then "]" else "\n" ^ rest))

(* TODO list vs tree *)
let print_policy_asm p Policy.{ policy_export; policy_import } =
  let exports = AST.COMP.CompTree.elements policy_export in
  let imports = AST.COMP.CompTree.elements policy_import in
  Format.fprintf p "{| policy_export := [";
  Format.pp_print_string p (string_of_exports exports);
  (* TODO *)
  Format.fprintf p ";\n policy_import := [";
  Format.pp_print_string p (string_of_imports imports);
  (* TODO *)
  Format.fprintf p "|}@,"

let destination : string option ref = ref None

let print_program_asm oc prog =
  let p = Format.formatter_of_out_channel oc in
  Format.fprintf p "@[{|@.prog_defs :=@.@[";
  print_list_asm p print_prog_def_asm prog.prog_defs;
  Format.fprintf p "@];@.prog_public :=@.@[";
  print_list_asm p print_ident_asm prog.prog_public;
  Format.fprintf p "@];@.prog_main :=@.@[";
  print_ident_asm p prog.prog_main;
  Format.fprintf p "@];@.prog_pol :=@.@[";
  print_policy_asm p prog.prog_pol;
  Format.fprintf p "|}@]@."

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program_asm oc prog;
      close_out oc

(* end module contents *)

  (* end *)
