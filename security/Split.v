Require Import String.
Require Import Coqlib Maps Errors.
Require Import AST Linking Smallstep Events Behaviors.


Variant side := Left | Right.
Theorem side_eq: forall (x y: side), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition split := compartment -> side.

Class Unlinker (A: Type) {LA: Linker A} := {
  unlink: split -> A -> option (A * A);
  unlink_link: forall s x y z, unlink s z = Some (x, y) -> link x y = Some z; (* too strong. *)
}.

Class Internal_To_External (A: Type) {CA: has_comp A} := {
    internal_name: A -> string;
    internal_sig: A -> signature;
  }.
Definition internal_to_external {F: Type} {CF: has_comp F} {ITEF: Internal_To_External F}
                                (f: F) :=
  EF_external (internal_name f) (comp_of f) (internal_sig f).

Definition unlink_fundef {F: Type} {CF: has_comp F} {ITEF: Internal_To_External F}
  (s: split) (fd: fundef F) :=
  match fd with
  | Internal f =>
      match s (comp_of f) with
      | Left => Some (Internal f, External (internal_to_external f))
      | Right => Some (External (internal_to_external f), Internal f)
      end
  | External ef => Some (External ef, External ef)
  end.

Global Program Instance Unlinker_fundef (F: Type) {CF: has_comp F}
  {ITEF: Internal_To_External F} {LF: Linker F}: Unlinker (fundef F) := {
    unlink := unlink_fundef;
  }.
Next Obligation.
  Local Transparent Linker_fundef.
  unfold link, Linker_fundef. unfold link_fundef.
  Local Opaque Linker_fundef.
  destruct z; simpl in *.
  - destruct (s (comp_of f)) eqn:sf.
    + inv H. simpl.
      now rewrite peq_true.
    + inv H. simpl.
      now rewrite peq_true.
  - inv H.
    destruct (external_function_eq e e); now auto.
Defined.

Global Opaque Unlinker_fundef.

Definition unlink_varinit (s: split) (i: list init_data) :=
  match classify_init i with
  | Init_extern => Some (i, i)
  | Init_common sz => if Z.geb sz 0 then Some (i, i) else None
  | _ => None
  end.

Global Program Instance Unlinker_varinit: Unlinker (list init_data) :=
  { unlink := unlink_varinit; }.
Next Obligation.
  Local Transparent Linker_varinit.
  unfold link, Linker_varinit, link_varinit.
  Local Opaque Linker_varinit.
  unfold unlink_varinit in H.
  destruct (classify_init z); try now inv H; auto.
  destruct (sz >=? 0) eqn:sz_gt_0; inv H; auto.
  simpl. apply Z.geb_le in sz_gt_0.
  assert (R: sz = (Z.max sz 0 + 0)) by lia.
  now rewrite <- R, zeq_true.
Defined.

Definition unlink_vardef {V: Type} {LV: Linker V} {UV: Unlinker V} (s: split) (v: globvar V) :=
  match unlink s v.(gvar_info), unlink s v.(gvar_init) with
  | Some (info1, info2), Some (init1, init2) =>
      Some ({| gvar_info := info1;
              gvar_init := init1;
              gvar_comp := v.(gvar_comp);
              gvar_readonly := v.(gvar_readonly);
              gvar_volatile := v.(gvar_volatile) |},
          {| gvar_info := info2;
            gvar_init := init2;
            gvar_comp := v.(gvar_comp);
            gvar_readonly := v.(gvar_readonly);
            gvar_volatile := v.(gvar_volatile) |})
  | _, _ => None
  end.

Global Program Instance Unlinker_vardef (V: Type) {LV: Linker V} {UV: Unlinker V}: Unlinker (globvar V) :=
  { unlink := unlink_vardef; }.
Next Obligation.
  unfold unlink_vardef in H.
  destruct (unlink s (gvar_info z)) as [[] |] eqn:unlink_info; try congruence.
  destruct (unlink s (gvar_init z)) as [[] |] eqn:unlink_init; try congruence.
  inv H.
  Local Transparent Linker_vardef.
  unfold link, Linker_vardef, link_vardef. simpl.
  apply unlink_link in unlink_info. rewrite unlink_info.
  apply unlink_link in unlink_init. rewrite unlink_init.
  destruct (eq_compartment (gvar_comp z) (gvar_comp z)); try congruence;
    rewrite !eqb_reflx; now destruct z.
Defined.

Global Opaque Unlinker_vardef.

(** A trivial unlinker for the trivial var info [unit]. *)

Global Program Instance Unlinker_unit: Unlinker unit := {
  unlink := fun s x => Some (tt, tt);
}.
Next Obligation.
  destruct z; auto.
Defined.

Global Opaque Unlinker_unit.


Definition unlink_def {F V: Type} {LF: Linker F} {LV: Linker V} {UF: Unlinker F} {UV: Unlinker V}
  (s: split) (gd: globdef F V) :=
  match gd with
  | Gfun f => match unlink s f with
             | Some (f1, f2) => Some (Gfun f1, Gfun f2)
             | None => None
             end
  | Gvar v => match unlink s v with
             | Some (v1, v2) => Some (Gvar v1, Gvar v2)
             | None => None
             end
  end.

Global Program Instance Unlinker_def (F V: Type) {LF: Linker F} {LV: Linker V}
  {UF: Unlinker F} {UV: Unlinker V}: Unlinker (globdef F V) :=
  { unlink := unlink_def; }.
Next Obligation.
  Local Transparent Linker_def.
  unfold link, Linker_def, link_def.
  Local Opaque Linker_def.
  destruct z; simpl in H.
  - destruct (unlink s f) as [[] |] eqn:unlink_f; inv H.
    apply unlink_link in unlink_f; now rewrite unlink_f.
  - destruct (unlink s v) as [[] |] eqn:unlink_v; inv H.
    apply unlink_link in unlink_v; now rewrite unlink_v.
Defined.

Global Opaque Unlinker_def.

Section UNLINKER_PROG.

Context {F V: Type} {CF: has_comp F} {LF: Linker F} {LV: Linker V} {UF: Unlinker F} {UV: Unlinker V}.
Context (s: split) (p: program F V).

Let dm := prog_defmap p.

Definition unlink_prog_check (x: ident) (gd: globdef F V) :=
  match unlink s gd with
  | Some _ => true
  | None => false
  end.

Definition is_side (lr: side) (gd: globdef F V) :=
  side_eq (s (comp_of gd)) lr.

Definition unlink_prog :=
  Some ({| prog_public := p.(prog_public);
          prog_main   := p.(prog_main);
          prog_pol    := p.(prog_pol);
          prog_defs   := PTree.elements (PTree.filter1 (is_side Left) (PTree.map1 fst (PTree.map_filter1 (unlink s) dm)))
        |},
      {| prog_public := p.(prog_public);
        prog_main   := p.(prog_main);
        prog_pol    := p.(prog_pol);
        prog_defs   := PTree.elements (PTree.filter1 (is_side Right) (PTree.map1 snd (PTree.map_filter1 (unlink s) dm)))
      |}).

End UNLINKER_PROG.

Global Program Instance Unlinker_prog {F V: Type} {CF: has_comp F}
  {LF: Linker F} {LV: Linker V} {UF: Unlinker F} {UV: Unlinker V}: Unlinker (program F V) :=
  { unlink := unlink_prog }.
Next Obligation.
  Local Transparent Linker_prog.
  unfold link, Linker_prog.
  Local Opaque Linker_prog.
  rewrite link_prog_succeeds; simpl.
  - simpl. unfold prog_defmap. simpl.
    admit.
  - reflexivity.
  - admit.
  - now rewrite Policy.eqb_refl.
Admitted.
