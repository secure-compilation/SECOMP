(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Separate compilation and syntactic linking *)

Require Import Coq.Bool.Sumbool.
Require Import Coqlib Maps Errors AST.

(** This file follows "approach A" from the paper
       "Lightweight Verification of Separate Compilation"
    by Kang, Kim, Hur, Dreyer and Vafeiadis, POPL 2016. *)

Lemma sumbool_of_bool_true :
  forall (b: bool) (H : b = true),
    sumbool_of_bool b = left H.
Proof.
  intros b. unfold sumbool_of_bool.
  destruct b; try discriminate.
  intros H. f_equal.
  apply Zaux.eqbool_irrelevance.
Qed.

(** * Syntactic linking *)

(** A syntactic element [A] supports syntactic linking if it is equipped with the following:
- a partial binary operator [link] that produces the result of linking two elements,
  or fails if they cannot be linked (e.g. two definitions that are incompatible);
- a preorder [linkorder] with the meaning that [linkorder a1 a2] holds
  if [a2] can be obtained by linking [a1] with some other syntactic element.
*)

Class Linker (A: Type) := {
  link: A -> A -> option A;
  linkorder: A -> A -> Prop;
  linkorder_refl: forall x, linkorder x x;
  linkorder_trans: forall x y z, linkorder x y -> linkorder y z -> linkorder x z;
  link_linkorder: forall x y z, link x y = Some z -> linkorder x z /\ linkorder y z;
}.

(* has_comp_match *)
(* Class has_comp_linker {A: Type} {CA: has_comp A} (LA: Linker A) := *)
(*     link_comp : forall x y z, *)
(*       link x y = Some z -> *)
(*       ((comp_of x = bottom /\ comp_of y = comp_of z) \/ *)
(*        (comp_of y = bottom /\ comp_of x = comp_of z) \/ *)
(*        (comp_of x = comp_of z /\ comp_of y = comp_of z)). *)

(** Linking function definitions.  External functions of the [EF_external]
  kind can link with internal function definitions; the result of
  linking is the internal definition.  Two external functions can link
  if they are identical. *)

Definition link_fundef {F: Type} {CF: has_comp F} (fd1 fd2: fundef F) :=
  match fd1, fd2 with
  | Internal _, Internal _ => None
  | External ef1, External ef2 =>
      if external_function_eq ef1 ef2 then Some (External ef1) else None
  | Internal f, External ef =>
      match ef with
      | EF_external id sg => Some (Internal f)
      | _ => None
      end
  | External ef, Internal f =>
      match ef with
      | EF_external id sg => Some (Internal f)
      | _ => None
      end
  end.

Inductive linkorder_fundef {F: Type} {CF: has_comp F} : fundef F -> fundef F -> Prop :=
  | linkorder_fundef_refl: forall fd, linkorder_fundef fd fd
  | linkorder_fundef_ext_int: forall f id sg, linkorder_fundef (External (EF_external id sg)) (Internal f).

Global Program Instance Linker_fundef (F: Type) {CP: has_comp F}: Linker (fundef F) := {
  link := link_fundef;
  linkorder := linkorder_fundef
}.
Next Obligation.
  constructor.
Defined.
Next Obligation.
  inv H; inv H0; constructor.
Defined.
Next Obligation.
  destruct x, y; simpl in H.
+ discriminate.
+ destruct e; inv H.
  split; constructor.
+ destruct e; inv H.
  split; constructor.
+ destruct (external_function_eq e e0); inv H. split; constructor.
Defined.

(* Global Instance Linker_fundef_comp (F: Type) {CP: has_comp F}: *)
(*   has_comp_linker (Linker_fundef F). *)
(* Proof. *)
(*   unfold has_comp_linker, Linker_fundef. *)
(*   intros x y z H. *)
(*   unfold link, link_fundef in H. *)
(*   destruct x, y; try congruence. *)
(*   - destruct e; try congruence; right; left; split; auto with comps. *)
(*     inv H; auto with comps. *)
(*   - destruct e; try congruence; left; split; auto with comps. *)
(*     inv H; subst; auto with comps. *)
(*   - destruct (external_function_eq e e0); try congruence; right; right; split; auto with comps. *)
(*     inv H; subst; auto with comps. *)
(*     inv H; subst; auto with comps. *)
(* Qed. *)

Global Opaque Linker_fundef.

(** Linking variable initializers.  We adopt the following conventions:
- an "extern" variable has an empty initialization list;
- a "common" variable has an initialization list of the form [Init_space sz];
- all other initialization lists correspond to fully defined variables, neither "common" nor "extern".
*)

Inductive init_class : list init_data -> Type :=
  | Init_extern: init_class nil
  | Init_common: forall sz, init_class (Init_space sz :: nil)
  | Init_definitive: forall il, init_class il.

Definition classify_init (i: list init_data) : init_class i :=
  match i with
  | nil => Init_extern
  | Init_space sz :: nil => Init_common sz
  | i => Init_definitive i
  end.

Definition link_varinit (i1 i2: list init_data) :=
  match classify_init i1, classify_init i2 with
  | Init_extern, _ => Some i2
  | _, Init_extern => Some i1
  | Init_common sz1, _ => if zeq sz1 (init_data_list_size i2) then Some i2 else None
  | _, Init_common sz2 => if zeq sz2 (init_data_list_size i1) then Some i1 else None
  | _, _ => None
  end.

Inductive linkorder_varinit: list init_data -> list init_data -> Prop :=
  | linkorder_varinit_refl: forall il, linkorder_varinit il il
  | linkorder_varinit_extern: forall il, linkorder_varinit nil il
  | linkorder_varinit_common: forall sz il,
      il <> nil -> init_data_list_size il = sz ->
      linkorder_varinit (Init_space sz :: nil) il.

Global Program Instance Linker_varinit : Linker (list init_data) := {
  link := link_varinit;
  linkorder := linkorder_varinit
}.
Next Obligation.
  constructor.
Defined.
Next Obligation.
  inv H; inv H0; constructor; auto.
  congruence.
  simpl. generalize (init_data_list_size_pos z). extlia.
Defined.
Next Obligation.
  revert H; unfold link_varinit.
  destruct (classify_init x) eqn:Cx, (classify_init y) eqn:Cy; intros E; inv E; try (split; constructor; fail).
+ destruct (zeq sz (Z.max sz0 0 + 0)); inv H0.
  split; constructor. congruence. auto.
+ destruct (zeq sz (init_data_list_size il)); inv H0.
  split; constructor. red; intros; subst z; discriminate. auto.
+ destruct (zeq sz (init_data_list_size il)); inv H0.
  split; constructor. red; intros; subst z; discriminate. auto.
Defined.

Global Opaque Linker_varinit.

(** Linking variable definitions. *)

Definition link_vardef {V: Type} {LV: Linker V} (v1 v2: globvar V) :=
  match link v1.(gvar_info) v2.(gvar_info) with
  | None => None
  | Some info =>
      match link v1.(gvar_init) v2.(gvar_init) with
      | None => None
      | Some init =>
          if cp_eq_dec v1.(gvar_comp) v2.(gvar_comp)
             (* FIXME: use the meet or join!! (figure out which one makes sense) *)
          && eqb v1.(gvar_readonly) v2.(gvar_readonly)
          && eqb v1.(gvar_volatile) v2.(gvar_volatile)
          then Some {| gvar_info := info; gvar_init := init;
                       gvar_comp := v1.(gvar_comp);
                       gvar_readonly := v1.(gvar_readonly);
                       gvar_volatile := v1.(gvar_volatile) |}
          else None
      end
  end.

Inductive linkorder_vardef {V: Type} {LV: Linker V}: globvar V -> globvar V -> Prop :=
  | linkorder_vardef_intro: forall info1 info2 c i1 i2 ro vo,
      linkorder info1 info2 ->
      linkorder i1 i2 ->
      linkorder_vardef (mkglobvar info1 c i1 ro vo) (mkglobvar info2 c i2 ro vo).

Global Program Instance Linker_vardef (V: Type) {LV: Linker V}: Linker (globvar V) := {
  link := link_vardef;
  linkorder := linkorder_vardef
}.
Next Obligation.
  destruct x; constructor; apply linkorder_refl.
Defined.
Next Obligation.
  inv H; inv H0. constructor; eapply linkorder_trans; eauto.
Defined.
Next Obligation.
  revert H; unfold link_vardef.
  destruct x as [f1 c1 i1 r1 v1], y as [f2 c2 i2 r2 v2]; simpl.
  destruct (link f1 f2) as [f|] eqn:LF; try discriminate.
  destruct (link i1 i2) as [i|] eqn:LI; try discriminate.
  destruct (cp_eq_dec c1 c2) eqn:EC; try discriminate.
  destruct (eqb r1 r2) eqn:ER; try discriminate.
  destruct (eqb v1 v2) eqn:EV; intros EQ; inv EQ.
  apply eqb_prop in ER; apply eqb_prop in EV; subst r2 v2.
  apply link_linkorder in LF. apply link_linkorder in LI.
  split; constructor; tauto.
Defined.

(* Global Instance Linker_vardef_comp (V: Type) {LV: Linker V}: *)
(*   has_comp_linker (Linker_vardef V). *)
(* Proof. *)
(*   unfold has_comp_linker, link, Linker_vardef, link_vardef. *)
(*   intros. *)
(*   right; right. *)
(*   destruct (link (gvar_info x) (gvar_info y)) eqn:?; try congruence. *)
(*   destruct (link (gvar_init x) (gvar_init y)) eqn:?; try congruence. *)
(*   destruct andb eqn:EQ; try congruence. inv H. simpl in *. *)
(*   apply andb_prop in EQ as [EQ1 EQ3]. *)
(*   apply andb_prop in EQ1 as [EQ1 EQ2]. *)
(*   destruct (cp_eq_dec (gvar_comp x) (gvar_comp y)) as [e | ?]; try discriminate. *)
(*   now rewrite e. *)
(* Qed. *)

Global Opaque Linker_vardef.

(** A trivial linker for the trivial var info [unit]. *)

Global Program Instance Linker_unit: Linker unit := {
  link := fun x y => Some tt;
  linkorder := fun x y => True
}.

Global Opaque Linker_unit.

(** Linking global definitions *)

Definition link_def {F V: Type} {LF: Linker F} {LV: Linker V} (gd1 gd2: globdef F V) :=
  match gd1, gd2 with
  | Gfun f1, Gfun f2 =>
    match link f1 f2 with Some f => Some (Gfun f) | None => None end
  | Gvar v1, Gvar v2 =>
    match link v1 v2 with Some v => Some (Gvar v) | None => None end
  | _, _ => None
  end.

Inductive linkorder_def {F V: Type} {LF: Linker F} {LV: Linker V}: globdef F V -> globdef F V -> Prop :=
  | linkorder_def_fun: forall fd1 fd2,
      linkorder fd1 fd2 ->
      linkorder_def (Gfun fd1) (Gfun fd2)
  | linkorder_def_var: forall v1 v2,
      linkorder v1 v2 ->
      linkorder_def (Gvar v1) (Gvar v2).

Global Program Instance Linker_def (F V: Type) {LF: Linker F} {LV: Linker V}: Linker (globdef F V) := {
  link := link_def;
  linkorder := linkorder_def
}.
Next Obligation.
  destruct x; constructor; apply linkorder_refl.
Defined.
Next Obligation.
  inv H; inv H0; constructor; eapply linkorder_trans; eauto.
Defined.
Next Obligation.
  unfold link_def; intros.
  destruct x as [f1|v1], y as [f2|v2]; try discriminate.
+ simpl in H.
  destruct (link f1 f2) as [f|] eqn:L. inv H. apply link_linkorder in L.
  split; constructor; tauto. discriminate.
+ simpl in H.
  destruct (link v1 v2) as [v|] eqn:L; inv H. apply link_linkorder in L.
  split; constructor; tauto.
Defined.

(* Global Instance Linker_def_comp (F V: Type) {CF: has_comp F} {LF: Linker F} (* {CLF: has_comp_linker LF}  *){LV: Linker V}: *)
(*   has_comp_linker (Linker_def F V). *)
(* Proof. *)
(*   unfold has_comp_linker, Linker_def. *)
(*   intros x y z H. *)
(*   unfold link, link_def in H. *)
(*   destruct x, y; try congruence. *)
(*   - destruct (link f f0) eqn:EQ; try congruence. *)
(*     inv H. *)
(*     specialize (CLF _ _ _ EQ). auto. *)
(*   - destruct (link v v0) eqn:EQ; try congruence. *)
(*     inv H. simpl. *)
(*     pose proof (Linker_vardef_comp _ _ _ _ EQ). auto. *)
(* Qed. *)
Global Opaque Linker_def.

(** Linking two compilation units.  Compilation units are represented like
  whole programs using the type [program F V].  If a name has
  a global definition in one unit but not in the other, this definition
  is left unchanged in the result of the link.  If a name has
  global definitions in both units, and is public (not static) in both,
  the two definitions are linked as per [Linker_def] above.

  If one or both definitions are static (not public), we should ideally
  rename it so that it can be kept unchanged in the result of the link.
  This would require a general notion of renaming of global identifiers
  in programs that we do not have yet.  Hence, as a first step, linking
  is undefined if static definitions with the same name appear in both
  compilation units. *)

Section LINKER_PROG.

Context {F V: Type} {CF: has_comp F} {LF: Linker F} {LV: Linker V}
  (* {CLF: has_comp_linker LF} (* {CLV: Has_Comp_Linker LV} *) *)
  (p1 p2: program F V).

Let dm1 := prog_defmap p1.
Let dm2 := prog_defmap p2.

Definition link_prog_check (x: ident) (gd1: globdef F V) :=
  match dm2!x with
  | None => true
  | Some gd2 =>
      In_dec peq x p1.(prog_public)
      && In_dec peq x p2.(prog_public)
      && match link gd1 gd2 with Some _ => true | None => false end
  end.

Definition link_prog_merge (o1 o2: option (globdef F V)) :=
  match o1, o2 with
  | None, _ => o2
  | _, None => o1
  | Some gd1, Some gd2 => link gd1 gd2
  end.

Lemma link_prog_subproof :
  Policy.eqb p1.(prog_pol) p2.(prog_pol) = true ->
  Policy.in_pub p1.(prog_pol) (p1.(prog_public) ++ p2.(prog_public)).
Proof.

Admitted.

Definition link_pol_comp: PTree.t compartment :=
  let defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2) in
  PTree_Properties.of_list (List.map (fun '(id, a) => (id, comp_of a)) defs).


Definition link_pol  (pol1 pol2: Policy.t): Policy.t :=
  let comb := link_pol_comp in
  {| Policy.policy_comps := comb;
     Policy.policy_export := pol1.(Policy.policy_export);
     Policy.policy_import := pol1.(Policy.policy_import);
  |}.

Lemma prog_agr_comps_link:
  agr_comps (link_pol p1.(prog_pol) p2.(prog_pol))
    (PTree.elements (PTree.combine link_prog_merge dm1 dm2)).
Proof.
 unfold agr_comps.
 unfold link_pol. simpl.
 unfold link_pol_comp.
 rewrite Forall_forall.
 pose proof (PTree.elements_keys_norepet (PTree.combine link_prog_merge dm1 dm2)) as H. revert H.
 generalize (PTree.elements (PTree.combine link_prog_merge dm1 dm2)).
 intros l.
 assert (H: forall id gd, In (id, gd) l -> In (id, comp_of gd) (map (fun '(id, a) => (id, comp_of a)) l)).
 { intros.
   pose proof (@in_map (positive * globdef F V) _ (fun '(id, gd) => (id, comp_of gd))) as G.
   specialize (G l (id, gd)). eauto. }
 intros NO.
 assert (H': list_norepet (map fst (map (fun '(id, a) => (id, comp_of a)) l))).
 { rewrite map_map.
   replace (fun x : positive * globdef F V => fst (let '(id, a) := x in (id, comp_of a))) with
     (fst : positive * globdef F V -> positive). eauto.
   eapply FunctionalExtensionality.functional_extensionality.
   intros []; auto. }
 revert H' H NO.
 generalize (map (fun '(id, a) => (id, comp_of a)) l).
 induction l.
 - intros l' NO IN H x G; inv G.
 - intros l' NO IN H [id gd] G; inversion H as [|? ? A B C]; subst. simpl in *.
   destruct a as [id' gd']; simpl in *.
   destruct G as [G | G].
   + inv G.
     erewrite PTree_Properties.of_list_norepet; eauto.
   + exploit IN; eauto.
     exploit IHl; eauto.
Qed.

Definition link_prog :=
  if ident_eq p1.(prog_main) p2.(prog_main)
     && PTree_Properties.for_all dm1 link_prog_check then
    (* The policies of the two linked programs must be equal *)
    match sumbool_of_bool (Policy.eqb p1.(prog_pol) p2.(prog_pol)) with
    | left yes =>
        Some {| prog_main := p1.(prog_main);
                prog_public := p1.(prog_public) ++ p2.(prog_public);
                prog_defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2);
                prog_pol := link_pol (prog_pol p1) (prog_pol p2);
                prog_pol_pub := link_prog_subproof yes;
                prog_agr_comps := prog_agr_comps_link |}
    | right _ => None
    end
  else
    None.

Lemma link_prog_inv:
  forall p,
  link_prog = Some p ->
      p1.(prog_main) = p2.(prog_main)
   /\ (forall id gd1 gd2,
         dm1!id = Some gd1 -> dm2!id = Some gd2 ->
         In id p1.(prog_public) /\ In id p2.(prog_public) /\ exists gd, link gd1 gd2 = Some gd)
   /\ exists yes : Policy.eqb p1.(prog_pol) p2.(prog_pol) = true,
    (* If one can link two programs, then their policies where the same *)
      p = {| prog_main := p1.(prog_main);
            prog_public := p1.(prog_public) ++ p2.(prog_public);
            prog_defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2);
            prog_pol := link_pol (prog_pol p1) (prog_pol p2);
            prog_pol_pub := link_prog_subproof yes;
            prog_agr_comps := prog_agr_comps_link |}.
Proof.
  unfold link_prog; intros p E.
  destruct (ident_eq (prog_main p1) (prog_main p2)); try discriminate.
  destruct (PTree_Properties.for_all dm1 link_prog_check) eqn:C;
  simpl in E; try congruence.
  destruct (sumbool_of_bool (Policy.eqb p1.(prog_pol) p2.(prog_pol))) as [D|_];
  simpl in E; try congruence.
  rewrite PTree_Properties.for_all_correct in C.
  split; auto. split; auto.
  intros. exploit C; eauto. unfold link_prog_check. rewrite H0. intros.
  destruct (in_dec peq id (prog_public p1)); try discriminate.
  destruct (in_dec peq id (prog_public p2)); try discriminate.
  destruct (link gd1 gd2) eqn:L; try discriminate.
  intuition auto. exists g; auto.
  exists D; congruence.
Qed.

Lemma link_prog_succeeds:
  p1.(prog_main) = p2.(prog_main) ->
  (forall id gd1 gd2,
      dm1!id = Some gd1 -> dm2!id = Some gd2 ->
      In id p1.(prog_public) /\ In id p2.(prog_public) /\ link gd1 gd2 <> None) ->
  forall yes : Policy.eqb p1.(prog_pol) p2.(prog_pol) = true,
  link_prog =
    Some {| prog_main := p1.(prog_main);
            prog_public := p1.(prog_public) ++ p2.(prog_public);
            prog_defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2);
            prog_pol := link_pol (prog_pol p1) (prog_pol p2);
            prog_pol_pub := link_prog_subproof yes;
            prog_agr_comps := prog_agr_comps_link;
         |}.
Proof.
  intros. unfold link_prog. unfold proj_sumbool. rewrite H, dec_eq_true. simpl.
  replace (PTree_Properties.for_all dm1 link_prog_check) with true; auto.
  rewrite (sumbool_of_bool_true _ yes); trivial.
  symmetry. apply PTree_Properties.for_all_correct; intros. rename a into gd1.
  unfold link_prog_check. destruct dm2!x as [gd2|] eqn:G2; auto.
  exploit H0; eauto. intros (P & Q & R). unfold proj_sumbool; rewrite ! pred_dec_true by auto.
  destruct (link gd1 gd2); auto; discriminate.
Qed.

Lemma prog_defmap_elements:
  forall (m: PTree.t (globdef F V)) pub mn pol H H' x,
  (prog_defmap {| prog_defs := PTree.elements m;
                 prog_public := pub;
                 prog_main := mn;
                 prog_pol := pol;
                 prog_pol_pub := H;
                 prog_agr_comps := H';
               |})!x = m!x.
Proof.
  intros. unfold prog_defmap; simpl. apply PTree_Properties.of_list_elements.
Qed.

End LINKER_PROG.

Global Program Instance Linker_prog (F V: Type) {CF: has_comp F} {LF: Linker F} (* {CLF: has_comp_linker LF} *)
  {LV: Linker V} : Linker (program F V) := {
  link := link_prog;
  linkorder := fun p1 p2 =>
     p1.(prog_main) = p2.(prog_main)
  /\ incl p1.(prog_public) p2.(prog_public)
  /\ forall id gd1,
     (prog_defmap p1)!id = Some gd1 ->
     exists gd2,
        (prog_defmap p2)!id = Some gd2
     /\ linkorder gd1 gd2
     /\ (~In id p2.(prog_public) -> gd2 = gd1)
}.
Next Obligation.
  split; auto. split. apply incl_refl. intros.
  exists gd1; split; auto. split; auto. apply linkorder_refl.
Defined.
Next Obligation.
  split. congruence. split. red; eauto.
  intros. exploit H4; eauto. intros (gd2 & P & Q & R).
  exploit H2; eauto. intros (gd3 & U & X & Y).
  exists gd3. split; auto. split. eapply linkorder_trans; eauto.
  intros. transitivity gd2. apply Y. auto. apply R. red; intros; elim H0; auto.
Defined.
Next Obligation.
  apply link_prog_inv in H. destruct H as (L1 & L2 & L3 & L4).
  subst z; simpl. intuition auto.
+ red; intros; apply in_app_iff; auto.
+ rewrite prog_defmap_elements, PTree.gcombine, H by auto.
  destruct (prog_defmap y)!id as [gd2|] eqn:GD2; simpl.
* exploit L2; eauto. intros (P & Q & gd & R).
  exists gd; split. auto. split. apply link_linkorder in R; tauto.
  rewrite in_app_iff; tauto.
* exists gd1; split; auto. split. apply linkorder_refl. auto.
+ red; intros; apply in_app_iff; auto.
+ rewrite prog_defmap_elements, PTree.gcombine, H by auto.
  destruct (prog_defmap x)!id as [gd2|] eqn:GD2; simpl.
* exploit L2; eauto. intros (P & Q & gd & R).
  exists gd; split. auto. split. apply link_linkorder in R; tauto.
  rewrite in_app_iff; tauto.
* exists gd1; split; auto. split. apply linkorder_refl. auto.
Defined.

Lemma prog_defmap_linkorder:
  forall {F V: Type} {CF: has_comp F} {LF: Linker F} (* {CLF: has_comp_linker LF} *) {LV: Linker V} (p1 p2: program F V) id gd1,
  linkorder p1 p2 ->
  (prog_defmap p1)!id = Some gd1 ->
  exists gd2, (prog_defmap p2)!id = Some gd2 /\ linkorder gd1 gd2.
Proof.
  intros. destruct H as (A & B & C).
  exploit C; eauto. intros (gd2 & P & Q & R). exists gd2; auto.
Qed.

Global Opaque Linker_prog.

(** * Matching between two programs *)

(** The following is a relational presentation of program transformations,
  e.g. [transf_partial_program] from module [AST].  *)

(** To capture the possibility of separate compilation, we parameterize
  the [match_fundef] relation between function definitions with
  a context, e.g. the compilation unit from which the function definition comes.
  This unit is characterized as any program that is in the [linkorder]
  relation with the final, whole program. *)

Section MATCH_PROGRAM_GENERIC.

Context {C F1 V1 F2 V2: Type} {CF1: has_comp F1} {CF2: has_comp F2} {LC: Linker C} {LF: Linker F1} {LV: Linker V1}.
Variable match_fundef: C -> F1 -> F2 -> Prop.
(* Context {comp_match_fundef: has_comp_match match_fundef}. *)
Variable match_varinfo: V1 -> V2 -> Prop.

Inductive match_globvar: globvar V1 -> globvar V2 -> Prop :=
  | match_globvar_intro: forall i1 i2 c init ro vo,
      match_varinfo i1 i2 ->
      match_globvar (mkglobvar i1 c init ro vo) (mkglobvar i2 c init ro vo).

Inductive match_globdef (ctx: C): globdef F1 V1 -> globdef F2 V2 -> Prop :=
  | match_globdef_fun: forall ctx' f1 f2,
      linkorder ctx' ctx ->
      match_fundef ctx' f1 f2 ->
      match_globdef ctx (Gfun f1) (Gfun f2)
  | match_globdef_var: forall v1 v2,
      match_globvar v1 v2 ->
      match_globdef ctx (Gvar v1) (Gvar v2).

Definition match_ident_globdef
     (ctx: C) (ig1: ident * globdef F1 V1) (ig2: ident * globdef F2 V2) : Prop :=
  fst ig1 = fst ig2 /\ match_globdef ctx (snd ig1) (snd ig2).

Definition match_program_gen (ctx: C) (p1: program F1 V1) (p2: program F2 V2) : Prop :=
  list_forall2 (match_ident_globdef ctx) p1.(prog_defs) p2.(prog_defs)
  /\ p2.(prog_main) = p1.(prog_main)
  /\ p2.(prog_public) = p1.(prog_public)
  /\ Policy.eqb p2.(prog_pol) p1.(prog_pol) = true.

Theorem match_program_defmap:
  forall ctx p1 p2, match_program_gen ctx p1 p2 ->
  forall id, option_rel (match_globdef ctx) (prog_defmap p1)!id (prog_defmap p2)!id.
Proof.
  intros. apply PTree_Properties.of_list_related. apply H.
Qed.

Lemma match_program_gen_main:
  forall ctx p1 p2, match_program_gen ctx p1 p2 -> p2.(prog_main) = p1.(prog_main).
Proof.
  intros. apply H.
Qed.

Lemma match_program_public:
  forall ctx p1 p2, match_program_gen ctx p1 p2 -> p2.(prog_public) = p1.(prog_public).
Proof.
  intros. apply H.
Qed.

End MATCH_PROGRAM_GENERIC.

(** In many cases, the context for [match_program_gen] is the source program or
  source compilation unit itself.  We provide a specialized definition for this case. *)

Definition match_program {F1 V1 F2 V2: Type} {CF1: has_comp F1} {CF2: has_comp F2} {LF: Linker F1}
                         (* {CLF: has_comp_linker LF} *) {LV: Linker V1}
                         (match_fundef: program F1 V1 -> F1 -> F2 -> Prop)
                         (match_varinfo: V1 -> V2 -> Prop)
                         (p1: program F1 V1) (p2: program F2 V2) : Prop :=
  match_program_gen match_fundef match_varinfo p1 p1 p2.

Lemma match_program_main:
  forall {F1 V1 F2 V2: Type} {CF1: has_comp F1} {CF2: has_comp F2} {LF: Linker F1} (* {CLF: has_comp_linker LF} *) {LV: Linker V1}
         {match_fundef: program F1 V1 -> F1 -> F2 -> Prop}
         {match_varinfo: V1 -> V2 -> Prop}
         {p1: program F1 V1} {p2: program F2 V2},
  match_program match_fundef match_varinfo p1 p2 -> p2.(prog_main) = p1.(prog_main).
Proof.
  intros. apply H.
Qed.

(*
Lemma match_program_implies:
  forall (A B V W: Type) (LA: Linker A) (LV: Linker V)
         (match_fundef1 match_fundef2: program A V -> A -> B -> Prop)
         (match_varinfo1 match_varinfo2: V -> W -> Prop)
         p p',
  match_program match_fundef1 match_varinfo1 p p' ->
  (forall cu a b, match_fundef1 cu a b -> linkorder cu p -> match_fundef2 cu a b) ->
  (forall v w, match_varinfo1 v w -> match_varinfo2 v w) ->
  match_program match_fundef2 match_varinfo2 p p'.
Proof.
  intros. destruct H as [P Q]. split; auto.
  eapply list_forall2_imply; eauto.
  intros. inv H3. split; auto. inv H5.
  econstructor; eauto.
  constructor. inv H7; constructor; auto.
Qed.
*)

(** Relation between the program transformation functions from [AST]
  and the [match_program] predicate. *)

Theorem match_transform_partial_program2:
  forall {C F1 V1 F2 V2: Type} {CF1: has_comp F1} {CF2: has_comp F2} {LC: Linker C} {LF: Linker F1}
                                                                {LV: Linker V1}
         (match_fundef: C -> F1 -> F2 -> Prop)
         (match_varinfo: V1 -> V2 -> Prop)
         (transf_fun: ident -> F1 -> res F2)
         {Cf: forall id, has_comp_transl_partial (transf_fun id)}
         (transf_var: ident -> V1 -> res V2)
         (ctx: C) (p: program F1 V1) (tp: program F2 V2),
  transform_partial_program2 transf_fun transf_var p = OK tp ->
  (forall i f tf, transf_fun i f = OK tf -> match_fundef ctx f tf) ->
  (forall i v tv, transf_var i v = OK tv -> match_varinfo v tv) ->
  match_program_gen match_fundef match_varinfo ctx p tp.
Proof.
  unfold transform_partial_program2; intros. revert H.
  generalize (agr_comps_transf_partial transf_fun transf_var (prog_agr_comps p)).
  intros a H.
  destruct transf_globdefs eqn:EQ; try congruence.
  inv H.
  red; simpl; split; auto.
  clear a.
  revert l EQ. generalize (prog_defs p).
  induction l as [ | [i g] l]; simpl; intros.
- monadInv EQ. constructor.
- destruct g as [f|v].
+ destruct (transf_fun i f) as [tf|?] eqn:TF; monadInv EQ.
  constructor; auto. split; simpl; auto. econstructor. apply linkorder_refl. eauto.
+ destruct (transf_globvar transf_var i v) as [tv|?] eqn:TV; monadInv EQ.
  constructor; auto. split; simpl; auto. constructor.
  monadInv TV. destruct v; simpl; constructor. eauto.
- split; auto. split; auto.
  destruct (prog_pol p); simpl; auto.
  unfold update_policy; simpl; auto.
  unfold Policy.eqb; rewrite !andb_true_iff; repeat split; simpl; auto.
  + rewrite PTree.beq_correct. intros id.
    unfold update_list_comps.
    destruct (policy_comps ! id); auto.
    destruct cp_eq_dec; auto.
  + rewrite PTree.beq_correct.
    intros y. destruct (policy_export ! y); auto.
    destruct (Policy.list_id_eq l0 l0); auto.
  + rewrite PTree.beq_correct.
    intros y. destruct (policy_import ! y); auto.
    destruct (Policy.list_cpt_id_eq l0 l0); auto.
Qed.

Theorem match_transform_partial_program_contextual:
  forall {A B V: Type} {CA: has_comp A} {CB: has_comp B} {LA: Linker A} {LV: Linker V}
         (match_fundef: program A V -> A -> B -> Prop)
         (transf_fun: A -> res B)
         {comp_transf_fun: has_comp_transl_partial transf_fun}
         (p: program A V) (tp: program B V),
  transform_partial_program transf_fun p = OK tp ->
  (forall f tf, transf_fun f = OK tf -> match_fundef p f tf) ->
  match_program match_fundef eq p tp.
Proof.
  intros.
  eapply match_transform_partial_program2. eexact H.
  auto.
  simpl; intros. congruence.
Qed.

Theorem match_transform_program_contextual:
  forall {A B V: Type} {CA: has_comp A} {CB: has_comp B} {LA: Linker A} {LV: Linker V}
         (match_fundef: program A V -> A -> B -> Prop)
         (transf_fun: A -> B)
         {comp_transf: has_comp_transl transf_fun}
         (p: program A V),
  (forall f, match_fundef p f (transf_fun f)) ->
  match_program match_fundef eq p (transform_program transf_fun p).
Proof.
  intros.
  eapply match_transform_partial_program_contextual.
  apply transform_program_partial_program with (transf_fun := transf_fun).
  simpl; intros. inv H0. auto.
Qed.

(** The following two theorems are simpler versions for the case where the
  function transformation does not depend on the compilation unit. *)

Theorem match_transform_partial_program:
  forall {A B V: Type} {CA: has_comp A} {CB: has_comp B} {LA: Linker A} {LV: Linker V}
         (transf_fun: A -> res B)
         {comp_transf_fun: has_comp_transl_partial transf_fun}
         (p: program A V) (tp: program B V),
  transform_partial_program transf_fun p = OK tp ->
  match_program (fun cu f tf => transf_fun f = OK tf) eq p tp.
Proof.
  intros.
  eapply match_transform_partial_program2. eexact H.
  auto.
  simpl; intros. congruence.
Qed.

Theorem match_transform_program:
  forall {A B V: Type} {CA: has_comp A} {CB: has_comp B} {LA: Linker A} {LV: Linker V}
         (transf: A -> B)
         {comp_transf: has_comp_transl transf}
         (p: program A V),
  match_program (fun cu f tf => tf = transf f) eq p (transform_program transf p).
Proof.
  intros. apply match_transform_program_contextual. auto.
Qed.

(** * Commutation between linking and program transformations *)

Section LINK_MATCH_PROGRAM.

Context {C F1 V1 F2 V2: Type} {CF1: has_comp F1} {CF2: has_comp F2} {LC: Linker C} {LF1: Linker F1} {LF2: Linker F2} {LV1: Linker V1} {LV2: Linker V2}.
Variable match_fundef: C -> F1 -> F2 -> Prop.
Context {has_comp_match_fundef: has_comp_match match_fundef}.
Variable match_varinfo: V1 -> V2 -> Prop.

Local Transparent Linker_vardef Linker_def Linker_prog.

Hypothesis link_match_fundef:
  forall ctx1 ctx2 f1 tf1 f2 tf2 f,
  link f1 f2 = Some f ->
  match_fundef ctx1 f1 tf1 -> match_fundef ctx2 f2 tf2 ->
  exists tf, link tf1 tf2 = Some tf /\ (match_fundef ctx1 f tf \/ match_fundef ctx2 f tf).

Hypothesis link_match_varinfo:
  forall v1 tv1 v2 tv2 v,
  link v1 v2 = Some v ->
  match_varinfo v1 tv1 -> match_varinfo v2 tv2 ->
  exists tv, link tv1 tv2 = Some tv /\ match_varinfo v tv.

Lemma link_match_globvar:
  forall v1 tv1 v2 tv2 v,
  link v1 v2 = Some v ->
  match_globvar match_varinfo v1 tv1 -> match_globvar match_varinfo v2 tv2 ->
  exists tv, link tv1 tv2 = Some tv /\ match_globvar match_varinfo v tv.
Proof.
  simpl; intros. unfold link_vardef in *. inv H0; inv H1; simpl in *.
  destruct (link i1 i0) as [info'|] eqn:LINFO; try discriminate.
  destruct (link init init0) as [init'|] eqn:LINIT; try discriminate.
  destruct (cp_eq_dec c c0 && eqb ro ro0 && eqb vo vo0); inv H.
  exploit link_match_varinfo; eauto. intros (tinfo & P & Q). rewrite P.
  econstructor; split. eauto. constructor. auto.
Qed.

Lemma link_match_globdef:
  forall ctx1 ctx2 ctx g1 tg1 g2 tg2 g,
  linkorder ctx1 ctx -> linkorder ctx2 ctx ->
  link g1 g2 = Some g ->
  match_globdef match_fundef match_varinfo ctx1 g1 tg1 ->
  match_globdef match_fundef match_varinfo ctx2 g2 tg2 ->
  exists tg, link tg1 tg2 = Some tg /\ match_globdef match_fundef match_varinfo ctx g tg.
Proof.
  simpl link. unfold link_def.
  intros ctx1 ctx2 ctx g1 tg1 g2 tg2 g LO1 LO2 L MATCH1 MATCH2.
  destruct MATCH1 as [ctx1' f1 tf1 LO1' MATCH1|v1 tv1];
  destruct MATCH2 as [ctx2' f2 tf2 LO2' MATCH2|v2 tv2];
  try discriminate.
- destruct (link f1 f2) as [f|] eqn:LF; try easy.
  exploit link_match_fundef; eauto. intros (tf & P & Q).
  assert (X: exists ctx', linkorder ctx' ctx /\ match_fundef ctx' f tf).
  { destruct Q as [Q|Q]; econstructor; (split; [|eassumption]).
    apply linkorder_trans with ctx1; auto.
    apply linkorder_trans with ctx2; auto. }
  destruct X as (cu & X & Y).
  exists (Gfun tf); split. rewrite P; auto.
  inv L. econstructor; eauto.
- destruct (link v1 v2) as [v|] eqn:LVAR; try easy.
  exploit link_match_globvar; eauto. intros (tv & P & Q).
  exists (Gvar tv); split. rewrite P; auto. inv L. constructor; auto.
Qed.

Lemma match_globdef_linkorder:
  forall ctx ctx' g tg,
  match_globdef match_fundef match_varinfo ctx g tg ->
  linkorder ctx ctx' ->
  match_globdef match_fundef match_varinfo ctx' g tg.
Proof.
  intros. inv H.
- econstructor. eapply linkorder_trans; eauto. auto.
- constructor; auto.
Qed.

Theorem link_match_program:
  forall ctx1 ctx2 ctx p1 p2 tp1 tp2 p,
  link p1 p2 = Some p ->
  match_program_gen match_fundef match_varinfo ctx1 p1 tp1 ->
  match_program_gen match_fundef match_varinfo ctx2 p2 tp2 ->
  linkorder ctx1 ctx -> linkorder ctx2 ctx ->
  exists tp, link tp1 tp2 = Some tp /\ match_program_gen match_fundef match_varinfo ctx p tp.
Proof.
  intros. destruct (link_prog_inv _ _ _ H) as (P & Q & S & R).
  generalize H0; intros (A1 & B1 & C1 & D1).
  generalize H1; intros (A2 & B2 & C2 & D2).
  assert (yes : Policy.eqb (prog_pol tp1) (prog_pol tp2) = true).
  { apply (Policy.eqb_trans _ _ _ D1).
    apply (Policy.eqb_trans _ _ _ S).
    now apply Policy.eqb_comm. }
  econstructor; split.
- apply (link_prog_succeeds tp1 tp2) with (yes := yes).
+ congruence.
+ intros.
  generalize (match_program_defmap _ _ _ _ _ H0 id) (match_program_defmap _ _ _ _ _ H1 id).
  rewrite H4, H5. intros R1 R2; inv R1; inv R2.
  exploit Q; eauto. intros (X & Y & gd & Z).
  exploit link_match_globdef. eexact H2. eexact H3. eauto. eauto. eauto.
  intros (tg & TL & _). intuition congruence.
- split; [|split].
+ rewrite R. apply PTree.elements_canonical_order'. intros id.
  rewrite ! PTree.gcombine by auto.
  generalize (match_program_defmap _ _ _ _ _ H0 id) (match_program_defmap _ _ _ _ _ H1 id).
  clear R. intros R1 R2; inv R1; inv R2; unfold link_prog_merge.
* constructor.
* constructor. apply match_globdef_linkorder with ctx2; auto.
* constructor. apply match_globdef_linkorder with ctx1; auto.
* exploit Q; eauto. intros (X & Y & gd & Z).
  exploit link_match_globdef. eexact H2. eexact H3. eauto. eauto. eauto.
  intros (tg & TL & MG). rewrite Z, TL. constructor; auto.
+ rewrite R; simpl; auto.
+ rewrite R; simpl. split; try congruence.
  unfold Policy.eqb.
  rewrite !andb_true_iff. unfold CompTree.beq. simpl.
  clear yes. unfold Policy.eqb in D1. rewrite !andb_true_iff in D1.
  destruct D1 as [[? ?] ?].
  split; [split |]; auto.
  unfold link_pol_comp.
  rewrite PTree.beq_correct. intros x.
  assert (G: forall A B (f: A -> B) (t: PTree.t A), map (fun '(id, x) => (id, f x)) (PTree.elements t) =
                   PTree.elements (PTree.map1 f t)).
  { clear.
    intros.
    unfold PTree.elements. generalize 1%positive.
    assert (H: map (fun '(id, x) => (id, f x)) nil = (nil: list (positive * B))) by reflexivity.
    revert H.
    generalize (nil: list (positive * B)).
    generalize (nil: list (positive * A)).
    induction t using PTree.tree_ind.
    - intros; auto.
    - intros l0 l1 EQ p.
      destruct l; simpl in *; auto.
      + destruct o; simpl in *; auto.
        * destruct r; simpl in *; try rewrite EQ; auto.
          erewrite IHt0; auto.
        * destruct r; simpl in *; auto.
      + destruct o; simpl in *; auto.
        * destruct r; simpl in *; auto.
          now erewrite IHt; eauto; simpl; rewrite EQ.
          now erewrite IHt; eauto; simpl; erewrite IHt0.
        * destruct r; simpl in *; auto.
  }
  rewrite !G.
  rewrite !PTree_Properties.of_list_elements.
  rewrite !PTree.gmap1.
  unfold option_map.
  assert (option_rel (match_globdef match_fundef match_varinfo ctx)
            (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)) ! x
            (PTree.combine link_prog_merge (prog_defmap tp1) (prog_defmap tp2)) ! x).
  {
  rewrite ! PTree.gcombine by auto.
  generalize (match_program_defmap _ _ _ _ _ H0 x) (match_program_defmap _ _ _ _ _ H1 x).
  clear R. intros R1 R2; inv R1; inv R2; unfold link_prog_merge.
* constructor.
* constructor. apply match_globdef_linkorder with ctx2; auto.
* constructor. apply match_globdef_linkorder with ctx1; auto.
* exploit Q; eauto. intros (X & Y & gd & Z).
  exploit link_match_globdef. eexact H2. eexact H3. eauto. eauto. eauto.
  intros (tg & TL & MG). rewrite Z, TL. constructor; auto. }
  inv H7; auto. inv H10; auto.
  apply has_comp_match_fundef in H11. simpl; rewrite H11.
  now destruct cp_eq_dec.
  inv H7; simpl; now destruct cp_eq_dec.
Qed.

End LINK_MATCH_PROGRAM.

(** We now wrap this commutation diagram into a class, and provide some common instances. *)

Class TransfLink {A B: Type} {LA: Linker A} {LB: Linker B} (transf: A -> B -> Prop) :=
  transf_link:
    forall (p1 p2: A) (tp1 tp2: B) (p: A),
    link p1 p2 = Some p ->
    transf p1 tp1 -> transf p2 tp2 ->
    exists tp, link tp1 tp2 = Some tp /\ transf p tp.

Remark link_transf_partial_fundef:
  forall (A B: Type) {CA: has_comp A} {CB: has_comp B}
         (tr1 tr2: A -> res B)
         {CAB1: has_comp_transl_partial tr1} {CAB2: has_comp_transl_partial tr2}
         (f1 f2: fundef A) (tf1 tf2: fundef B) (f: fundef A),
  link f1 f2 = Some f ->
  transf_partial_fundef tr1 f1 = OK tf1 ->
  transf_partial_fundef tr2 f2 = OK tf2 ->
  exists tf,
      link tf1 tf2 = Some tf
  /\ (transf_partial_fundef tr1 f = OK tf \/ transf_partial_fundef tr2 f = OK tf).
Proof.
Local Transparent Linker_fundef.
  simpl; intros. destruct f1 as [f1|ef1], f2 as [f2|ef2]; simpl in *; monadInv H0; monadInv H1.
- discriminate.
- destruct ef2; inv H.
  exists (Internal x); split.
    reflexivity.
  left; simpl; rewrite EQ; auto.
- destruct ef1; inv H.
  exists (Internal x). split.
    reflexivity.
  right; simpl; rewrite EQ; auto.
- destruct (external_function_eq ef1 ef2); inv H. exists (External ef2); split; auto. simpl. rewrite dec_eq_true; auto.
Qed.

Global Instance TransfPartialContextualLink
           {A B C V: Type} {LV: Linker V}
           {CA: has_comp A} {CB: has_comp B}
           (tr_fun: C -> A -> res B)
           {CAB: forall ctx, has_comp_transl_partial (tr_fun ctx)}
           (ctx_for: program (fundef A) V -> C):
  TransfLink (fun (p1: program (fundef A) V) (p2: program (fundef B) V) =>
              match_program
                (fun cu f tf => AST.transf_partial_fundef (tr_fun (ctx_for cu)) f = OK tf)
                eq p1 p2).
Proof.
  red. intros. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  eapply link_match_program; eauto.
- intros ? ? ? ?. eapply has_comp_transl_partial_match; eauto.
  eapply comp_transf_partial_fundef. eauto.
- intros. eapply link_transf_partial_fundef; eauto.
- intros; subst. exists v; auto.
Qed.

Global Instance TransfPartialLink
           {A B V: Type} {LV: Linker V}
           {CA: has_comp A} {CB: has_comp B}
           (tr_fun: A -> res B)
           {CAB: has_comp_transl_partial tr_fun}:
  TransfLink (fun (p1: program (fundef A) V) (p2: program (fundef B) V) =>
              match_program
                (fun cu f tf => AST.transf_partial_fundef tr_fun f = OK tf)
                eq p1 p2).
Proof.
  red. intros. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  eapply link_match_program; eauto.
- intros ? ? ? ?. eapply has_comp_transl_partial_match; eauto.
  eapply comp_transf_partial_fundef. eauto.
- intros. eapply link_transf_partial_fundef; eauto.
- intros; subst. exists v; auto.
Qed.

Global Instance TransfTotallContextualLink
           {A B C V: Type}
           {CA: has_comp A} {CB: has_comp B} {LV: Linker V}
           (tr_fun: C -> A -> B)
           {CAB: forall ctx, has_comp_transl (tr_fun ctx)}
           (ctx_for: program (fundef A) V -> C):
  TransfLink (fun (p1: program (fundef A) V) (p2: program (fundef B) V) =>
              match_program
                (fun cu f tf => tf = AST.transf_fundef (tr_fun (ctx_for cu)) f)
                eq p1 p2).
Proof.
  red. intros. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  eapply link_match_program; eauto.
- intros ? ? ? ?. eapply has_comp_transl_match; eauto.
  eapply comp_transf_fundef. eauto.
- intros. subst. destruct f1, f2; simpl in *.
+ discriminate.
+ destruct e; try easy.
  inv H2.
  econstructor; eauto.
+ destruct e; try easy.
  inv H2.
  econstructor; eauto.
+ destruct (external_function_eq e e0); inv H2. econstructor; eauto.
- intros; subst. exists v; auto.
Qed.

Global Instance TransfTotalLink
           {A B V: Type}
           {CA: has_comp A} {CB: has_comp B} {LV: Linker V}
           (tr_fun: A -> B)
           {CAB: has_comp_transl tr_fun}:
  TransfLink (fun (p1: program (fundef A) V) (p2: program (fundef B) V) =>
              match_program
                (fun cu f tf => tf = AST.transf_fundef tr_fun f)
                eq p1 p2).
Proof.
  red. intros. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  eapply link_match_program; eauto.
- intros ? ? ? ?. eapply has_comp_transl_match; eauto.
  eapply comp_transf_fundef. eauto.
- intros. subst. destruct f1, f2; simpl in *.
+ discriminate.
+ destruct e; try easy.
  inv H2.
  econstructor; eauto.
+ destruct e; try easy.
  inv H2.
  econstructor; eauto.
+ destruct (external_function_eq e e0); inv H2. econstructor; eauto.
- intros; subst. exists v; auto.
Qed.

(** * Linking a set of compilation units *)

(** Here, we take a more general view of linking as taking a nonempty list of compilation units
  and producing a whole program. *)

Section LINK_LIST.

Context {A: Type} {LA: Linker A}.

Fixpoint link_list (l: nlist A) : option A :=
  match l with
  | nbase a => Some a
  | ncons a l =>
      match link_list l with None => None | Some b => link a b end
  end.

Lemma link_list_linkorder:
  forall a l b, link_list l = Some b -> nIn a l -> linkorder a b.
Proof.
  induction l; simpl; intros.
- inv H. subst. apply linkorder_refl.
- destruct (link_list l) as [b'|]; try discriminate.
  apply link_linkorder in H. destruct H0.
+ subst a0. tauto.
+ apply linkorder_trans with b'. auto. tauto.
Qed.

End LINK_LIST.

(** List linking commutes with program transformations, provided the
  transformation commutes with simple (binary) linking. *)

Section LINK_LIST_MATCH.

Context {A B: Type} {LA: Linker A} {LB: Linker B} (prog_match: A -> B -> Prop) {TL: TransfLink prog_match}.

Theorem link_list_match:
  forall al bl, nlist_forall2 prog_match al bl ->
  forall a, link_list al = Some a ->
  exists b, link_list bl = Some b /\ prog_match a b.
Proof.
  induction 1; simpl; intros a' L.
- inv L. exists b; auto.
- destruct (link_list l) as [a1|] eqn:LL; try discriminate.
  exploit IHnlist_forall2; eauto. intros (b' & P & Q).
  red in TL. exploit TL; eauto. intros (b'' & U & V).
  rewrite P; exists b''; auto.
Qed.

End LINK_LIST_MATCH.

(** * Linking and composition of compilation passes *)

Set Implicit Arguments.

(** A generic language is a type of programs and a linker. *)

Structure Language := mklang { lang_prog :> Type; lang_link: Linker lang_prog }.

Canonical Structure Language_gen (A: Type) (L: Linker A) : Language := @mklang A L.

(** A compilation pass from language [S] (source) to language [T] (target)
  is a matching relation between [S] programs and [T] programs,
  plus two linkers, one for [S] and one for [T],
  and a property of commutation with linking. *)

Record Pass (S T: Language) := mkpass {
  pass_match :> lang_prog S -> lang_prog T -> Prop;
  pass_match_link: @TransfLink (lang_prog S) (lang_prog T) (lang_link S) (lang_link T) pass_match;
}.

Arguments mkpass {S} {T} (pass_match) {pass_match_link}.

Program Definition pass_identity (l: Language): Pass l l :=
  {| pass_match := fun p1 p2 => p1 = p2;
     pass_match_link := _; |}.
Next Obligation.
  red; intros. subst. exists p; auto.
Defined.

Program Definition pass_compose {l1 l2 l3: Language} (pass: Pass l1 l2) (pass': Pass l2 l3) : Pass l1 l3 :=
  {| pass_match := fun p1 p3 => exists p2, pass_match pass p1 p2 /\ pass_match pass' p2 p3;
     pass_match_link := _; |}.
Next Obligation.
  red; intros.
  destruct H0 as (p1' & A1 & B1).
  destruct H1 as (p2' & A2 & B2).
  edestruct (pass_match_link pass) as (p' & A & B); eauto.
  edestruct (pass_match_link pass') as (tp & C & D); eauto.
Defined.

(** A list of compilation passes that can be composed. *)

Inductive Passes: Language -> Language -> Type :=
  | pass_nil: forall l, Passes l l
  | pass_cons: forall l1 l2 l3, Pass l1 l2 -> Passes l2 l3 -> Passes l1 l3.

Declare Scope linking_scope.

Infix ":::" := pass_cons (at level 60, right associativity) : linking_scope.

(** The pass corresponding to the composition of a list of passes. *)

Fixpoint compose_passes (l l': Language) (passes: Passes l l') : Pass l l' :=
  match passes in Passes l l' return Pass l l' with
  | pass_nil l => pass_identity l
  | pass_cons pass1 passes => pass_compose pass1 (compose_passes passes)
  end.

(** Some more lemmas about [nlist_forall2]. *)

Lemma nlist_forall2_identity:
  forall (A: Type) (la lb: nlist A),
  nlist_forall2 (fun a b => a = b) la lb -> la = lb.
Proof.
  induction 1; congruence.
Qed.

Lemma nlist_forall2_compose_inv:
  forall (A B C: Type) (R1: A -> B -> Prop) (R2: B -> C -> Prop)
         (la: nlist A) (lc: nlist C),
  nlist_forall2 (fun a c => exists b, R1 a b /\ R2 b c) la lc ->
  exists lb: nlist B, nlist_forall2 R1 la lb /\ nlist_forall2 R2 lb lc.
Proof.
  induction 1.
- rename b into c. destruct H as (b & P & Q).
  exists (nbase b); split; constructor; auto.
- rename b into c. destruct H as (b & P & Q). destruct IHnlist_forall2 as (lb & U & V).
  exists (ncons b lb); split; constructor; auto.
Qed.

(** List linking with a composition of compilation passes. *)

Theorem link_list_compose_passes:
  forall (src tgt: Language) (passes: Passes src tgt)
         (src_units: nlist src) (tgt_units: nlist tgt),
  nlist_forall2 (pass_match (compose_passes passes)) src_units tgt_units ->
  forall src_prog,
  @link_list _ (lang_link src) src_units = Some src_prog ->
  exists tgt_prog,
  @link_list _ (lang_link tgt) tgt_units = Some tgt_prog
  /\ pass_match (compose_passes passes) src_prog tgt_prog.
Proof.
  induction passes; simpl; intros src_units tgt_units F2 src_prog LINK.
- apply nlist_forall2_identity in F2. subst tgt_units. exists src_prog; auto.
- apply nlist_forall2_compose_inv in F2. destruct F2 as (interm_units & P & Q).
  edestruct (@link_list_match _ _ (lang_link l1) (lang_link l2) (pass_match p))
  as (interm_prog & U & V).
  apply pass_match_link. eauto. eauto.
  exploit IHpasses; eauto. intros (tgt_prog & X & Y).
  exists tgt_prog; split; auto. exists interm_prog; auto.
Qed.

