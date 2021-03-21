(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)
Require Import Recdef.
Require Import Zwf.
Require Import Axioms Coqlib Errors Maps AST Linking.
Require Import Integers Floats Values Memory Builtins.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.
Local Open Scope error_monad_scope.

Set Implicit Arguments.


Section POLICY.

Variable F: Type.  (**r The type of function descriptions *)
Context {CF: has_comp F} {FD: @is_fundef F CF}.

Record t : Type := mkpolicy {
  policy_export : compartment -> list F; (* The list of exported functions *)
  policy_import : compartment -> list (compartment * F); (* The list of imported functions and their compartment *)
  (* Well-formedness conditions on the interface *)
  export_in_cp: forall cp f, In f (policy_export cp) -> comp_of f = cp;
  (* All runtime functions can be called from any compartment *)
  imports_builtin: forall cp name f sg bf,
      lookup_builtin_function name sg = Some bf ->
      simpl_fundef f = External (EF_builtin name sg) ->
      In (default_compartment, f) (policy_import cp);
  exports_builtin: forall name f sg bf,
      lookup_builtin_function name sg = Some bf ->
      simpl_fundef f = External (EF_builtin name sg) ->
      In f (policy_export default_compartment);
  (* All runtime functions can be called from any compartment *)
  imports_runtime: forall cp name f sg bf,
      lookup_builtin_function name sg = Some bf ->
      simpl_fundef f = External (EF_runtime name sg) ->
      In (default_compartment, f) (policy_import cp);
  exports_runtime: forall name f sg bf,
      lookup_builtin_function name sg = Some bf ->
      simpl_fundef f = External (EF_runtime name sg) ->
      In f (policy_export default_compartment);
  (* Vload can be called from any compartment *)
  imports_vload: forall cp f ch,
      simpl_fundef f = External (EF_vload ch) ->
      In (default_compartment, f) (policy_import cp);
  exports_vload: forall f ch,
      simpl_fundef f = External (EF_vload ch) ->
      In f (policy_export default_compartment);
  (* Vstore can be called from any compartment *)
  imports_vstore: forall cp f ch,
      simpl_fundef f = External (EF_vstore ch) ->
      In (default_compartment, f) (policy_import cp);
  exports_vstore: forall f ch,
      simpl_fundef f = External (EF_vstore ch) ->
      In f (policy_export default_compartment);
  (* Malloc can be called from any compartment *)
  imports_malloc: forall cp f,
      simpl_fundef f = External (EF_malloc) ->
      In (default_compartment, f) (policy_import cp);
  exports_malloc: forall f,
      simpl_fundef f = External (EF_malloc) ->
      In f (policy_export default_compartment);
  (* Free can be called from any compartment *)
  imports_free: forall cp f,
      simpl_fundef f = External (EF_free) ->
      In (default_compartment, f) (policy_import cp);
  exports_free: forall f,
      simpl_fundef f = External (EF_free) ->
      In f (policy_export default_compartment);
  (* Memcpy can be called from any compartment *)
  imports_memcpy: forall cp f v1 v2,
      simpl_fundef f = External (EF_memcpy v1 v2) ->
      In (default_compartment, f) (policy_import cp);
  exports_memcpy: forall f v1 v2,
      simpl_fundef f = External (EF_memcpy v1 v2) ->
      In f (policy_export default_compartment);
  (* All calls to the EF_debug must be allowed from any compartment *)
  imports_debug: forall cp f n i l,
      simpl_fundef f = External (EF_debug n i l) ->
      In (default_compartment, f) (policy_import cp);
  exports_debug: forall f n i l,
      simpl_fundef f = External (EF_debug n i l) ->
      In f (policy_export default_compartment)
  }.

Definition allowed_cross_call (pol: t) (cp: compartment) (f: F) :=
  In (comp_of f, f) (policy_import pol cp) /\
  In f (policy_export pol (comp_of f)).

Definition allowed_call (pol: t) (cp: compartment) (f: F) :=
  comp_of f = cp \/ allowed_cross_call pol cp f.

(* JT: TODO: Refactor these two definitions *)
Lemma pol_accepts_runtime: forall pol cp name f sg bf,
    lookup_builtin_function name sg = Some bf ->
    simpl_fundef f = External (EF_runtime name sg) ->
    allowed_call pol cp f.
Proof.
  intros pol cp name f sg bf H1 H2; subst.
  right; split.
  - erewrite preserves_comp.
    rewrite H2.
    eapply imports_runtime; eauto.
  - erewrite preserves_comp.
    rewrite H2.
    eapply exports_runtime; eauto.
Qed.

Lemma pol_accepts_builtin: forall pol cp name f sg bf,
    lookup_builtin_function name sg = Some bf ->
    simpl_fundef f = External (EF_builtin name sg) ->
    allowed_call pol cp f.
Proof.
  intros pol cp name f sg bf H1 H2; subst.
  right; split.
  - erewrite preserves_comp.
    rewrite H2.
    eapply imports_builtin; eauto.
  - erewrite preserves_comp.
    rewrite H2.
    eapply exports_builtin; eauto.
Qed.

Lemma pol_accepts_vload: forall pol cp f ch,
    simpl_fundef f = External (EF_vload ch) ->
    allowed_call pol cp f.
Proof.
  intros pol cp f ch H1; subst.
  right; split.
  - erewrite preserves_comp.
    rewrite H1.
    eapply imports_vload; eauto.
  - erewrite preserves_comp.
    rewrite H1.
    eapply exports_vload; eauto.
Qed.

Lemma pol_accepts_vstore: forall pol cp f ch,
    simpl_fundef f = External (EF_vstore ch) ->
    allowed_call pol cp f.
Proof.
  intros pol cp f ch H1; subst.
  right; split.
  - erewrite preserves_comp.
    rewrite H1.
    eapply imports_vstore; eauto.
  - erewrite preserves_comp.
    rewrite H1.
    eapply exports_vstore; eauto.
Qed.

Lemma pol_accepts_memcpy: forall pol cp f v1 v2,
    simpl_fundef f = External (EF_memcpy v1 v2) ->
    allowed_call pol cp f.
Proof.
  intros pol cp f v1 v2 H1; subst.
  right; split.
  - erewrite preserves_comp.
    rewrite H1.
    eapply imports_memcpy; eauto.
  - erewrite preserves_comp.
    rewrite H1.
    eapply exports_memcpy; eauto.
Qed.

Lemma pol_accepts_debug: forall pol cp f n i l,
    simpl_fundef f = External (EF_debug n i l) ->
    allowed_call pol cp f.
Proof.
  intros pol cp f n i l H.
  right; split.
  - erewrite preserves_comp. rewrite H.
    eapply imports_debug; eauto.
  - erewrite preserves_comp. rewrite H.
    eapply exports_debug; eauto.
Qed.



(* TODO: Write the proper definition of these *)
Axiom allowed_call_b: t -> compartment -> F -> bool.
Axiom allowed_call_reflect : forall pol cp f,
    allowed_call pol cp f <-> allowed_call_b pol cp f = true.

(* Definition allowed_cross_call_p (pol: t) (cp: compartment) (f: F) := *)
(*   if in_dec _ (comp_of f, f) (policy_import pol cp) then *)
(*     if (in_dec _ f (policy_export pol (comp_of f))) then *)
(*       true *)
(*     else false *)
(*   else false. *)

(* Definition allowed_call_b (pol: t) (cp: compartment) (f: F) := *)
(*   if peq (comp_of f) cp then *)
(*     true *)
(*   else allowed_cross_call_b pol cp f. *)

End POLICY.

Section MATCH_POLICIES.

Context {C F1 F2: Type} {LC: Linker C} {LF1: Linker F1} {LF2: Linker F2}.
Context {CF1: has_comp F1} {CF2: has_comp F2}.
Context {FD1: @is_fundef F1 _} {FD2: @is_fundef F2 _}.
Variable match_fundef: C -> F1 -> F2 -> Prop.
Context {match_fundef_comp: has_comp_match (fun ctx f1 f2 => match_fundef ctx f1 f2)}.

(* The definition of matching policies between languages must depend on how the function names are
 compiled *)
Definition match_pol_gen (ctx: C) (pol: t (F := F1)) (tpol: t (F := F2)) :=
  forall f tf,
    match_fundef ctx f tf ->
    forall cp,
      allowed_call pol cp f <-> allowed_call tpol cp tf.

End MATCH_POLICIES.

(* A definition that ignores the context *)
Definition match_pol {F1 F2: Type} {CF1: has_comp F1} {CF2: has_comp F2} {FD1: @is_fundef F1 _} {FD2: @is_fundef F2 _}
           (match_fundef: F1 -> F2 -> Prop)
           (f1: Policy.t (F := F1)) (f2: Policy.t (F := F2)) : Prop :=
  match_pol_gen (fun _: unit => match_fundef) tt f1 f2.
