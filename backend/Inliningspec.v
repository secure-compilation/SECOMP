(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** RTL function inlining: relational specification *)

Require Import Coqlib Wfsimpl Maps Errors Integers.
Require Import AST Linking.
Require Import Op Registers RTL.
Require Import Inlining.

(** ** Soundness of function environments. *)

(** A compile-time function environment is compatible with a whole
  program if the following condition holds. *)

Definition fenv_compat (p: program) (fenv: funenv) : Prop :=
  forall id f,
  fenv!id = Some f ->
  (prog_defmap p)!id = Some (Gfun (Internal f)).

Lemma funenv_program_compat:
  forall p, fenv_compat p (funenv_program p).
Proof.
  set (P := fun (dm: PTree.t (globdef fundef unit)) (fenv: funenv) =>
              forall id f,
              fenv!id = Some f ->
              dm!id = Some (Gfun (Internal f))).
  assert (REMOVE: forall dm fenv id g,
             P dm fenv ->
             P (PTree.set id g dm) (PTree.remove id fenv)).
  { unfold P; intros. rewrite PTree.grspec in H0. destruct (PTree.elt_eq id0 id).
    discriminate.
    rewrite PTree.gso; auto.
  }
  assert (ADD: forall io dm dm' fenv idg,
             P dm fenv ->
             P (PTree.set (fst idg) (snd idg) dm) (add_globdef io dm' fenv idg)).
  { intros io dm dm' fenv [id g]; simpl; intros.
    destruct g as [[f|ef] | v]; auto.
    destruct (should_inline io id f && no_cross_calls dm' f); auto.
    red; intros. rewrite ! PTree.gsspec in *.
    destruct (peq id0 id); auto. inv H0; eauto.
  }
  assert (REC: forall io dm' l dm fenv,
            P dm fenv ->
            P (fold_left (fun x idg => PTree.set (fst idg) (snd idg) x) l dm)
              (fold_left (add_globdef io dm') l fenv)).
  { induction l; simpl; intros.
  - auto.
  - apply IHl. apply ADD; auto.
  }
  intros. apply REC. red; intros.  rewrite PTree.gempty in H; discriminate.
Qed.

Lemma fenv_compat_linkorder:
  forall cunit prog fenv,
  linkorder cunit prog -> fenv_compat cunit fenv -> fenv_compat prog fenv.
Proof.
  intros; red; intros. apply H0 in H1.
  destruct (prog_defmap_linkorder _ _ _ _ H H1) as (gd' & P & Q).
  inv Q. inv H3. eauto.
Qed.

(** ** No cross-compartment calls in inlineable functions *)

(** Functions in the inlining environment have no cross-compartment calls:
    any [Icall] or [Itailcall] in their code is either to the same compartment
    or to the bottom compartment. For indirect calls ([inl r]), the function
    is not in the environment at all, so [False] is vacuously satisfied. *)

Definition fenv_no_cross_calls (p: program) (fenv: funenv) : Prop :=
  forall id f pc sig ros args res s,
    fenv!id = Some f ->
    (fn_code f)!pc = Some (Icall sig ros args res s) ->
    match ros with
    | inl _ => False
    | inr callee_id =>
      match (prog_defmap p)!callee_id with
      | Some (Gfun (Internal f')) => comp_of f = comp_of f'
      | Some (Gfun (External ef)) =>
        match ef with EF_external _ _ => False | _ => True end
      | _ => False
      end
    end.

Definition fenv_no_cross_tailcalls (p: program) (fenv: funenv) : Prop :=
  forall id f pc sig ros args,
    fenv!id = Some f ->
    (fn_code f)!pc = Some (Itailcall sig ros args) ->
    match ros with
    | inl _ => False
    | inr callee_id =>
      match (prog_defmap p)!callee_id with
      | Some (Gfun (Internal f')) => comp_of f = comp_of f'
      | Some (Gfun (External ef)) =>
        match ef with EF_external _ _ => False | _ => True end
      | _ => False
      end
    end.

Remark fold_andb_negb_true:
  forall {A: Type} (check: A -> bool) l b,
  fold_left (fun acc (p: positive * A) => acc && negb (check (snd p))) l b = true ->
  b = true /\ forall k v, In (k, v) l -> check v = false.
Proof.
  induction l; simpl; intros.
  - split; auto. intros; contradiction.
  - destruct a as [k' v']. simpl in H.
    apply IHl in H. destruct H as [H1 H2].
    apply andb_true_iff in H1. destruct H1 as [H1 H3].
    apply negb_true_iff in H3.
    split; auto. intros k v [E | IN].
    + inv E; auto.
    + eauto.
Qed.

Lemma no_cross_calls_spec:
  forall dm f,
    no_cross_calls dm f = true ->
    forall pc i, (fn_code f)!pc = Some i -> is_cross_call dm (comp_of f) i = false.
Proof.
  unfold no_cross_calls. intros dm f H pc i Hi.
  rewrite PTree.fold_spec in H.
  apply fold_andb_negb_true in H. destruct H as [_ H].
  apply (H pc). apply PTree.elements_correct; auto.
Qed.

Remark funenv_program_ncc_aux:
  forall io dm l fenv,
  (forall id f, fenv!id = Some f -> no_cross_calls dm f = true) ->
  forall id f, (fold_left (add_globdef io dm) l fenv)!id = Some f ->
               no_cross_calls dm f = true.
Proof.
  induction l as [|[id' g'] l IHl]; simpl; intros.
  - eauto.
  - eapply IHl. 2: eauto.
    intros id0 f0 H1. simpl in H1.
    destruct g' as [[f'|ef'] | v'].
    + destruct (should_inline io id' f' && no_cross_calls dm f') eqn:E.
      * rewrite PTree.gsspec in H1. destruct (peq id0 id').
        -- inv H1. apply andb_true_iff in E. destruct E; auto.
        -- eauto.
      * rewrite PTree.grspec in H1. destruct (PTree.elt_eq id0 id'); [discriminate|]. eauto.
    + rewrite PTree.grspec in H1. destruct (PTree.elt_eq id0 id'); [discriminate|]. eauto.
    + rewrite PTree.grspec in H1. destruct (PTree.elt_eq id0 id'); [discriminate|]. eauto.
Qed.

Lemma funenv_program_no_cross_calls:
  forall p, fenv_no_cross_calls p (funenv_program p).
Proof.
  intros p. red; intros id f pc sig ros args res s FENV CODE.
  set (dm := prog_defmap p) in *.
  set (io := inlining_analysis p) in *.
  assert (NCC: no_cross_calls dm f = true).
  { unfold funenv_program in FENV. fold io in FENV. fold dm in FENV.
    eapply funenv_program_ncc_aux; eauto.
    intros. rewrite PTree.gempty in H; discriminate.
  }
  exploit no_cross_calls_spec; eauto.
  simpl. destruct ros as [r | callee_id].
  - intro H. discriminate.
  - destruct (dm ! callee_id) as [[[f0|e]|]|] eqn:E; intro H; try discriminate.
    + destruct (cp_eq_dec (comp_of f) (comp_of f0)); auto. discriminate.
    + destruct e; auto; discriminate.
Qed.

Lemma funenv_program_no_cross_tailcalls:
  forall p, fenv_no_cross_tailcalls p (funenv_program p).
Proof.
  intros p. red; intros id f pc sig ros args FENV CODE.
  set (dm := prog_defmap p) in *.
  set (io := inlining_analysis p) in *.
  assert (NCC: no_cross_calls dm f = true).
  { unfold funenv_program in FENV. fold io in FENV. fold dm in FENV.
    eapply funenv_program_ncc_aux; eauto.
    intros. rewrite PTree.gempty in H; discriminate.
  }
  exploit no_cross_calls_spec; eauto.
  simpl. destruct ros as [r | callee_id].
  - intro H. discriminate.
  - destruct (dm ! callee_id) as [[[f0|e]|]|] eqn:E; intro H; try discriminate.
    + destruct (cp_eq_dec (comp_of f) (comp_of f0)); auto. discriminate.
    + destruct e; auto; discriminate.
Qed.

(** ** Properties of shifting *)

Lemma shiftpos_eq: forall x y, Zpos (shiftpos x y) = (Zpos x + Zpos y) - 1.
Proof.
  intros. unfold shiftpos. zify.  try rewrite Pos2Z.inj_sub. auto.
  zify. lia.
Qed.

Lemma shiftpos_inj:
  forall x y n, shiftpos x n = shiftpos y n -> x = y.
Proof.
  intros.
  assert (Zpos (shiftpos x n) = Zpos (shiftpos y n)) by congruence.
  rewrite ! shiftpos_eq in H0.
  assert (Z.pos x = Z.pos y) by lia.
  congruence.
Qed.

Lemma shiftpos_diff:
  forall x y n, x <> y -> shiftpos x n <> shiftpos y n.
Proof.
  intros; red; intros. elim H. eapply shiftpos_inj; eauto.
Qed.

Lemma shiftpos_above:
  forall x n, Ple n (shiftpos x n).
Proof.
  intros. unfold Ple; zify. rewrite shiftpos_eq. extlia.
Qed.

Lemma shiftpos_not_below:
  forall x n, Plt (shiftpos x n) n -> False.
Proof.
  intros. generalize (shiftpos_above x n). extlia.
Qed.

Lemma shiftpos_below:
  forall x n, Plt (shiftpos x n) (Pos.add x n).
Proof.
  intros. unfold Plt; zify. rewrite shiftpos_eq. lia.
Qed.

Lemma shiftpos_le:
  forall x y n, Ple x y -> Ple (shiftpos x n) (shiftpos y n).
Proof.
  intros. unfold Ple in *; zify. rewrite ! shiftpos_eq. lia.
Qed.


(** ** Working with the state monad *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: state) (i: sincr s1 s3),
  bind f g s1 = R y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = R x s2 i1 /\ g x s2 = R y s3 i2.
Proof.
  unfold bind; intros. destruct (f s1). exists x; exists s'; exists I.
  destruct (g x s'). inv H. exists I0; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (R _ _ _ = R _ _ _) =>
      inversion H; clear H; try subst
  | (ret _ _ = R _ _ _) =>
      inversion H; clear H; try subst
  | (bind ?F ?G ?S = R ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = R _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = R ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

Fixpoint mlist_iter2 {A B: Type} (f: A -> B -> mon unit) (l: list (A*B)): mon unit :=
  match l with
  | nil => ret tt
  | (x,y) :: l' => do z <- f x y; mlist_iter2 f l'
  end.

Remark mlist_iter2_fold:
  forall (A B: Type) (f: A -> B -> mon unit) l s,
  exists i,
  mlist_iter2 f l s =
  R tt (fold_left (fun a p => match f (fst p) (snd p) a with R _ s2 _ => s2 end) l s) i.
Proof.
  induction l; simpl; intros.
  exists (sincr_refl s); auto.
  destruct a as [x y]. unfold bind. simpl. destruct (f x y s) as [xx s1 i1].
  destruct (IHl s1) as [i2 EQ]. rewrite EQ. econstructor; eauto.
Qed.

Lemma ptree_mfold_spec:
  forall (A: Type) (f: positive -> A -> mon unit) t s x s' i,
  ptree_mfold f t s = R x s' i ->
  exists i', mlist_iter2 f (PTree.elements t) s = R tt s' i'.
Proof.
  intros.
  destruct (mlist_iter2_fold _ _ f (PTree.elements t) s) as [i' EQ].
  unfold ptree_mfold in H. inv H. rewrite PTree.fold_spec.
  econstructor. eexact EQ.
Qed.

(** ** Relational specification of the translation of moves *)

Inductive tr_moves (c: code) : node -> list reg -> list reg -> node -> Prop :=
  | tr_moves_cons: forall pc1 src srcs dst dsts pc2 pc3,
      tr_moves c pc1 srcs dsts pc2 ->
      c!pc2 = Some(Iop Omove (src :: nil) dst pc3) ->
      tr_moves c pc1 (src :: srcs) (dst :: dsts) pc3
  | tr_moves_nil: forall srcs dsts pc,
      srcs = nil \/ dsts = nil ->
      tr_moves c pc srcs dsts pc.

Lemma add_moves_unchanged:
  forall srcs dsts pc2 s pc1 s' i pc,
  add_moves srcs dsts pc2 s = R pc1 s' i ->
  Plt pc s.(st_nextnode) \/ Ple s'.(st_nextnode) pc ->
  s'.(st_code)!pc = s.(st_code)!pc.
Proof.
  induction srcs; simpl; intros.
  monadInv H. auto.
  destruct dsts; monadInv H. auto.
  transitivity (st_code s0)!pc. eapply IHsrcs; eauto. monadInv EQ; simpl. extlia.
  monadInv EQ; simpl. apply PTree.gso.
  inversion INCR0; simpl in *. extlia.
Qed.

Lemma add_moves_spec:
  forall srcs dsts pc2 s pc1 s' i c,
  add_moves srcs dsts pc2 s = R pc1 s' i ->
  (forall pc, Ple s.(st_nextnode) pc -> Plt pc s'.(st_nextnode) -> c!pc = s'.(st_code)!pc) ->
  tr_moves c pc1 srcs dsts pc2.
Proof.
  induction srcs; simpl; intros.
  monadInv H. apply tr_moves_nil; auto.
  destruct dsts; monadInv H. apply tr_moves_nil; auto.
  apply tr_moves_cons with x. eapply IHsrcs; eauto.
  intros. inversion INCR. apply H0; extlia.
  monadInv EQ.
  rewrite H0. erewrite add_moves_unchanged; eauto.
  simpl. apply PTree.gss.
  simpl. extlia.
  extlia.
  inversion INCR; inversion INCR0; simpl in *; extlia.
Qed.

(** ** Relational specification of CFG expansion *)

Section INLINING_SPEC.

Variable fenv: funenv.

Definition context_below (ctx1 ctx2: context): Prop :=
  Ple (Pos.add ctx1.(dreg) ctx1.(mreg)) ctx2.(dreg).

Definition context_stack_call (ctx1 ctx2: context): Prop :=
  ctx1.(mstk) >= 0 /\ ctx1.(dstk) + ctx1.(mstk) <= ctx2.(dstk).

Definition context_stack_tailcall (ctx1: context) (f: function) (ctx2: context) : Prop :=
  ctx2.(dstk) = align ctx1.(dstk) (min_alignment f.(fn_stacksize)).

Section INLINING_BODY_SPEC.

Variable stacksize: Z.

Inductive tr_instr: context -> compartment -> node -> instruction -> code -> Prop :=
  | tr_nop: forall ctx cp pc c s,
      c!(spc ctx pc) = Some (Inop (spc ctx s)) ->
      tr_instr ctx cp pc (Inop s) c
  | tr_op: forall ctx cp pc c op args res s,
      Ple res ctx.(mreg) ->
      c!(spc ctx pc) = Some (Iop (sop ctx op) (sregs ctx args) (sreg ctx res) (spc ctx s)) ->
      tr_instr ctx cp pc (Iop op args res s) c
  | tr_load: forall ctx cp pc c chunk addr args res s,
      Ple res ctx.(mreg) ->
      c!(spc ctx pc) = Some (Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx res) (spc ctx s)) ->
      tr_instr ctx cp pc (Iload chunk addr args res s) c
  | tr_store: forall ctx cp pc c chunk addr args src s,
      c!(spc ctx pc) = Some (Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx s)) ->
      tr_instr ctx cp pc (Istore chunk addr args src s) c
  | tr_call: forall ctx cp pc c sg ros args res s,
      Ple res ctx.(mreg) ->
      c!(spc ctx pc) = Some (Icall sg (sros ctx ros) (sregs ctx args) (sreg ctx res) (spc ctx s)) ->
      tr_instr ctx cp pc (Icall sg ros args res s) c
  | tr_call_inlined:forall ctx cp pc sg id args res s c f pc1 ctx',
      forall (SAMECOMP: comp_of f = cp),
      Ple res ctx.(mreg) ->
      fenv!id = Some f ->
      c!(spc ctx pc) = Some(Inop pc1) ->
      tr_moves c pc1 (sregs ctx args) (sregs ctx' f.(fn_params)) (spc ctx' f.(fn_entrypoint)) ->
      tr_funbody ctx' f c ->
      ctx'.(retinfo) = Some(spc ctx s, sreg ctx res) ->
      context_below ctx ctx' ->
      context_stack_call ctx ctx' ->
      tr_instr ctx cp pc (Icall sg (inr _ id) args res s) c
  | tr_tailcall: forall ctx cp pc c sg ros args,
      c!(spc ctx pc) = Some (Itailcall sg (sros ctx ros) (sregs ctx args)) ->
      ctx.(retinfo) = None ->
      tr_instr ctx cp pc (Itailcall sg ros args) c
  | tr_tailcall_call: forall ctx cp pc c sg ros args res s,
      c!(spc ctx pc) = Some (Icall sg (sros ctx ros) (sregs ctx args) res s) ->
      ctx.(retinfo) = Some(s, res) ->
      tr_instr ctx cp pc (Itailcall sg ros args) c
  | tr_tailcall_inlined: forall ctx cp pc sg id args c f pc1 ctx',
      forall (SAMECOMP: comp_of f = cp),
      fenv!id = Some f ->
      c!(spc ctx pc) = Some(Inop pc1) ->
      tr_moves c pc1 (sregs ctx args) (sregs ctx' f.(fn_params)) (spc ctx' f.(fn_entrypoint)) ->
      tr_funbody ctx' f c ->
      ctx'.(retinfo) = ctx.(retinfo) ->
      context_below ctx ctx' ->
      context_stack_tailcall ctx f ctx' ->
      tr_instr ctx cp pc (Itailcall sg (inr _ id) args) c
  | tr_builtin: forall ctx cp pc c ef args res s,
      match res with BR r => Ple r ctx.(mreg) | _ => True end ->
      c!(spc ctx pc) = Some (Ibuiltin ef (map (sbuiltinarg ctx) args) (sbuiltinres ctx res) (spc ctx s)) ->
      tr_instr ctx cp pc (Ibuiltin ef args res s) c
  | tr_cond: forall ctx cp pc cond args s1 s2 c,
      c!(spc ctx pc) = Some (Icond cond (sregs ctx args) (spc ctx s1) (spc ctx s2)) ->
      tr_instr ctx cp pc (Icond cond args s1 s2) c
  | tr_jumptable: forall ctx cp pc r tbl c,
      c!(spc ctx pc) = Some (Ijumptable (sreg ctx r) (List.map (spc ctx) tbl)) ->
      tr_instr ctx cp pc (Ijumptable r tbl) c
  | tr_return: forall ctx cp pc or c,
      c!(spc ctx pc) = Some (Ireturn (option_map (sreg ctx) or)) ->
      ctx.(retinfo) = None ->
      tr_instr ctx cp pc (Ireturn or) c
  | tr_return_inlined: forall ctx cp pc or c rinfo,
      c!(spc ctx pc) = Some (inline_return ctx or rinfo) ->
      ctx.(retinfo) = Some rinfo ->
      tr_instr ctx cp pc (Ireturn or) c

with tr_funbody: context -> function -> code -> Prop :=
  | tr_funbody_intro: forall ctx f c,
      (forall r, In r f.(fn_params) -> Ple r ctx.(mreg)) ->
      (forall pc i, f.(fn_code)!pc = Some i -> tr_instr ctx (comp_of f) pc i c) ->
      ctx.(mstk) = Z.max f.(fn_stacksize) 0 ->
      (min_alignment f.(fn_stacksize) | ctx.(dstk)) ->
      ctx.(dstk) >= 0 -> ctx.(dstk) + ctx.(mstk) <= stacksize ->
      tr_funbody ctx f c.

Definition fenv_agree (fe: funenv) : Prop :=
  forall id f, fe!id = Some f -> fenv!id = Some f.

Section EXPAND_INSTR.

Variable fe: funenv.
Hypothesis FE: fenv_agree fe.

Variable rec: forall fe', (size_fenv fe' < size_fenv fe)%nat -> context -> function -> mon unit.

Hypothesis rec_unchanged:
  forall fe' (L: (size_fenv fe' < size_fenv fe)%nat) ctx f s x s' i pc,
  rec fe' L ctx f s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Plt pc ctx.(dpc) ->
  s'.(st_code)!pc = s.(st_code)!pc.

Remark set_instr_other:
  forall pc instr s x s' i pc',
  set_instr pc instr s = R x s' i ->
  pc' <> pc ->
  s'.(st_code)!pc' = s.(st_code)!pc'.
Proof.
  intros. monadInv H; simpl. apply PTree.gso; auto.
Qed.

Remark set_instr_same:
  forall pc instr s x s' i c,
  set_instr pc instr s = R x s' i ->
  c!(pc) = s'.(st_code)!pc ->
  c!(pc) = Some instr.
Proof.
  intros. rewrite H0. monadInv H; simpl. apply PTree.gss.
Qed.

Lemma expand_instr_unchanged:
  forall ctx cp pc instr s x s' i pc',
  expand_instr fe rec ctx cp pc instr s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Plt pc' s.(st_nextnode) ->
  pc' <> spc ctx pc ->
  s'.(st_code)!pc' = s.(st_code)!pc'.
Proof.
  generalize set_instr_other; intros A.
  intros. unfold expand_instr in H; destruct instr; eauto.
(* call *)
  destruct (can_inline fe cp s1). eauto.
  monadInv H. unfold inline_function in EQ. monadInv EQ.
  transitivity (s2.(st_code)!pc'). eauto.
  transitivity (s5.(st_code)!pc'). eapply add_moves_unchanged; eauto.
    left. inversion INCR5. inversion INCR3. monadInv EQ1; simpl in *. extlia.
  transitivity (s4.(st_code)!pc'). eapply rec_unchanged; eauto.
    simpl. monadInv EQ; simpl. monadInv EQ1; simpl. extlia.
    simpl. monadInv EQ1; simpl. auto.
  monadInv EQ; simpl. monadInv EQ1; simpl. auto.
(* tailcall *)
  destruct (can_inline fe cp s1).
  destruct (retinfo ctx) as [[rpc rreg]|]; eauto.
  monadInv H. unfold inline_tail_function in EQ. monadInv EQ.
  transitivity (s2.(st_code)!pc'). eauto.
  transitivity (s5.(st_code)!pc'). eapply add_moves_unchanged; eauto.
    left. inversion INCR5. inversion INCR3. monadInv EQ1; simpl in *. extlia.
  transitivity (s4.(st_code)!pc'). eapply rec_unchanged; eauto.
    simpl. monadInv EQ; simpl. monadInv EQ1; simpl. extlia.
    simpl. monadInv EQ1; simpl. auto.
  monadInv EQ; simpl. monadInv EQ1; simpl. auto.
(* return *)
  destruct (retinfo ctx) as [[rpc rreg]|]; eauto.
Qed.

Lemma iter_expand_instr_unchanged:
  forall ctx cp pc l s x s' i,
  mlist_iter2 (expand_instr fe rec ctx cp) l s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Plt pc s.(st_nextnode) ->
  ~In pc (List.map (spc ctx) (List.map (@fst _ _) l)) ->
  list_norepet (List.map (@fst _ _) l) ->
  s'.(st_code)!pc = s.(st_code)!pc.
Proof.
  induction l; simpl; intros.
  (* base case *)
  monadInv H. auto.
  (* inductive case *)
  destruct a as [pc1 instr1]; simpl in *.
  monadInv H. inv H3.
  transitivity ((st_code s0)!pc).
  eapply IHl; eauto. destruct INCR; extlia. destruct INCR; extlia.
  eapply expand_instr_unchanged; eauto.
Qed.

Lemma expand_cfg_rec_unchanged:
  forall ctx f s x s' i pc,
  expand_cfg_rec fe rec ctx f s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Plt pc ctx.(dpc) ->
  s'.(st_code)!pc = s.(st_code)!pc.
Proof.
  intros. unfold expand_cfg_rec in H. monadInv H. inversion EQ.
  transitivity ((st_code s0)!pc).
  exploit ptree_mfold_spec; eauto. intros [INCR' ITER].
  eapply iter_expand_instr_unchanged; eauto.
    subst s0; auto.
    subst s0; simpl. extlia.
    red; intros. exploit list_in_map_inv; eauto. intros [pc1 [A B]].
    subst pc. unfold spc in H1. eapply shiftpos_not_below; eauto.
    apply PTree.elements_keys_norepet.
  subst s0; auto.
Qed.

Hypothesis rec_spec:
  forall fe' (L: (size_fenv fe' < size_fenv fe)%nat) ctx f s x s' i c,
  rec fe' L ctx f s = R x s' i ->
  fenv_agree fe' ->
  Ple (ctx.(dpc) + max_pc_function f) s.(st_nextnode) ->
  ctx.(mreg) = max_reg_function f ->
  Ple (Pos.add ctx.(dreg) ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 ->
  ctx.(mstk) = Z.max (fn_stacksize f) 0 ->
  (min_alignment (fn_stacksize f) | ctx.(dstk)) ->
  ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc, Ple ctx.(dpc) pc -> Plt pc s'.(st_nextnode) -> c!pc = s'.(st_code)!pc) ->
  tr_funbody ctx f c.

Remark min_alignment_pos:
  forall sz, min_alignment sz > 0.
Proof.
  intros; unfold min_alignment.
  destruct (zle sz 1). lia. destruct (zle sz 2). lia. destruct (zle sz 4); lia.
Qed.

Ltac inv_incr :=
  match goal with
  | [ H: sincr _ _ |- _ ] => destruct H; inv_incr
  | _ => idtac
  end.

Lemma expand_instr_spec:
  forall ctx cp pc instr s x s' i c,
  expand_instr fe rec ctx cp pc instr s = R x s' i ->
  (forall r, instr_defs instr = Some r -> Ple r ctx.(mreg)) ->
  Plt (spc ctx pc) s.(st_nextnode) ->
  Ple (ctx.(dreg) + ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 -> ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc', Ple s.(st_nextnode) pc' -> Plt pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  c!(spc ctx pc) = s'.(st_code)!(spc ctx pc) ->
  tr_instr ctx cp pc instr c.
Proof.
  intros until c; intros EXP DEFS OPC OREG STK1 STK2 STK3 S1 S2.
  generalize set_instr_same; intros BASE.
  unfold expand_instr in EXP; destruct instr; simpl in DEFS;
  try (econstructor; eauto; fail).
(* call *)
  destruct (can_inline fe cp s1) as [|id f P Q R].
  (* not inlined *)
  eapply tr_call; eauto.
  (* inlined *)
  subst s1.
  monadInv EXP. unfold inline_function in EQ; monadInv EQ.
  set (ctx' := callcontext ctx x1 x2 (max_reg_function f) (fn_stacksize f) n r).
  inversion EQ0; inversion EQ1; inversion EQ. inv_incr.
  apply tr_call_inlined with (pc1 := x0) (ctx' := ctx') (f := f); auto.
  eapply BASE; eauto.
  eapply add_moves_spec; eauto.
    intros. rewrite S1. eapply set_instr_other; eauto. unfold node; extlia.
    extlia. extlia.
  eapply rec_spec; eauto.
    red; intros. rewrite PTree.grspec in H. destruct (PTree.elt_eq id0 id); try discriminate. auto.
    simpl. subst s2; simpl in *; extlia.
    simpl. subst s3; simpl in *; extlia.
    simpl. extlia.
    simpl. apply align_divides. apply min_alignment_pos.
    assert (dstk ctx + mstk ctx <= dstk ctx'). simpl. apply align_le. apply min_alignment_pos. lia.
    lia.
    intros. simpl in H. rewrite S1.
    transitivity (s1.(st_code)!pc0). eapply set_instr_other; eauto. unfold node in *; extlia.
    eapply add_moves_unchanged; eauto. unfold node in *; extlia. extlia.
  red; simpl. subst s2; simpl in *. extlia.
  red; simpl. split. auto. apply align_le. apply min_alignment_pos.
(* tailcall *)
  destruct (can_inline fe cp s1) as [|id f P Q R].
  (* not inlined *)
  destruct (retinfo ctx) as [[rpc rreg] | ] eqn:?.
  (* turned into a call *)
  eapply tr_tailcall_call; eauto.
  (* preserved *)
  eapply tr_tailcall; eauto.
  (* inlined *)
  subst s1.
  monadInv EXP. unfold inline_function in EQ; monadInv EQ.
  set (ctx' := tailcontext ctx x1 x2 (max_reg_function f) (fn_stacksize f)) in *.
  inversion EQ0; inversion EQ1; inversion EQ. inv_incr.
  apply tr_tailcall_inlined with (pc1 := x0) (ctx' := ctx') (f := f); auto.
  eapply BASE; eauto.
  eapply add_moves_spec; eauto.
    intros. rewrite S1. eapply set_instr_other; eauto. unfold node; extlia. extlia. extlia.
  eapply rec_spec; eauto.
    red; intros. rewrite PTree.grspec in H. destruct (PTree.elt_eq id0 id); try discriminate. auto.
    simpl. subst s3; simpl in *. subst s2; simpl in *. extlia.
    simpl. subst s3; simpl in *; extlia.
    simpl. extlia.
    simpl. apply align_divides. apply min_alignment_pos.
    assert (dstk ctx <= dstk ctx'). simpl. apply align_le. apply min_alignment_pos. lia.
    lia.
    intros. simpl in H. rewrite S1.
    transitivity (s1.(st_code))!pc0. eapply set_instr_other; eauto. unfold node in *; extlia.
    eapply add_moves_unchanged; eauto. unfold node in *; extlia. extlia.
  red; simpl.
subst s2; simpl in *; extlia.
  red; auto.
(* builtin *)
  eapply tr_builtin; eauto. destruct b; eauto.
(* return *)
  destruct (retinfo ctx) as [[rpc rreg] | ] eqn:?.
  (* inlined *)
  eapply tr_return_inlined; eauto.
  (* unchanged *)
  eapply tr_return; eauto.
Qed.

Lemma iter_expand_instr_spec:
  forall ctx cp l s x s' i c,
  mlist_iter2 (expand_instr fe rec ctx cp) l s = R x s' i ->
  list_norepet (List.map (@fst _ _) l) ->
  (forall pc instr r, In (pc, instr) l -> instr_defs instr = Some r -> Ple r ctx.(mreg)) ->
  (forall pc instr, In (pc, instr) l -> Plt (spc ctx pc) s.(st_nextnode)) ->
  Ple (ctx.(dreg) + ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 -> ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc', Ple s.(st_nextnode) pc' -> Plt pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  (forall pc instr, In (pc, instr) l -> c!(spc ctx pc) = s'.(st_code)!(spc ctx pc)) ->
  forall pc instr, In (pc, instr) l -> tr_instr ctx cp pc instr c.
Proof.
  induction l; simpl; intros.
  (* base case *)
  contradiction.
  (* inductive case *)
  destruct a as [pc1 instr1]; simpl in *. inv H0. monadInv H. inv_incr.
  assert (A: Ple ctx.(dpc) s0.(st_nextnode)).
    assert (B: Plt (spc ctx pc) (st_nextnode s)) by eauto.
    unfold spc in B. generalize (shiftpos_above pc (dpc ctx)). extlia.
  destruct H9. inv H.
  (* same pc *)
  eapply expand_instr_spec; eauto.
  lia.
  intros.
    transitivity ((st_code s')!pc').
    apply H7. auto. extlia.
    eapply iter_expand_instr_unchanged; eauto.
    red; intros. rewrite list_map_compose in H9. exploit list_in_map_inv; eauto.
    intros [[pc0 instr0] [P Q]]. simpl in P.
    assert (Plt (spc ctx pc0) (st_nextnode s)) by eauto. extlia.
  transitivity ((st_code s')!(spc ctx pc)).
    eapply H8; eauto.
    eapply iter_expand_instr_unchanged; eauto.
    assert (Plt (spc ctx pc) (st_nextnode s)) by eauto. extlia.
    red; intros. rewrite list_map_compose in H. exploit list_in_map_inv; eauto.
    intros [[pc0 instr0] [P Q]]. simpl in P.
    assert (pc = pc0) by (eapply shiftpos_inj; eauto). subst pc0.
    elim H12. change pc with (fst (pc, instr0)). apply List.in_map; auto.
  (* older pc *)
  inv_incr. eapply IHl; eauto.
  intros. eapply Pos.lt_le_trans. eapply H2. right; eauto. extlia.
  intros; eapply Ple_trans; eauto.
  intros. apply H7; auto. extlia.
Qed.

Lemma expand_cfg_rec_spec:
  forall ctx f s x s' i c,
  expand_cfg_rec fe rec ctx f s = R x s' i ->
  Ple (ctx.(dpc) + max_pc_function f) s.(st_nextnode) ->
  ctx.(mreg) = max_reg_function f ->
  Ple (ctx.(dreg) + ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 ->
  ctx.(mstk) = Z.max (fn_stacksize f) 0 ->
  (min_alignment (fn_stacksize f) | ctx.(dstk)) ->
  ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc', Ple ctx.(dpc) pc' -> Plt pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  tr_funbody ctx f c.
Proof.
  intros. unfold expand_cfg_rec in H. monadInv H. inversion EQ.
  constructor.
  intros. rewrite H1. eapply max_reg_function_params; eauto.
  intros. exploit ptree_mfold_spec; eauto. intros [INCR' ITER].
  eapply iter_expand_instr_spec; eauto.
    apply PTree.elements_keys_norepet.
    intros. rewrite H1. eapply max_reg_function_def with (i := instr); eauto.
    eapply PTree.elements_complete; eauto.
  intros.
    assert (Ple pc0 (max_pc_function f)).
      eapply max_pc_function_sound. eapply PTree.elements_complete; eauto.
      eapply Pos.lt_le_trans. apply shiftpos_below. subst s0; simpl; extlia.
  subst s0; simpl; auto.
  intros. apply H8; auto. subst s0; simpl in H11; extlia.
  intros. apply H8. apply shiftpos_above.
  assert (Ple pc0 (max_pc_function f)).
    eapply max_pc_function_sound. eapply PTree.elements_complete; eauto.
  eapply Pos.lt_le_trans. apply shiftpos_below. inversion i; extlia.
  apply PTree.elements_correct; auto.
  auto. auto. auto.
  inversion INCR0. subst s0; simpl in STKSIZE; extlia.
Qed.

End EXPAND_INSTR.

Lemma expand_cfg_unchanged:
  forall fe ctx f s x s' i pc,
  expand_cfg fe ctx f s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Plt pc ctx.(dpc) ->
  s'.(st_code)!pc = s.(st_code)!pc.
Proof.
  intros fe0; pattern fe0. apply well_founded_ind with (R := ltof _ size_fenv).
  apply well_founded_ltof.
  intros. unfold expand_cfg in H0. rewrite unroll_Fixm in H0.
  eapply expand_cfg_rec_unchanged; eauto. assumption.
Qed.

Lemma expand_cfg_spec:
  forall fe ctx f s x s' i c,
  expand_cfg fe ctx f s = R x s' i ->
  fenv_agree fe ->
  Ple (ctx.(dpc) + max_pc_function f) s.(st_nextnode) ->
  ctx.(mreg) = max_reg_function f ->
  Ple (ctx.(dreg) + ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 ->
  ctx.(mstk) = Z.max (fn_stacksize f) 0 ->
  (min_alignment (fn_stacksize f) | ctx.(dstk)) ->
  ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc', Ple ctx.(dpc) pc' -> Plt pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  tr_funbody ctx f c.
Proof.
  intros fe0; pattern fe0. apply well_founded_ind with (R := ltof _ size_fenv).
  apply well_founded_ltof.
  intros. unfold expand_cfg in H0. rewrite unroll_Fixm in H0.
  eapply expand_cfg_rec_spec; eauto.
  simpl. intros. eapply expand_cfg_unchanged; eauto. assumption.
Qed.

End INLINING_BODY_SPEC.

End INLINING_SPEC.

(** ** Stack size preservation with empty funenv *)

Lemma set_instr_stksize:
  forall pc i s x s' inc,
  set_instr pc i s = R x s' inc ->
  st_stksize s' = st_stksize s.
Proof.
  intros. unfold set_instr in H. inv H. reflexivity.
Qed.

Lemma expand_instr_empty_stksize:
  forall rec ctx cp pc i s x s' inc,
  expand_instr (PTree.empty _) rec ctx cp pc i s = R x s' inc ->
  st_stksize s' = st_stksize s.
Proof.
  unfold expand_instr. intros rec ctx cp pc i.
  destruct i; intros; try (eapply set_instr_stksize; eauto; fail).
  - (* Icall *)
    destruct s0 as [r0 | id0]; cbn [can_inline] in H; simpl in H;
      eapply set_instr_stksize; eauto.
  - (* Itailcall *)
    destruct s0 as [r0 | id0]; cbn [can_inline] in H; simpl in H;
      destruct (retinfo ctx) as [[rpc rreg]|]; eapply set_instr_stksize; eauto.
  - (* Ireturn *)
    destruct (retinfo ctx); eapply set_instr_stksize; eauto.
Qed.

Lemma ptree_mfold_stksize:
  forall {A: Type} (f: positive -> A -> mon unit) t s,
  (forall k v s0 x s0' inc, f k v s0 = R x s0' inc -> st_stksize s0' = st_stksize s0) ->
  st_stksize (PTree.fold (fun s1 k v => match f k v s1 return _ with R _ s2 _ => s2 end) t s) = st_stksize s.
Proof.
  intros. apply PTree_Properties.fold_rec.
  - auto.
  - reflexivity.
  - intros. destruct (f k v a) eqn:Hfkv.
    rewrite (H _ _ _ _ _ _ Hfkv). auto.
Qed.

Lemma expand_cfg_empty_stksize:
  forall ctx f s x s' inc,
  expand_cfg (PTree.empty _) ctx f s = R x s' inc ->
  st_stksize s' = Z.max (st_stksize s) (dstk ctx + mstk ctx).
Proof.
  intros. unfold expand_cfg in H. rewrite unroll_Fixm in H.
  unfold expand_cfg_rec in H. simpl in H. monadInv H.
  unfold ptree_mfold in EQ0. inv EQ0.
  unfold request_stack in EQ. inv EQ. simpl.
  rewrite ptree_mfold_stksize. reflexivity.
  intros. eapply expand_instr_empty_stksize; eauto.
Qed.

(** ** Relational specification of the translation of a function *)

Inductive tr_function: program -> function -> function -> Prop :=
  | tr_function_intro: forall p fenv f f' ctx,
      fenv_compat p fenv ->
      fenv_no_cross_calls p fenv ->
      tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code) ->
      ctx.(dstk) = 0 ->
      ctx.(retinfo) = None ->
      comp_of f' = (comp_of f) ->
      f'.(fn_sig) = f.(fn_sig) ->
      f'.(fn_params) = sregs ctx f.(fn_params) ->
      f'.(fn_entrypoint) = spc ctx f.(fn_entrypoint) ->
      0 <= fn_stacksize f' < Ptrofs.max_unsigned ->
      (no_cross_calls (prog_defmap p) f = true \/
       (fenv = PTree.empty _ /\ fn_stacksize f' = ctx.(dstk) + ctx.(mstk))) ->
      tr_function p f f'.

Lemma is_cross_call_linkorder:
  forall cunit prog cp i,
  linkorder cunit prog ->
  is_cross_call (prog_defmap cunit) cp i = false ->
  is_cross_call (prog_defmap prog) cp i = false.
Proof.
  intros cunit prog cp i LO H. unfold is_cross_call in *.
  destruct i; auto; destruct s0 as [?r|?id]; auto;
  destruct ((prog_defmap cunit) ! id) as [[[?|[]]|]|] eqn:E; try discriminate;
  destruct (prog_defmap_linkorder _ _ _ _ LO E) as (gd2 & P & Q);
  rewrite P; inv Q; try inv H1; try inv H0; auto.
Qed.

Lemma fenv_no_cross_calls_linkorder:
  forall cunit prog fenv,
  linkorder cunit prog ->
  fenv_no_cross_calls cunit fenv ->
  fenv_no_cross_calls prog fenv.
Proof.
  intros cunit prog fenv LO NCC.
  red; intros id f pc sig ros args res s FENV CODE.
  specialize (NCC _ _ _ _ _ _ _ _ FENV CODE).
  destruct ros as [r | callee_id]; auto.
  destruct ((prog_defmap cunit) ! callee_id) as [[[fi|ef]|]|] eqn:E.
  - destruct (prog_defmap_linkorder _ _ _ _ LO E) as (gd2 & P & Q).
    rewrite P. inv Q. inv H0. auto.
  - destruct (prog_defmap_linkorder _ _ _ _ LO E) as (gd2 & P & Q).
    rewrite P. inv Q. inv H0; try contradiction; auto.
  - contradiction.
  - contradiction.
Qed.

Lemma no_cross_calls_from_spec:
  forall dm f,
  (forall pc i, (fn_code f)!pc = Some i -> is_cross_call dm (comp_of f) i = false) ->
  no_cross_calls dm f = true.
Proof.
  intros dm f SPEC. unfold no_cross_calls. rewrite PTree.fold_spec.
  assert (forall l b, b = true ->
    (forall k v, In (k, v) l -> (fn_code f)!k = Some v) ->
    fold_left (fun acc p => acc && negb (is_cross_call dm (comp_of f) (snd p))) l b = true).
  { induction l as [|[k v] l IHl]; simpl; intros.
    - auto.
    - apply IHl.
      + subst b. simpl. rewrite (SPEC k v); auto.
      + intros. apply H0. right; auto. }
  apply H; auto.
  intros. apply PTree.elements_complete; auto.
Qed.

Lemma no_cross_calls_linkorder:
  forall cunit prog f,
  linkorder cunit prog ->
  no_cross_calls (prog_defmap cunit) f = true ->
  no_cross_calls (prog_defmap prog) f = true.
Proof.
  intros cunit prog f LO NCC.
  apply no_cross_calls_from_spec.
  intros pc i Hi.
  eapply is_cross_call_linkorder; eauto.
  eapply no_cross_calls_spec; eauto.
Qed.

Lemma tr_function_linkorder:
  forall cunit prog f f',
  linkorder cunit prog ->
  tr_function cunit f f' ->
  tr_function prog f f'.
Proof.
  intros. inv H0. econstructor; eauto.
  eapply fenv_compat_linkorder; eauto.
  eapply fenv_no_cross_calls_linkorder; eauto.
  destruct H11 as [NCC | [EMPTY SZEQ]].
  - left. eapply no_cross_calls_linkorder; eauto.
  - right. split; auto.
Qed.

Lemma fenv_no_cross_calls_empty:
  forall p, fenv_no_cross_calls p (PTree.empty _).
Proof.
  intros p. red; intros. rewrite PTree.gempty in H. discriminate.
Qed.

Lemma transf_function_spec:
  forall cunit f f',
  transf_function (funenv_program cunit) (prog_defmap cunit) f = OK f' ->
  tr_function cunit f f'.
Proof.
  intros. unfold transf_function in H.
  set (fenv := funenv_program cunit) in *.
  destruct (no_cross_calls (prog_defmap cunit) f) eqn:NCC_EQ.
  - (* no_cross_calls = true: use normal funenv *)
    destruct (expand_function fenv f initstate) as [ctx s i] eqn:?.
    destruct (zlt (st_stksize s) Ptrofs.max_unsigned); inv H.
    monadInv Heqr. set (ctx := initcontext x x0 (max_reg_function f) (fn_stacksize f)) in *.
  Opaque initstate.
    destruct INCR3. inversion EQ1. inversion EQ.
    apply tr_function_intro with fenv ctx; auto.
    apply funenv_program_compat.
    apply funenv_program_no_cross_calls.
    eapply expand_cfg_spec with (fe := fenv); eauto.
      red; auto.
      unfold ctx; rewrite <- H1; rewrite <- H2; rewrite <- H3; simpl. extlia.
      unfold ctx; rewrite <- H0; rewrite <- H1; simpl. extlia.
      simpl. extlia.
      simpl. apply Z.divide_0_r.
      simpl. lia.
    simpl. lia.
    simpl. split; auto. destruct INCR2. destruct INCR1. destruct INCR0. destruct INCR.
    simpl. change 0 with (st_stksize initstate). lia.
  - (* no_cross_calls = false: use empty funenv *)
    set (fenv' := PTree.empty function) in *.
    destruct (expand_function fenv' f initstate) as [ctx s i] eqn:?.
    destruct (zlt (st_stksize s) Ptrofs.max_unsigned); inv H.
    monadInv Heqr. set (ctx := initcontext x x0 (max_reg_function f) (fn_stacksize f)) in *.
  Opaque initstate.
    destruct INCR3. inversion EQ1. inversion EQ.
    apply tr_function_intro with fenv' ctx; auto.
    { red. intros. rewrite PTree.gempty in H. discriminate. }
    apply fenv_no_cross_calls_empty.
    eapply expand_cfg_spec with (fe := fenv'); eauto.
      red; auto.
      unfold ctx; rewrite <- H1; rewrite <- H2; rewrite <- H3; simpl. extlia.
      unfold ctx; rewrite <- H0; rewrite <- H1; simpl. extlia.
      simpl. extlia.
      simpl. apply Z.divide_0_r.
      simpl. lia.
    simpl. lia.
    simpl. split; auto. destruct INCR2. destruct INCR1. destruct INCR0. destruct INCR.
    simpl. change 0 with (st_stksize initstate). lia.
    right. split; auto.
    (* fn_stacksize f' = dstk ctx + mstk ctx: with empty fenv, expand_cfg doesn't
       increase st_stksize beyond request_stack(dstk + mstk). *)
    simpl.
    exploit expand_cfg_empty_stksize; eauto.
    subst s0 s1. simpl. change (st_stksize initstate) with 0.
    intro. rewrite H. apply Z.max_case_strong; intros; apply Z.max_case_strong; lia.
Qed.