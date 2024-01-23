Require Import String.
Require Import Coqlib Maps Errors Integers.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.
Require Import Complements.
Require Import Ctypes Cop Clight.
Require Import Split.

Definition gdef := globdef fundef type.

Variant match_fundef : unit -> fundef -> fundef -> Prop :=
  | match_function_left: forall cp ty cc params vars vars' temps temps' body body',
      match_fundef tt
        (Internal {| fn_comp := cp; fn_return := ty; fn_callconv := cc;
                     fn_params := params; fn_vars := vars; fn_temps := temps;
                     fn_body := body |})
        (Internal {| fn_comp := cp; fn_return := ty; fn_callconv := cc;
                     fn_params := params; fn_vars := vars'; fn_temps := temps';
                     fn_body := body' |})
  | match_external_left: forall ef tys ty cc,
      match_fundef tt (External ef tys ty cc)
                        (External ef tys ty cc)
.

#[local] Instance has_comp_match_fundef : has_comp_match match_fundef.
intros ? x y H.
inv H; auto.
Qed.

Lemma match_fundef_refl u f : match_fundef u f f.
Proof.
destruct u. destruct f as [[]|]; constructor.
Qed.

Definition match_varinfo (ty1 ty2: type): Prop := ty1 = ty2.

Definition kept_genv (s: split) (ge: genv) (δ: side) (id: ident): bool :=
  match Genv.find_symbol ge id with
  | Some b =>
      match (Genv.genv_defs ge)!b with
      | None => false
      | Some gd => side_eq (s (comp_of gd)) δ
      end
  | None => false
  end.

Variant match_globdef : gdef -> gdef -> Prop :=
| match_gfun f1 f2 :
  match_fundef tt f1 f2 -> match_globdef (Gfun f1) (Gfun f2)
| match_gvar v1 v2 :
  match_globvar match_varinfo v1 v2 ->
  match_globdef (Gvar v1) (Gvar v2).

Definition match_opt_globdefs sd d1 d2 :=
  match sd with
  | Left => option_rel match_globdef d1 d2
  | Right => d1 = d2
  end.

Definition match_globdefs (s: split) (ge1 ge2: genv) :=
  forall id cp,
    (Genv.find_comp_of_ident ge1 id = Some cp \/
       Genv.find_comp_of_ident ge2 id = Some cp) ->
    (s cp = Right \/ Genv.public_symbol ge1 id = true \/
       Genv.public_symbol ge2 id = true) ->
    exists b1 b2,
      Genv.find_symbol ge1 id = Some b1 /\
      Genv.find_symbol ge2 id = Some b2 /\
      match_opt_globdefs (s cp) (Genv.find_def ge1 b1) (Genv.find_def ge2 b2).

Record match_prog (s: split) (p p': program) : Prop := {
  match_prog_main:
    p'.(prog_main) = p.(prog_main);
  match_prog_public:
    p'.(prog_public) = p.(prog_public);
  match_prog_types:
    p'.(prog_types) = p.(prog_types);
  match_prog_pol:
    p'.(prog_pol) = p.(prog_pol);
  match_prog_globdefs:
    match_globdefs s (globalenv p) (globalenv p');
  match_prog_unique1:
    list_norepet (prog_defs_names p);
  match_prog_unique2:
    list_norepet (prog_defs_names p')
}.

Section Equivalence.
  Variable s: split.
  Variable j: meminj.

  Definition same_domain (ge1: genv) (m1: mem) :=
    let H := Mem.has_side_block in
    forall b,
      match Genv.invert_symbol ge1 b with
      | Some id =>
          if Senv.public_symbol ge1 id then
            j b <> None
          else
            j b <> None <-> (s, m1) |= b ∈ Right
      | None =>
          j b <> None <-> (s, m1) |= b ∈ Right
      end.

  Lemma same_domain_free m b lo hi cp m' ge
    (FREE : Mem.free m b lo hi cp = Some m')
    (BLOCKS : same_domain ge m) :
    same_domain ge m'.
  Proof.
    intros b'. specialize (BLOCKS b').
    destruct Genv.invert_symbol as [id |] eqn:INVSYM.
    - destruct Senv.public_symbol eqn:PUBSYM;
        [assumption |].
      split.
      + intros j_b'. destruct BLOCKS as [BLOCKS _]. specialize (BLOCKS j_b').
        simpl in *. destruct (Mem.block_compartment m b') as [cp' |] eqn:COMP;
          [| contradiction].
        rewrite (Mem.free_can_access_block_inj_1 _ _ _ _ _ _ FREE _ (Some _) COMP).
        assumption.
      + intros RIGHT. destruct BLOCKS as [_ BLOCKS]. simpl in *.
        destruct (Mem.block_compartment m' b') as [cp' |] eqn:COMP';
          [| contradiction].
        rewrite (Mem.free_can_access_block_inj_2 _ _ _ _ _ _ FREE _ (Some _) COMP')
          in BLOCKS.
        exact (BLOCKS RIGHT).
    - split. (* Same proof as above *)
      + intros j_b'. destruct BLOCKS as [BLOCKS _]. specialize (BLOCKS j_b').
        simpl in *. destruct (Mem.block_compartment m b') as [cp' |] eqn:COMP;
          [| contradiction].
        rewrite (Mem.free_can_access_block_inj_1 _ _ _ _ _ _ FREE _ (Some _) COMP).
        assumption.
      + intros RIGHT. destruct BLOCKS as [_ BLOCKS]. simpl in *.
        destruct (Mem.block_compartment m' b') as [cp' |] eqn:COMP';
          [| contradiction].
        rewrite (Mem.free_can_access_block_inj_2 _ _ _ _ _ _ FREE _ (Some _) COMP')
          in BLOCKS.
        exact (BLOCKS RIGHT).
  Qed.

  Lemma same_domain_free_list m bs cp m' ge
    (FREE : Mem.free_list m bs cp = Some m')
    (BLOCKS : same_domain ge m) :
    same_domain ge m'.
  Proof.
    revert m cp m' ge FREE BLOCKS.
    induction bs as [| [[b lo] hi] ? IH]; intros.
    - now inv FREE.
    - simpl in FREE.
      destruct (Mem.free m b lo hi cp) as [m1 |] eqn:FREE1; [| discriminate].
      eapply same_domain_free in FREE1; [| exact BLOCKS].
      now eapply IH; eauto.
  Qed.

  Lemma same_domain_store chunk m b off v cp m' ge :
    Mem.store chunk m b off v cp = Some m' ->
    same_domain ge m ->
    same_domain ge m'.
  Proof.
    intros STORE DOM b'. specialize (DOM b'). simpl in *.
    now rewrite (Mem.store_block_compartment _ _ _ _ _ _ _ STORE).
  Qed.

  Lemma same_domain_storebytes m b ofs sz ocp m' ge :
    Mem.storebytes m b ofs sz ocp = Some m' ->
    same_domain ge m ->
    same_domain ge m'.
  Proof.
    intros STORE DOM b'. specialize (DOM b'). simpl in *.
    now rewrite (Mem.storebytes_block_compartment _ _ _ _ _ _ STORE).
  Qed.

  Definition same_blocks (ge: genv) (m: mem) :=
    forall b cp, Genv.find_comp_of_block ge b = Some cp ->
                 Mem.block_compartment m b = Some cp.

  Lemma same_blocks_store chunk m b ofs sz cp m' ge
    (STORE : Mem.store chunk m b ofs sz cp = Some m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    intros. intros b' cp' FIND. specialize (BLOCKS b' cp' FIND).
    erewrite Mem.store_block_compartment; eauto.
  Qed.

  Lemma same_blocks_storebytes m b ofs sz ocp m' ge
    (STORE : Mem.storebytes m b ofs sz ocp = Some m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    intros. intros b' cp FIND. specialize (BLOCKS b' cp FIND).
    erewrite Mem.storebytes_block_compartment; eauto.
  Qed.

  Lemma same_blocks_free m b lo hi cp m' ge
    (FREE : Mem.free m b lo hi cp = Some m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    intros b' cp' FIND. specialize (BLOCKS b' cp' FIND).
    exact (Mem.free_can_access_block_inj_1 _ _ _ _ _ _ FREE _ (Some _) BLOCKS).
  Qed.

  Lemma same_blocks_free_list m bs cp m' ge
    (FREE : Mem.free_list m bs cp = Some m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    revert m cp m' ge FREE BLOCKS.
    induction bs as [| [[b lo] hi] ? IH]; intros.
    - now inv FREE.
    - simpl in FREE.
      destruct (Mem.free m b lo hi cp) as [m1 |] eqn:FREE1; [| discriminate].
      eapply same_blocks_free in FREE1; [| exact BLOCKS].
      now eapply IH; eauto.
  Qed.

  Lemma same_blocks_assign_loc {ce cp ty m b ofs bf v m' ge}
    (ASSIGN : assign_loc ce cp ty m b ofs bf v m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    inv ASSIGN.
    - eapply same_blocks_store; eauto.
    - eapply same_blocks_storebytes; eauto.
    - inv H.
      eapply same_blocks_store; eauto.
  Qed.

  Record right_mem_injection (ge1 ge2: genv) (m1 m2: mem) : Prop :=
    { same_dom: same_domain ge1 m1;
      partial_mem_inject: Mem.inject j m1 m2;
      j_delta_zero: Mem.delta_zero j;
      same_symb: symbols_inject j ge1 ge2;
      jinjective: Mem.meminj_injective j;
      same_blks1: same_blocks ge1 m1;
      same_blks2: same_blocks ge2 m2;
    }.

Fixpoint remove_until_right (k: cont) :=
  match k with
  | Kstop => Kstop
  | Kseq _ k' | Kloop1 _ _ k'  | Kloop2 _ _ k' | Kswitch k' => remove_until_right k'
  | Kcall id f en le k' =>
      match s (comp_of f) with
      | Right => k
      | Left => remove_until_right k'
      end
  end.

Definition right_env_injection_some (e1 e2: env): Prop :=
  forall i b ty,
    e1 ! i = Some (b, ty) ->
    exists b', j b = Some (b', 0%Z) /\
          e2 ! i = Some (b', ty).

Definition right_env_injection_none (e1 e2: env): Prop :=
  forall i,
    e1 ! i = None ->
    e2 ! i = None.

Definition right_env_injection (e1 e2: env): Prop :=
  right_env_injection_some e1 e2 /\ right_env_injection_none e1 e2.

Definition right_tenv_injection (le1 le2: temp_env): Prop :=
  forall i v,
    le1 ! i = Some v ->
    exists v', Val.inject j v v' /\
            le2 ! i = Some v'.

Inductive right_cont_injection: cont -> cont -> Prop :=
| right_cont_injection_kstop: right_cont_injection Kstop Kstop
| right_cont_injection_kseq: forall s k1 k2,
    right_cont_injection k1 k2 ->
    right_cont_injection (Kseq s k1) (Kseq s k2) (* TODO: write other cases *)
| right_cont_injection_kloop1: forall s s' k1 k2,
    right_cont_injection k1 k2 ->
    right_cont_injection (Kloop1 s s' k1) (Kloop1 s s' k2)
| right_cont_injection_kloop2: forall s s' k1 k2,
    right_cont_injection k1 k2 ->
    right_cont_injection (Kloop2 s s' k1) (Kloop2 s s' k2)
| right_cont_injection_kswitch: forall k1 k2,
    right_cont_injection k1 k2 ->
    right_cont_injection (Kswitch k1) (Kswitch k2)
(* | right_cont_injection_kcall_left: forall id1 id2 f1 f2 en1 en2 le1 le2 k1 k2, *)
(*     s |= f1 ∈ Left -> *)
(*     s |= f2 ∈ Left -> *)
(*     right_cont_injection (remove_until_right k1) (remove_until_right k2) -> *)
(*     right_cont_injection (Kcall id1 f1 en1 le1 k1) (Kcall id2 f2 en2 le2 k2) *)
| right_cont_injection_kcall_left: forall id f en1 en2 le1 le2 k1 k2,
    s |= f ∈ Left ->
    right_cont_injection (remove_until_right k1) (remove_until_right k2) ->
    right_cont_injection (Kcall id f en1 le1 k1) (Kcall id f en2 le2 k2)
(* TODO: is it correct to add [right_cont_injection_kcall_right]? *)
(* | right_cont_injection_kcall_right: forall id1 id2 f1 f2 en1 en2 le1 le2 k1 k2, *)
(*     s |= f1 ∈ Right -> *)
(*     s |= f2 ∈ Right -> *)
(*     right_cont_injection k1 k2 -> *)
(*     right_cont_injection (Kcall id1 f1 en1 le1 k1) (Kcall id2 f2 en2 le2 k2) *)
| right_cont_injection_kcall_right: forall id f en1 en2 le1 le2 k1 k2,
    s |= f ∈ Right ->
    right_env_injection en1 en2 -> (* check for redundancies w.r.t. right_executing_injection *)
    right_tenv_injection le1 le2 -> (* check for redundancies w.r.t. right_executing_injection *)
    right_cont_injection k1 k2 ->
    right_cont_injection (Kcall id f en1 le1 k1) (Kcall id f en2 le2 k2)
.

 (* Analogous to: [partialize ctx scs1 = partialize ctx scs2] with
    [ctx] giving us the [Left] part (the program part). Partialize keeps the context part
    and discards the program part.

  [right_state_injection] should relate the context part of the two states, and ignore
  the program part of the two states.
  *)
Variant right_executing_injection (ge1 ge2: genv): state -> state -> Prop :=
| inject_states: forall f s k1 k2 e1 e2 le1 le2 m1 m2,
    (* we forget about program memories but require injection of context memories *)
    forall RMEMINJ : right_mem_injection ge1 ge2 m1 m2,

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    forall RCONTINJ : right_cont_injection k1 k2,

    (* the environments satisfy the injection *)
    forall RENVINJ : right_env_injection e1 e2,
    forall RTENVINJ : right_tenv_injection le1 le2,

    right_executing_injection ge1 ge2 (State f s k1 e1 le1 m1) (State f s k2 e2 le2 m2)
| inject_callstates: forall f vs vs' k1 k2 m1 m2,
    (* we forget about program memories but require injection of context memories *)
    forall RMEMINJ : right_mem_injection ge1 ge2 m1 m2,

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    forall RCONTINJ : right_cont_injection k1 k2,

    (* the parameters are related by the memory injection *)
    forall ARGINJ : Val.inject_list j vs vs',

    right_executing_injection ge1 ge2 (Callstate f vs k1 m1) (Callstate f vs' k2 m2)
| inject_returnstates: forall v v' k1 k2 m1 m2 ty cp,
    (* we forget about program memories but require injection of context memories *)
    forall RMEMINJ : right_mem_injection ge1 ge2 m1 m2,

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    forall RCONTINJ : right_cont_injection k1 k2,

    (* The return values are related by the injection *)
    forall RVALINJ : Val.inject j v v',

    right_executing_injection ge1 ge2 (Returnstate v k1 m1 ty cp) (Returnstate v' k2 m2 ty cp)
.

#[export] Instance state_has_side: has_side state :=
    { in_side s := fun st δ =>
                     match st with
                     | State f _ _ _ _ _ => s |= f ∈ δ
                     | Callstate fd _ _ _ => s |= fd ∈ δ (* Should this be the compartment that's on top of the stack instead? *)
                     | Returnstate _ _ _ _ cp => s |= cp ∈ δ
                     end
    }.

Definition memory_of (st: state): mem :=
  match st with
  | State _ _ _ _ _ m | Callstate _ _ _ m
  | Returnstate _ _ m _ _ => m
  end.

Definition cont_of (st: state): cont :=
  match st with
  | State _ _ k _ _ _ | Callstate _ _ k _
  | Returnstate _ k _ _ _ => k
  end.

Variant right_state_injection (ge1 ge2: genv): state -> state -> Prop :=
| LeftControl: forall st1 st2,
    (* program (left) has control *)
    s |= st1 ∈ Left ->
    s |= st2 ∈ Left ->

    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 (memory_of st1) (memory_of st2) ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection (remove_until_right (cont_of st1)) (remove_until_right (cont_of st2)) ->

    right_state_injection ge1 ge2 st1 st2
| RightControl: forall st1 st2,
    (* context (right) has control *)
    s |= st1 ∈ Right ->
    s |= st2 ∈ Right ->
    right_executing_injection ge1 ge2 st1 st2 ->
    right_state_injection ge1 ge2 st1 st2.


End Equivalence.

Section Simulation.
  Context (c p1 p2: Clight.program).
  Variable s: split.

  Context (W1 W2: Clight.program).
  Hypothesis c_p1: link p1 c = Some W1.
  Hypothesis c_p2: link p2 c = Some W2.

  Hypothesis match_W1_W2: match_prog s W1 W2.

  Hypothesis W1_ini: exists s, Smallstep.initial_state (semantics1 W1) s.
  Hypothesis W2_ini: exists s, Smallstep.initial_state (semantics1 W2) s.

  (* Context (ge1 ge2: genv). *)
  Notation ge1 := (globalenv W1).
  Notation ge2 := (globalenv W2).
(*
  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol ge2 s = Genv.find_symbol ge1 s.
  Proof (Genv.find_symbol_match match_W1_W2).
*)

(** New helpers *)

Lemma state_split_decidable:
  forall st, s |= st ∈ Left \/ s |= st ∈ Right.
Proof.
  intros [].
  - simpl. destruct (s (comp_of f)); auto.
  - simpl. destruct (s (comp_of fd)); auto.
  - simpl. destruct (s cp); auto.
Qed.

Lemma state_split_contra:
  forall st, s |= st ∈ Left -> s |= st ∈ Right -> False.
Proof.
  intros [].
  - simpl. destruct (s (comp_of f)); discriminate.
  - simpl. destruct (s (comp_of fd)); discriminate.
  - simpl. destruct (s cp); discriminate.
Qed.

Lemma step_E0_same_side: forall {p s1 s2 sd},
  Step (semantics1 p) s1 E0 s2 ->
  s |= s1 ∈ sd <-> s |= s2 ∈ sd.
Proof.
  intros p s1 s2 sd STEP.
  inv STEP; try easy.
  - inv EV. unfold Genv.type_of_call in H4.
    destruct (_ =? _)%positive eqn:EQ; [| contradiction].
    simpl. apply Pos.eqb_eq in EQ. rewrite EQ.
    easy.
  - inv EV. unfold Genv.type_of_call in H.
    destruct (_ =? _)%positive eqn:EQ; [| contradiction].
    simpl. apply Pos.eqb_eq in EQ. rewrite EQ. easy.
Qed.

Lemma star_E0_same_side: forall {p s1 s2 sd},
  Star (semantics1 p) s1 E0 s2 ->
  s |= s1 ∈ sd <-> s |= s2 ∈ sd.
Proof.
  intros p s1 s2 sd STAR.
  elim STAR using star_E0_ind; clear s1 s2 STAR.
  - easy.
  - intros s1 s2 s3 STEP12 IH.
    rewrite (step_E0_same_side STEP12).
    auto.
Qed.

Lemma right_state_injection_same_side_left: forall {j ge1 ge2 s1 s2 sd},
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s2 ∈ sd ->
  s |= s1 ∈ sd.
Proof.
  intros j ge1 ge2 s1 s2 sd RINJ SIDE.
  destruct sd; inv RINJ.
  - assumption.
  - exfalso. eapply state_split_contra; eauto.
  - exfalso. eapply state_split_contra; eauto.
  - assumption.
Qed.

Lemma right_cont_injection_call_cont: forall j k1 k2,
  right_cont_injection s j k1 k2 ->
  right_cont_injection s j (call_cont k1) (call_cont k2).
Proof.
  intros j k1 k2 RCONTINJ.
  induction RCONTINJ; auto.
  - constructor.
  - apply right_cont_injection_kcall_left; auto.
  - apply right_cont_injection_kcall_right; auto.
Qed.

Lemma right_cont_injection_inject_incr: forall j j' k1 k2,
  right_cont_injection s j k1 k2 ->
  inject_incr j j' ->
  right_cont_injection s j' k1 k2.
Proof.
  intros j j' k1 k2 RCONTINJ INCR.
  induction RCONTINJ;
    try now constructor.
  apply right_cont_injection_kcall_right;
    auto.
  - destruct H0 as [RENVSOME RENVNONE].
    split.
    + intros id' b1 ty GET1.
      specialize (RENVSOME id' b1 ty GET1) as (b2 & b1_b2 & GET2).
      eauto.
    + intros id' GET.
      specialize (RENVNONE id' GET).
      auto.
  - intros id' v GET1.
    specialize (H1 id' v GET1) as (v' & VALINJ & GET2).
    eauto.
Qed.


  (** More invariant helpers *)

  Lemma assign_loc_left_inject f m1 m2 m1' ce cp ty b ofs bf v
    (INJ: Mem.inject f m1 m2)
    (ASGN: assign_loc ce cp ty m1 b ofs bf v m1'):
    Mem.inject f m1' m2.
  Admitted.

  Lemma assign_loc_block_compartment {m m' b b' cp ce ty ofs bf v}
    (ASGN: assign_loc ce cp ty m b ofs bf v m'):
    Mem.block_compartment m b' = Mem.block_compartment m' b'.
  Proof.
    inv ASGN.
    - rewrite (Mem.store_block_compartment _ _ _ _ _ _ _ H0). reflexivity.
    - rewrite (Mem.storebytes_block_compartment _ _ _ _ _ _ H4). reflexivity.
    - inv H. rewrite (Mem.store_block_compartment _ _ _ _ _ _ _ H5). reflexivity.
  Qed.

  Remark assign_block_block_compartment_eq {m m' b b' cp cp' cp'' ce ty ofs bf v}
    (ASGN: assign_loc ce cp ty m b ofs bf v m')
    (COMP: Mem.block_compartment m b' = Some cp')
    (COMP': Mem.block_compartment m' b' = Some cp''):
    cp' = cp''.
  Proof.
    rewrite (assign_loc_block_compartment ASGN) in COMP.
    congruence.
  Qed.

  Lemma perm_assign_loc_1 {m m' b b' cp ce ty ofs ofs' bf v k p}
    (ASGN: assign_loc ce cp ty m b ofs bf v m')
    (PERM: Mem.perm m b' ofs' k p):
    Mem.perm m' b' ofs' k p.
  Proof.
    inv ASGN.
    - eapply Mem.perm_store_1; eauto.
    - eapply Mem.perm_storebytes_1; eauto.
    - inv H.
      eapply Mem.perm_store_1; eauto.
  Qed.

  Lemma perm_assign_loc_2 {m m' b b' cp ce ty ofs ofs' bf v k p}
    (ASGN: assign_loc ce cp ty m b ofs bf v m')
    (PERM: Mem.perm m' b' ofs' k p):
    Mem.perm m b' ofs' k p.
  Proof.
    inv ASGN.
    - eapply Mem.perm_store_2; eauto.
    - eapply Mem.perm_storebytes_2; eauto.
    - inv H.
      eapply Mem.perm_store_2; eauto.
  Qed.

  Lemma assign_loc_valid_block_1 {m m' b b' cp ce ty ofs bf v}
    (ASGN: assign_loc ce cp ty m b ofs bf v m')
    (VALID: Mem.valid_block m b'):
    Mem.valid_block m' b'.
  Proof.
    inv ASGN.
    - eapply Mem.store_valid_block_1; eauto.
    - eapply Mem.storebytes_valid_block_1; eauto.
    - inv H.
      eapply Mem.store_valid_block_1; eauto.
  Qed.

  Lemma assign_loc_valid_block_2 {m m' b b' cp ce ty ofs bf v}
    (ASGN: assign_loc ce cp ty m b ofs bf v m')
    (VALID: Mem.valid_block m' b'):
    Mem.valid_block m b'.
  Proof.
    inv ASGN.
    - eapply Mem.store_valid_block_2; eauto.
    - eapply Mem.storebytes_valid_block_2; eauto.
    - inv H.
      eapply Mem.store_valid_block_2; eauto.
  Qed.

  (* TODO: move, remove transparency hacks, add other direction *)
  Lemma assign_loc_perm {ce cp ty m b b' ofs ofs' k p bf v m'}
    (ASGN: assign_loc ce cp ty m b ofs bf v m')
    (PERM: Mem.perm m' b' ofs' k p):
    Mem.perm m b' ofs' k p.
  Proof.
    inv ASGN.
    - unfold Mem.storev in H0.
      Local Transparent Mem.store. unfold Mem.store in H0. Local Opaque Mem.store.
      destruct Mem.valid_access_dec eqn:VALID; [| discriminate].
      injection H0 as <-.
      auto.
    - Local Transparent Mem.storebytes. unfold Mem.storebytes in H4. Local Opaque Mem.storebytes.
      destruct Mem.range_perm_dec eqn:RANGE; [| discriminate].
      destruct Mem.can_access_block_dec eqn:ACC; [| discriminate].
      injection H4 as <-.
      auto.
    - inv H.
      unfold Mem.storev in H5.
      Local Transparent Mem.store. unfold Mem.store in H5. Local Opaque Mem.store.
      destruct Mem.valid_access_dec eqn:VALID; [| discriminate].
      injection H5 as <-.
      auto.
  Qed.

  (* TODO: move, remove transparency hacks, add other direction *)
  Lemma assign_loc_range_perm {ce cp ty m b b' ofs lo hi k p bf v m'}
    (ASGN: assign_loc ce cp ty m b ofs bf v m')
    (PERM: Mem.range_perm m' b' lo hi k p):
    Mem.range_perm m b' lo hi k p.
  Proof.
    inv ASGN.
    - unfold Mem.storev in H0.
      Local Transparent Mem.store. unfold Mem.store in H0. Local Opaque Mem.store.
      destruct Mem.valid_access_dec eqn:VALID; [| discriminate].
      injection H0 as <-.
      auto.
    - Local Transparent Mem.storebytes. unfold Mem.storebytes in H4. Local Opaque Mem.storebytes.
      destruct Mem.range_perm_dec eqn:RANGE; [| discriminate].
      destruct Mem.can_access_block_dec eqn:ACC; [| discriminate].
      injection H4 as <-.
      auto.
    - inv H.
      unfold Mem.storev in H5.
      Local Transparent Mem.store. unfold Mem.store in H5. Local Opaque Mem.store.
      destruct Mem.valid_access_dec eqn:VALID; [| discriminate].
      injection H5 as <-.
      auto.
  Qed.

  Lemma bind_parameters_valid_block_1 {ge cp e m1 params vl m2 b }
    (BIND: bind_parameters ge cp e m1 params vl m2)
    (VALID : Mem.valid_block m1 b):
    Mem.valid_block m2 b.
  Proof.
    revert b VALID.
    induction BIND; intros;
      [assumption |].
    apply IHBIND.
    eapply assign_loc_valid_block_1; eauto.
  Qed.

  Lemma bind_parameters_perm_1 {ge cp e m1 params vl m2 b ofs k p}
    (BIND: bind_parameters ge cp e m1 params vl m2)
    (PERM: Mem.perm m1 b ofs k p):
    Mem.perm m2 b ofs k p.
  Proof.
    revert b ofs k p PERM.
    induction BIND; intros;
      [assumption |].
    apply (perm_assign_loc_1 H0) in PERM.
    now auto.
  Qed.

  Lemma bind_parameters_perm_2 {ge cp e m1 params vl m2 b ofs k p}
    (BIND: bind_parameters ge cp e m1 params vl m2)
    (PERM: Mem.perm m2 b ofs k p):
    Mem.perm m1 b ofs k p.
  Proof.
    revert b ofs k p PERM.
    induction BIND; intros;
      [assumption |].
    apply (perm_assign_loc_2 H0).
    now auto.
  Qed.

  Lemma bind_parameters_range_perm_1 {ge cp e m1 params vl m2 b hi lo k p}
    (BIND: bind_parameters ge cp e m1 params vl m2)
    (PERM: Mem.range_perm m1 b hi lo k p):
    Mem.range_perm m2 b hi lo k p.
  Proof.
    intros delta RANGE.
    eapply bind_parameters_perm_1; eauto.
  Qed.

  Lemma bind_parameters_range_perm_2 {ge cp e m1 params vl m2 b hi lo k p}
    (BIND: bind_parameters ge cp e m1 params vl m2)
    (PERM: Mem.range_perm m2 b hi lo k p):
    Mem.range_perm m1 b hi lo k p.
  Proof.
    intros delta RANGE.
    eapply bind_parameters_perm_2; eauto.
  Qed.

  Lemma bind_parameters_can_access_block_1 {ge cp e m1 params vl m2 b cp'}
    (BIND: bind_parameters ge cp e m1 params vl m2)
    (ACC : Mem.can_access_block m1 b cp'):
    Mem.can_access_block m2 b cp'.
  Proof.
    destruct cp' as [cp' |];
      [| reflexivity].
    revert b cp' ACC.
    induction BIND; intros;
      [assumption |].
    change (Mem.can_access_block _ _ _)
      with (Mem.block_compartment m b0 = Some cp') in ACC.
    rewrite (assign_loc_block_compartment H0) in ACC.
    eauto.
  Qed.

  Lemma bind_parameters_can_access_block_2 {ge cp e m1 params vl m2 b cp'}
    (BIND: bind_parameters ge cp e m1 params vl m2)
    (ACC : Mem.can_access_block m2 b cp'):
    Mem.can_access_block m1 b cp'.
  Proof.
    destruct cp' as [cp' |];
      [| reflexivity].
    revert b cp' ACC.
    induction BIND; intros;
      [assumption |].
    apply IHBIND in ACC.
    change (Mem.can_access_block _ _ _)
      with (Mem.block_compartment m1 b0 = Some cp') in ACC.
    rewrite <- (assign_loc_block_compartment H0) in ACC.
    auto.
  Qed.

  Lemma alloc_variables_valid_block_1 {ge cp e1 m1 vars e2 m2 b}
    (ALLOC: alloc_variables ge cp e1 m1 vars e2 m2)
    (VALID : Mem.valid_block m1 b):
    Mem.valid_block m2 b.
  Proof.
    revert b VALID.
    induction ALLOC; intros;
      [assumption |].
    apply IHALLOC.
    eapply Mem.valid_block_alloc; eauto.
  Qed.

  Lemma alloc_variables_perm_1 {ge cp e1 m1 vars e2 m2 b ofs k p}
    (ALLOC: alloc_variables ge cp e1 m1 vars e2 m2)
    (PERM : Mem.perm m1 b ofs k p):
    Mem.perm m2 b ofs k p.
  Proof.
    revert b ofs k p PERM.
    induction ALLOC; intros;
      [assumption |].
    apply (Mem.perm_alloc_1 _ _ _ _ _ _ H) in PERM.
    now auto.
  Qed.

  Lemma alloc_variables_perm_2 {ge cp e1 m1 vars e2 m2 b ofs k p}
    (ALLOC: alloc_variables ge cp e1 m1 vars e2 m2)
    (VALID: Mem.valid_block m1 b)
    (PERM : Mem.perm m2 b ofs k p):
    Mem.perm m1 b ofs k p.
  Proof.
    revert b ofs k p VALID PERM.
    induction ALLOC; intros;
      [assumption |].
    destruct (Pos.eq_dec b b1) as [<- | NEQ].
    - apply Mem.fresh_block_alloc in H. contradiction.
    - assert (VALID': Mem.valid_block m1 b)
        by (eapply Mem.valid_block_alloc; eauto).
      specialize (IHALLOC _ _ _ _ VALID' PERM).
      eapply Mem.perm_alloc_4; eauto.
  Qed.

  Lemma alloc_variables_range_perm_1 {ge cp e1 m1 vars e2 m2 b hi lo k p}
    (ALLOC: alloc_variables ge cp e1 m1 vars e2 m2)
    (PERM : Mem.range_perm m1 b hi lo k p):
    Mem.range_perm m2 b hi lo k p.
  Proof.
    intros delta RANGE.
    eapply alloc_variables_perm_1; eauto.
  Qed.

  Lemma alloc_variables_range_perm_2 {ge cp e1 m1 vars e2 m2 b hi lo k p}
    (ALLOC: alloc_variables ge cp e1 m1 vars e2 m2)
    (VALID: Mem.valid_block m1 b)
    (PERM : Mem.range_perm m2 b hi lo k p):
    Mem.range_perm m1 b hi lo k p.
  Proof.
    intros delta RANGE.
    eapply alloc_variables_perm_2; eauto.
  Qed.

  Lemma alloc_variables_can_access_block_1 {ge cp e1 m1 vars e2 m2 b cp'}
    (ALLOC: alloc_variables ge cp e1 m1 vars e2 m2)
    (ACC : Mem.can_access_block m1 b cp'):
    Mem.can_access_block m2 b cp'.
  Proof.
    revert b cp' ACC.
    induction ALLOC; intros;
      [assumption |].
    apply IHALLOC.
    eapply Mem.alloc_can_access_block_other_inj_1; eauto.
  Qed.

  Lemma alloc_variables_can_access_block_2 {ge cp e1 m1 vars e2 m2 b cp'}
    (ALLOC: alloc_variables ge cp e1 m1 vars e2 m2)
    (VALID: Mem.valid_block m1 b)
    (ACC : Mem.can_access_block m2 b cp'):
    Mem.can_access_block m1 b cp'.
  Proof.
    revert b cp' VALID ACC.
    induction ALLOC; intros;
      [assumption |].
    destruct (Pos.eq_dec b b1) as [<- | NEQ].
    - apply Mem.fresh_block_alloc in H. contradiction.
    - assert (VALID': Mem.valid_block m1 b)
        by (eapply Mem.valid_block_alloc; eauto).
      specialize (IHALLOC _ _ VALID' ACC).
      eapply Mem.alloc_can_access_block_other_inj_2; eauto.
  Qed.

  (* nicer variants of this? *)
  Lemma alloc_variables_can_access_block_fresh {ge cp e1 m1 vars e2 m2 b cp'}
    (ALLOC: alloc_variables ge cp e1 m1 vars e2 m2)
    (VALID: ~ Mem.valid_block m1 b)
    (ACC : Mem.can_access_block m2 b (Some cp')):
    cp = cp'.
  Proof.
    revert b cp' VALID ACC.
    induction ALLOC; intros.
    - apply Mem.can_access_block_valid_block in ACC.
      contradiction.
    - destruct (Pos.eq_dec b b1) as [<- | NEQ].
      (* Search Mem.alloc compartment. *)
      + apply Mem.owned_new_block in H.
        apply (alloc_variables_can_access_block_1 ALLOC) in H.
        congruence.
      + eapply IHALLOC; [| eassumption].
        intros CONTRA. apply VALID; clear VALID.
        destruct (Mem.valid_block_alloc_inv _ _ _ _ _ _ H _ CONTRA) as [EQ | VALID];
          [contradiction |].
        destruct (plt b (Mem.nextblock m)) as [LT | GE];
          [exact LT | contradiction].
  Qed.

  Lemma same_blocks_function_entry1 ge f vargs m e le m'
    (ENTRY : function_entry1 ge f vargs m e le m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    intros b cp FIND. specialize (BLOCKS b cp FIND).
    inv ENTRY.
    change (Mem.block_compartment _ _ = _)
      with (Mem.can_access_block m' b (Some cp)).
    eapply bind_parameters_can_access_block_1; eauto.
    eapply alloc_variables_can_access_block_1; eauto.
  Qed.

  Lemma same_blocks_step1 s1 s1'
    (BLKS : same_blocks ge1 (memory_of s1))
    (STEP : step1 ge1 s1 E0 s1'):
    same_blocks ge1 (memory_of s1').
  Proof.
    inv STEP; auto.
    - eapply same_blocks_assign_loc; eauto.
    - intros b cp FIND.
      specialize (BLKS b cp FIND).
      simpl in *.
      change (Mem.block_compartment m b = Some cp)
        with (Mem.can_access_block m b (Some cp)) in BLKS.
      exploit external_call_can_access_block; eauto.
    - eapply same_blocks_free_list; eauto.
    - eapply same_blocks_free_list; eauto.
    - eapply same_blocks_free_list; eauto.
    - eapply same_blocks_function_entry1; eauto.
    - intros b cp FIND.
      specialize (BLKS b cp FIND).
      simpl in *.
      change (Mem.block_compartment m b = Some cp)
        with (Mem.can_access_block m b (Some cp)) in BLKS.
      exploit external_call_can_access_block; eauto.
  Qed.

  (** *)

  Lemma public_symbol_preserved:
    forall id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id.
  Proof.
    intros id.
    assert (in_dec ident_eq id (Genv.genv_public ge2) =
              in_dec ident_eq id (Genv.genv_public ge1) :> bool)
      as public_eq.
    { simpl. rewrite !Genv.globalenv_public. simpl.
      now rewrite (match_prog_public _ _ _ match_W1_W2). }
    destruct (Genv.public_symbol ge1 id) eqn:public1.
    - destruct (Genv.public_symbol_exists _ _ public1) as [b1 ge1_id_b1].
      assert (exists cp, Genv.find_comp_of_ident ge1 id = Some cp)
        as [cp ge1_id_cp].
      { apply Genv.find_symbol_find_comp.
        unfold ge1, fundef in *. simpl in *. congruence. }
      assert (exists b2, Genv.find_symbol ge2 id = Some b2)
        as [b2 ge2_id_b2].
      { exploit match_prog_globdefs; eauto.
        intros (? & b2 & _ & H & _). eauto. }
      unfold Genv.public_symbol in *.
      rewrite ge1_id_b1 in public1.
      rewrite ge2_id_b2. congruence.
    - unfold Genv.public_symbol in public1.
      destruct (Genv.find_symbol ge1 id) as [b1|] eqn:ge1_id.
      + assert (exists cp, Genv.find_comp_of_ident ge1 id = Some cp)
          as [cp ge1_id_cp].
        { apply Genv.find_symbol_find_comp.
          unfold ge1, fundef in *. simpl in *. congruence. }
        unfold Genv.public_symbol.
        destruct (Genv.find_symbol ge2 id) as [b2|] eqn:ge2_id; trivial.
        congruence.
      + destruct (Genv.public_symbol ge2 id) eqn:public2; trivial.
        destruct (Genv.public_symbol_exists _ _ public2) as [b2 ge2_id_b2].
        assert (exists cp, Genv.find_comp_of_ident ge2 id = Some cp)
          as [cp ge2_id_cp].
        { apply Genv.find_symbol_find_comp.
          unfold ge1, fundef in *. simpl in *. congruence. }
        exploit match_prog_globdefs; eauto.
        intros (? & _ & ? & _). congruence.
  Qed.

  Lemma allowed_addrof_translated:
    forall cp id,
      s cp = Right ->
      Genv.allowed_addrof ge1 cp id ->
      Genv.allowed_addrof ge2 cp id.
  Proof.
    intros cp id RIGHT [H|H].
    - left.
      exploit match_prog_globdefs; eauto. rewrite RIGHT. simpl.
      intros (b1 & b2 & ge1_id & ge2_id & MATCH).
      unfold Genv.find_comp_of_ident in *.
      simpl in H. rewrite ge1_id in H.
      rewrite ge2_id.
      unfold Genv.find_comp_of_block in *. now rewrite <- MATCH.
    - right. now rewrite public_symbol_preserved.
  Qed.

  Lemma genv_cenv_preserved : ge2 = ge1 :> composite_env.
  Proof.
    simpl.
    pose proof (prog_comp_env_eq W1) as H1.
    pose proof (prog_comp_env_eq W2) as H2.
    rewrite (match_prog_types _ _ _ match_W1_W2) in H2.
    congruence.
  Qed.

  Lemma sizeof_preserved : forall ty, sizeof ge2 ty = sizeof ge1 ty.
  Proof. intros ty. now rewrite genv_cenv_preserved. Qed.

Lemma right_mem_injection_free: forall {j ge1 ge2 m1 m2 b1 b2 lo hi cp m1'},
  right_mem_injection s j ge1 ge2 m1 m2 ->
  Mem.free m1 b1 lo hi cp = Some m1' ->
  j b1 = Some (b2, 0) ->
  exists m2',
    Mem.free m2 b2 lo hi cp = Some m2' /\
    right_mem_injection s j ge1 ge2 m1' m2'.
Proof.
  intros j ge1 ge2 m1 m2 b1 b2 lo hi cp m1' MEMINJ FREE1 j_b1.
  destruct MEMINJ
    as [DOM MI D0 SYMB MI_INJ BLKS1 BLKS2].
  pose proof (Mem.free_range_perm _ _ _ _ _ _ FREE1) as RANGE1.
  pose proof (Mem.free_can_access_block_1 _ _ _ _ _ _ FREE1) as ACCESS1.
  assert (Mem.range_perm m2 b2 lo hi Cur Freeable) as RANGE2.
  { intros x BOUNDS.
    specialize (RANGE1 x BOUNDS).
    exploit Mem.mi_inj; eauto. intros ?.
    exploit Mem.mi_perm; eauto.
    now rewrite Z.add_0_r. }
  assert (Mem.can_access_block m2 b2 (Some cp)) as ACCESS2.
  { exploit Mem.mi_inj; eauto. intros ?.
    exploit Mem.mi_own; eauto. }
  destruct (Mem.range_perm_free _ _ _ _ _ RANGE2 ACCESS2)
    as (m2' & FREE2).
  exists m2'; split; trivial; split; trivial.
  - eauto using same_domain_free.
  - exploit Mem.free_parallel_inject; eauto.
    rewrite !Z.add_0_r. intros (? & ? & ?). congruence.
  - eapply same_blocks_free; eauto.
  - eapply same_blocks_free; eauto.
Qed.

Lemma right_mem_injection_free_list: forall {j m1 m2 e1 e2 cp m1'},
  right_mem_injection s j ge1 ge2 m1 m2 ->
  right_env_injection j e1 e2 ->
  Mem.free_list m1 (blocks_of_env ge1 e1) cp = Some m1' ->
  s cp = Right ->
  exists m2',
    Mem.free_list m2 (blocks_of_env ge2 e2) cp = Some m2' /\
    right_mem_injection s j ge1 ge2 m1' m2'.
Proof.
  intros j m1 m2 e1 e2 cp m1' MEMINJ ENVINJ FREE s_cp.
  (* TODO: Separate lemma? *)
  assert (forall id,
      option_rel (fun '(b1, ty1) '(b2, ty2) =>
          j b1 = Some (b2, 0) /\ ty1 = ty2)
        e1!id e2!id) as ENVINJ'.
  { destruct ENVINJ as [EI1 EI2].
    intros id.
    destruct e1!id as [[b1 ty]|] eqn:e1_id.
    - destruct (EI1 _ _ _ e1_id) as (b2 & j_b1 & e2_id).
      rewrite e2_id; constructor; eauto.
    - rewrite (EI2 _ e1_id); constructor. }
  unfold blocks_of_env in *.
  pose proof (PTree.elements_canonical_order' _ _ ENVINJ') as ENVINJ''.
  clear ENVINJ ENVINJ'. revert ENVINJ'' m1 m2 MEMINJ FREE.
  generalize (PTree.elements e1) (PTree.elements e2). clear e1 e2.
  intros e1 e2 EI.
  induction EI as [|(id & b1 & ty) e1 (id' & b2 & ty') e2 (? & j_b1 & ?) _ IH].
  { intros. simpl in *; exists m2; split; congruence. }
  intros m1 m2 MEMINJ FREELIST1. simpl in *. subst id' ty'.
  destruct (Mem.free m1 b1) as [m1''|] eqn:FREE1; try congruence.
  destruct (right_mem_injection_free MEMINJ FREE1 j_b1)
    as (m2'' & FREE2 & MEMINJ'').
  destruct (IH _ _ MEMINJ'' FREELIST1)
    as (m2' & FREELIST2 & MEMINJ').
  pose proof (sizeof_preserved ty) as E. simpl in E. rewrite E.
  exists m2'. now rewrite FREE2; split.
Qed.

  (* AAA: [2023-08-08: This next part is not true anymore because left symbols
     can be covered by a memory injection] Right now, this statement is forcing
     every global identifier id that occurs in an expression to refer to a
     function or variable that is defined on the right.  This is because, when
     you evaluate an lvalue, you get something that is defined in the memory
     injection j.  Here are possible solutions:

     1. Modify the second implication so that, if we evaluate an lvalue that is
     not defined in the memory injection j (and, therefore, is on the Left),
     then this lvalue must be either a global function or variable.  The problem
     with this is that we would probably have to extend this to an invariant on
     memories: every pointer to a non-global-function-or-variable that is stored
     in Right memory must point to the Right. And this sounds complicated to
     reason about.

     2. Change the second implication so that we do not care if we get a
     non-global-function-or-variable pointer that is on the left.

     [2023-08-23] We realized that, if we allow programs to take the address of
     arbitrary variables, we run into issues when a program running on the right
     attempts to take the address of a private variable on the left. The issue
     is that, according to our current matching definitions, this private
     variable must not have a corresponding address in the memory injection
     relating the two executions. Therefore, it would not be possible to produce
     a matching evaluation on the other execution.

     One solution would be to dynamically disallow taking the address of a
     non-public variable that lives in a different compartment. But at lower
     levels it might not be possible to impose this check, because there
     probably isn't a difference between variables and their addresses (NB we
     should double-check this!). But this might not be an issue, because we are
     always free to omit checks at the target level.

     Moreover, it sounds like this check might be necessary for blame to
     hold. Consider a context C that is linked against two programs p1 and p2.
     If C tries to access a private variable of p1 that is not defined by p2,
     and the check is not performed, the execution with p1 might succeed,
     whereas the one with p2 will definitely fail.

   *)
  Lemma eval_expr_lvalue_injection:
    forall j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall cp_right: s cp = Right,
    (forall a v,
      eval_expr ge1 e1 cp le1 m1 a v ->
      exists v', Val.inject j v v' /\
                   eval_expr ge2 e2 cp le2 m2 a v')
    /\
    (forall a loc ofs bf,
      eval_lvalue ge1 e1 cp le1 m1 a loc ofs bf ->
      exists loc' ofs',
        (j loc = Some (loc', ofs')) /\
        eval_lvalue ge2 e2 cp le2 m2 a loc' (Ptrofs.add ofs (Ptrofs.repr ofs')) bf).
  Proof.
    intros.
    destruct inj as [inj_dom inj_inject j_delta_zero same_symb jinj SAMEBLKS].
    apply eval_expr_lvalue_ind; intros;
    try now match goal with
    | |- exists _, Val.inject _ (Vint _) _ /\ _ => eexists; split; [eapply Val.inject_int | econstructor; eauto]
    | |- exists _, Val.inject _ (Vfloat _) _ /\ _ => eexists; split; [eapply Val.inject_float | econstructor; eauto]
    | |- exists _, Val.inject _ (Vsingle _) _ /\ _ => eexists; split; [eapply Val.inject_single | econstructor; eauto]
    | |- exists _, Val.inject _ (Vlong _) _ /\ _ => eexists; split; [eapply Val.inject_long | econstructor; eauto]
    end.
    - (* eval_Etempvar *)
      exploit lenv_inj; eauto. intros [loc' [? ?]].
      eexists; split; eauto.
      constructor; auto.
    - (* eval_Eaddrof *)
      destruct H0 as [loc' [ofs' [? ?]]].
      eexists; split; eauto.
      econstructor; eauto.
    - (* eval_Eunop *)
      destruct H0 as [v' [? ?]].
      exploit sem_unary_operation_inject; eauto.
      intros [? [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
    - (* eval_Ebinop *)
      destruct H0 as [v1' [? ?]].
      destruct H2 as [v2' [? ?]].
      exploit sem_binary_operation_inject; eauto.
      rewrite <- genv_cenv_preserved.
      intros [? [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
    - (* eval_Ecast *)
      destruct H0 as [v' [? ?]].
      exploit sem_cast_inject; eauto.
      intros [v1' [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
    - (* eval_Esizeof *)
      rewrite <- genv_cenv_preserved.
      eexists; split; eauto.
      econstructor; eauto.
    - (* eval_Ealignof *)
      rewrite <- genv_cenv_preserved.
      eexists; split; eauto.
      econstructor; eauto.
    - (* eval_Elvalue *)
      destruct H0 as [loc' [ofs' [? ?]]].
      (* This assert heavily relies on the assumption that the injection always gives a delta = 0. *)
      assert (G: exists v', Val.inject j v v' /\
                         deref_loc cp (typeof a) m2 loc' (Ptrofs.add ofs (Ptrofs.repr ofs')) bf v').
      { inv H1.
        - simpl in *.
          exploit Mem.load_inject; eauto.
          intros [v' [? ?]].
          exploit j_delta_zero; eauto; intros; subst. rewrite Z.add_0_r in H1. rewrite Ptrofs.add_zero.
          eexists; split; eauto. econstructor; simpl; eauto.
        - exists (Vptr loc' (Ptrofs.add ofs (Ptrofs.repr ofs'))). split; eauto.
          eapply deref_loc_reference; eauto.
        - exists (Vptr loc' (Ptrofs.add ofs (Ptrofs.repr ofs'))). split; eauto.
          eapply deref_loc_copy; eauto.
        - inv H3.
          exploit Mem.load_inject; eauto.
          intros [v' [? ?]].
          exploit j_delta_zero; eauto; intros; subst. rewrite Z.add_0_r in H3; rewrite Ptrofs.add_zero.
          eexists; split; eauto.
          eapply deref_loc_bitfield. inv H7.
          econstructor; eauto. }
      destruct G as [v' [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
    - (* eval_Evar_local *)
      destruct env_inj as [env_inj _].
      exploit env_inj; eauto.
      intros [b' [? ?]].
      eexists; eexists; split; eauto.
      econstructor; eauto.
    - (* eval_Evar_global *)
      destruct env_inj as [_ env_inj].
      rename l into b.
      rename H into e1_id.
      rename H0 into W1_id.
      rename H1 into ALLOWED.
      exploit env_inj; eauto.
      intros e2_id.
      exploit Genv.find_invert_symbol; eauto.
      intros W1_b.
      pose proof (idP := inj_dom b).
      rewrite W1_b in idP.
      destruct (Senv.public_symbol _ id) eqn: public_id.
      + (* public symbol *)
        assert (exists b', j b = Some (b', 0) /\
                             Senv.find_symbol (globalenv W2) id = Some b')
          as (b' & j_b & W2_id).
        { destruct same_symb as (_ & _ & H & _). now apply H. }
        exists b', 0; split; trivial.
        rewrite Ptrofs.add_zero_l.
        eapply eval_Evar_global; eauto.
        now apply allowed_addrof_translated.
      + (* private symbol *)
        assert (id_cp : Genv.find_comp_of_ident ge1 id = Some cp).
        { destruct ALLOWED; trivial.
          unfold Genv.to_senv in public_id. simpl in public_id.
          unfold globalenv in H. simpl in H.
          congruence. }
        assert (b_right : (s, m1) |= b ∈ Right).
        { unfold Mem.has_side_block. simpl.
          unfold Genv.find_comp_of_ident in id_cp.
          rewrite W1_id in id_cp.
          apply SAMEBLKS in id_cp. now rewrite id_cp. }
        apply idP in b_right.
        destruct (j b) as [[loc' ofs']|] eqn:j_b; try easy.
        clear b_right idP.
        exists loc', ofs'. split; trivial.
        assert (ofs' = 0 /\ Genv.find_symbol (globalenv W2) id = Some loc')
          as [? W2_id].
        { destruct same_symb as (_ & same_symb & _).
          eapply same_symb; eauto. }
        subst ofs'.
        rewrite Ptrofs.add_zero_l.
        apply eval_Evar_global; eauto.
        now apply allowed_addrof_translated.
    - (* eval_Ederef *)
      destruct H0 as [v' [? ?]].
      inv H0.
      eexists; eexists; split; eauto.
      econstructor; eauto.
    - (* eval_Efield_struct *)
      destruct H0 as [v' [? ?]].
      inv H0.
      eexists; eexists; split; eauto.
      rewrite Ptrofs.add_assoc, (Ptrofs.add_commut (Ptrofs.repr delta)), <- Ptrofs.add_assoc.
      eapply eval_Efield_struct; try rewrite genv_cenv_preserved; eauto.
    - (* eval_Efield_union *)
      destruct H0 as [v' [? ?]].
      inv H0.
      eexists; eexists; split; eauto.
      rewrite Ptrofs.add_assoc, (Ptrofs.add_commut (Ptrofs.repr delta)), <- Ptrofs.add_assoc.
      eapply eval_Efield_union; try rewrite genv_cenv_preserved; eauto.
  Qed.

  Lemma eval_expr_injection:
    forall j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall s_right: s cp = Right,
    forall a v,
      eval_expr ge1 e1 cp le1 m1 a v ->
      exists v', Val.inject j v v' /\
                     eval_expr ge2 e2 cp le2 m2 a v'.
    Proof.
      intros.
      exploit eval_expr_lvalue_injection; eauto.
      intros [? _]. eauto.
    Qed.

  Lemma eval_exprlist_injection:
    forall j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall s_right: s cp = Right,
    forall al tys vs,
      eval_exprlist ge1 e1 cp le1 m1 al tys vs ->
      exists vs', Val.inject_list j vs vs' /\
              eval_exprlist ge2 e2 cp le2 m2 al tys vs'.
    Proof.
      intros.
      induction H.
      - exists nil; split; eauto. constructor.
      - destruct IHeval_exprlist as [vs' [? ?]].
        exploit eval_expr_injection; eauto.
        intros [v' [? ?]].
        destruct inj.
        exploit sem_cast_inject; eauto.
        intros [tv [? ?]].
        exists (tv :: vs'). split. constructor; eauto.
        econstructor; eauto.
    Qed.

  Lemma eval_lvalue_injection:
    forall j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall s_right: s cp = Right,
    forall a loc ofs bf,
      eval_lvalue ge1 e1 cp le1 m1 a loc ofs bf ->
      exists loc' ofs', j loc = Some (loc', ofs') /\
                     eval_lvalue ge2 e2 cp le2 m2 a loc' (Ptrofs.add ofs (Ptrofs.repr ofs')) bf.
  Proof.
    intros.
    exploit eval_expr_lvalue_injection; eauto.
    intros [_ ?]. eauto.
  Qed.

  Ltac destruct_mem_inj :=
    match goal with
    | H: right_mem_injection _ _ _ _ _ _ |- _ =>
        destruct H as [same_dom mem_inject delta_zero same_symb injective SAMEBLKS]
    end.

  Lemma find_funct_preserved j f v v' :
    s (comp_of f) = Right ->
    Val.inject j v v' ->
    symbols_inject j ge1 ge2 ->
    Genv.find_funct ge1 v = Some f ->
    Genv.find_funct ge2 v' = Some f.
  Proof.
    unfold Genv.find_funct. intros s_cp v_inj symbs_inj.
    case v_inj; try congruence. clear v_inj.
    intros b ofs b' _ delta j_b ->.
    destruct Ptrofs.eq_dec as [?|_]; try congruence. subst ofs.
    intros ge1_b.
    apply Genv.find_funct_ptr_iff in ge1_b.
    assert (exists id, Genv.find_symbol ge1 id = Some b) as [id ge1_id].
    { apply (Genv.find_def_find_symbol_inversion _ _ ge1_b).
      apply (match_prog_unique1 _ _ _ match_W1_W2). }
    assert (delta = 0 /\ Genv.find_symbol ge2 id = Some b') as [? ge2_id].
    { destruct symbs_inj as (_ & inj & _); eapply inj; eauto. }
    subst delta.
    rewrite Ptrofs.add_zero_l. unfold Ptrofs.zero.
    destruct Ptrofs.eq_dec as [_|?]; try congruence.
    assert (Genv.find_comp_of_ident ge1 id = Some (comp_of f)) as ge1_id_comp.
    { unfold Genv.find_comp_of_ident. rewrite ge1_id.
      unfold Genv.find_comp_of_block. now rewrite ge1_b. }
    exploit match_prog_globdefs; eauto.
    intros (b1 & b2 & ge1_id_alt & ge2_id_alt & MATCH).
    assert (b1 = b) by congruence. subst b1.
    assert (b2 = b') by congruence. subst b2.
    rewrite ge1_b, s_cp in MATCH. simpl in MATCH.
    unfold Genv.find_funct_ptr, ge2. simpl.
    rewrite <- MATCH. split; trivial.
  Qed.

  Lemma find_comp_of_block_preserved j m1 m2 b1 b2 delta id cp :
    right_mem_injection s j ge1 ge2 m1 m2 ->
    j b1 = Some (b2, delta) ->
    Genv.find_comp_of_block ge1 b1 = Some cp ->
    Genv.find_symbol ge1 id = Some b1 ->
    Genv.find_symbol ge2 id = Some b2 ->
    Genv.find_comp_of_block ge2 b2 = Some cp.
  Proof.
    intros inj j_b1 ge1_b1 ge1_id ge2_id.
    unfold Genv.find_comp_of_block in *.
    exploit Genv.find_symbol_find_def_inversion.
    { simpl in ge2_id. eauto. }
    intros (d2 & ge2_b2). unfold ge2. simpl. unfold fundef in *. rewrite ge2_b2.
    exploit partial_mem_inject; eauto. intros INJ.
    exploit Mem.mi_inj; eauto. intros INJ'.
    assert (access : Mem.can_access_block m1 b1 (Some cp)).
    { simpl. exploit same_blks1; eauto. }
    assert (ge2_b2' : Genv.find_comp_of_block ge2 b2 = Some (comp_of d2)).
    { unfold Genv.find_comp_of_block, ge2. simpl. unfold fundef in *.
      now rewrite ge2_b2. }
    exploit same_blks2; eauto. intros m2_b2.
    exploit Mem.mi_own; eauto. simpl. intros ?.
    congruence.
  Qed.

  Lemma allowed_call_preserved : forall j cp m1 m2 vf1 vf2,
      right_mem_injection s j ge1 ge2 m1 m2 ->
      Val.inject j vf1 vf2 ->
      Genv.allowed_call ge1 cp vf1 ->
      Genv.allowed_call ge2 cp vf2.
  Proof.
    intros j cp m1 m2 vf1 vf2 inj vf12 allowed.
    destruct allowed as [same_comp|cross]; [left|right].
    - unfold Genv.find_comp in *.
      revert same_comp. case vf12; try easy.
      intros b1 _ b2 ofs2 delta j_b1 _ ge1_b1.
      symmetry in ge1_b1. symmetry.
      assert (exists id, Genv.find_symbol ge1 id = Some b1) as (id & ge1_id).
      { unfold Genv.find_comp_of_block in ge1_b1.
        destruct (Genv.find_def ge1 b1) as [d1|] eqn:ge1_b1'; try easy.
        eapply Genv.find_def_find_symbol_inversion; eauto.
        exploit match_prog_unique1; eauto. }
      assert (Genv.find_symbol ge2 id = Some b2).
      { exploit same_symb; eauto.
        intros (H1 & H2 & H3 & H4).
        exploit H2; eauto. intros (-> & ge2_id). now simpl in ge2_id. }
      now exploit find_comp_of_block_preserved; eauto.
    - unfold Genv.allowed_cross_call in *.
      revert cross. case vf12; try easy.
      simpl. intros b1 _ b2 ofs2 delta j_b1 _.
      intros (id & cp' & ge1_b1 & ge1_b1' & imp & exp).
      exists id, cp'.
      exploit same_symb; eauto. intros (H1 & H2 & H3 & H4). simpl in *.
      exploit Genv.invert_find_symbol; eauto. intros ge1_id.
      exploit H2; eauto. intros (-> & ge2_id).
      split; [now apply Genv.find_invert_symbol|].
      split.
      { exploit find_comp_of_block_preserved; eauto. }
      rewrite Genv.globalenv_policy in *. simpl in *.
      now rewrite (match_prog_pol _ _ _ match_W1_W2); split.
  Qed.

  Lemma inject_list_not_ptr: forall j vl1 vl2,
    Val.inject_list j vl1 vl2 ->
    Forall not_ptr vl1 ->
    Forall not_ptr vl2.
  Proof.
    intros j vl1 vl2 INJ.
    induction INJ.
    - now constructor.
    - intros PTR.
      inv PTR.
      specialize (IHINJ H3).
      constructor; [| assumption].
      inv H; inv H2; constructor.
  Qed.

  (* Symbols are present in the program memory from the very beginning
     (cf. [Genv.init_mem] and the correspondence should also be
     reflected in and preserved by the memory injection. *)
  Lemma right_mem_injection_find_symbol: forall j m1 m2 id b1 b2 delta,
    right_mem_injection s j ge1 ge2 m1 m2 ->
    Genv.find_symbol ge1 id = Some b1 ->
    j b1 = Some (b2, delta) ->
    Genv.find_symbol ge2 id = Some b2.
  Proof.
    intros j m1 m2 id b1 b2 delta INJ FIND1 j_b1.
    exploit same_symb; eauto.
    intros (_ & H & ?).
    now destruct (H id b1 b2 delta j_b1 FIND1) as [??].
  Qed.

  (* This lemma relies on just one of the properties of
     [right_mem_injection], except for the appeal to (what is now
     known as) [right_mem_inj_find_symbol], namely Mem.delta_zero. *)
  Lemma right_mem_injection_list_match: forall j m1 m2 vargs1 vargs2 vl tyl,
    right_mem_injection s j ge1 ge2 m1 m2 ->
    (* Mem.delta_zero j -> *)
    Val.inject_list j vargs1 vargs2 ->
    eventval_list_match ge1 vl tyl vargs1 ->
    eventval_list_match ge2 vl tyl vargs2.
  Proof.
    intros j m1 m2 vargs1 vargs2 vl tyl RMEMINJ INJ. revert vl tyl.
    induction INJ; intros ? ? MATCH.
    - inv MATCH. constructor.
    - inv MATCH. constructor.
      + inv H; inv H4; try constructor.
        assert (delta = 0) as -> by (inv RMEMINJ; eauto).
        rewrite Ptrofs.add_zero.
        apply ev_match_ptr.
        * assert (PUBLIC: Genv.public_symbol ge1 id = true) by trivial.
          rewrite <- public_symbol_preserved in PUBLIC.
          auto.
        * (* Symbols are present in the program memory from the very
             beginning (cf. [Genv.init_mem] and the correspondence
             should also be reflected in and preserved by the memory
             injection. *)
          eapply right_mem_injection_find_symbol; eauto.
      + eauto.
  Qed.

  Remark right_env_injection_empty_env j:
    right_env_injection j empty_env empty_env.
  Proof.
    easy.
  Qed.

  Lemma right_tenv_injection_create_undef_temps j temps:
    right_tenv_injection
      j (create_undef_temps temps) (create_undef_temps temps).
  Proof.
    induction temps as [| [id ty] temps IHtemps].
    - intros id v GET.
      rewrite PTree.gempty in GET.
      discriminate.
    - intros id' v GET.
      destruct (peq id' id) as [-> | NEQ].
      + simpl. rewrite PTree.gss.
        simpl in GET. rewrite PTree.gss in GET.
        injection GET as <-.
        exists Vundef. auto.
      + simpl. rewrite PTree.gso; [| assumption].
        simpl in GET. rewrite PTree.gso in GET; [| assumption].
        eapply IHtemps; eauto.
  Qed.

  Lemma find_symbol_valid_block p m id b :
    same_blocks (globalenv p) m ->
    Genv.find_symbol (globalenv p) id = Some b ->
    Mem.valid_block m b.
  Proof.
    intros BLKS FIND.
    assert (exists cp, Genv.find_comp_of_block (globalenv p) b = Some cp)
      as (cp & ge_b).
    { unfold Genv.find_comp_of_block.
      destruct (Genv.find_symbol_find_def_inversion _ _ FIND)
        as [def ge_b].
      simpl; unfold program, fundef in *. rewrite ge_b; eauto. }
    apply BLKS in ge_b.
    apply Classical_Prop.NNPP. (* FIXME *)
    rewrite Mem.block_compartment_valid_block. congruence.
  Qed.

  Lemma block_is_volatile_valid_block p m b :
    same_blocks (globalenv p) m ->
    Genv.block_is_volatile (globalenv p) b = true ->
    Mem.valid_block m b.
  Proof.
    intros BLKS VOL.
    assert (exists cp, Genv.find_comp_of_block (globalenv p) b = Some cp)
      as (cp & ge_b).
    { unfold Genv.block_is_volatile, Genv.find_var_info in *.
      destruct Genv.find_def as [[|var]|] eqn:ge_b; try congruence.
      unfold Genv.find_comp_of_block.
      rewrite ge_b; eauto. }
    apply BLKS in ge_b.
    apply Classical_Prop.NNPP. (* FIXME *)
    rewrite Mem.block_compartment_valid_block. congruence.
  Qed.



  Lemma right_mem_injection_alloc {j f m1 m2 e1 e2 le1 le2 m1' b1 ty} id
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (RENVINJ: right_env_injection j e1 e2)
    (RTENVINJ: right_tenv_injection j le1 le2)
    (RIGHT: s |= (f: function) ∈ Right)
    (ALLOC: Mem.alloc m1 (comp_of f) 0 (sizeof ge1 ty) = (m1', b1)):
    exists j' m2' b2,
      Mem.alloc m2 (comp_of f) 0 (sizeof ge2 ty) = (m2', b2) /\
      right_mem_injection s j' ge1 ge2 m1' m2' /\
      inject_incr j j' /\
      right_env_injection j' (PTree.set id (b1, ty) e1) (PTree.set id (b2, ty) e2) /\
      right_tenv_injection j' le1 le2.
  Proof.
    destruct (Mem.alloc_parallel_inject _ _ _ _ _ _ _ _ _ _
                (partial_mem_inject _ _ _ _ _ _ RMEMINJ)
                ALLOC (Z.le_refl _) (Z.le_refl _))
      as (j' & m2' & b2 & ALLOC2' & INJ & INCR & ZERO & EXT).
    exists j', m2', b2.
    split; [| split; [| split; [| split]]].
    - rewrite sizeof_preserved. assumption.
    - destruct RMEMINJ as [DOM MI D0 SYMB MI_INJ BLKS1 BLKS2].
      constructor; auto.
      + intros b. specialize (DOM b).
        destruct Genv.invert_symbol as [id' |] eqn:INVERT.
        * (* Same as below, [b] must already be in the memory *)
          assert (NEQ: b <> b1).
          { eapply Mem.valid_block_alloc_inv'; eauto.
            clear -INVERT BLKS1. exploit find_symbol_valid_block; eauto.
            apply Genv.invert_find_symbol in INVERT. eauto. }
          simpl.
          rewrite (EXT _ NEQ), (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC).
          destruct eq_block as [| _]; [contradiction |].
          auto.
        * destruct (peq b b1) as [-> | NEQ].
          -- split.
             ++ intros _.
                simpl. rewrite (Mem.owned_new_block _ _ _ _ _ _ ALLOC).
                auto.
             ++ intros _ CONTRA.
                congruence.
          -- split.
             ++ intros j'_b. simpl.
                rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC).
                destruct eq_block as [| _]; [contradiction |].
                apply DOM.
                rewrite (EXT _ NEQ) in j'_b.
                auto.
             ++ intros RIGHT' j'_b.
                rewrite (EXT _ NEQ) in j'_b.
                apply DOM; [| assumption].
                simpl in RIGHT'.
                rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC) in RIGHT'.
                destruct eq_block as [| _]; [contradiction |].
                auto.
      + intros b1' b2' delta j'_b1. specialize (D0 b1' b2' delta).
        destruct (peq b1' b1) as [-> | NEQ].
        * rewrite ZERO in j'_b1. injection j'_b1 as <- <-.
          reflexivity.
        * specialize (EXT b1' NEQ). rewrite EXT in j'_b1.
          auto.
      + destruct SYMB as (PUB & FIND & PUB_FIND & VOL).
        split; [| split; [| split]].
        * auto.
        * intros id' b1' b2' delta b1'_b2' id'_b1'.
          specialize (FIND id' b1' b2' delta).
          (* [id] must already be found in the initial state from
             which the execution originates, so its assigned block
             cannot be newly allocated -- even if this information
             is not readily available in the invariant. See
             [Genv.find_symbol_not_fresh] *)
          assert (NEQ: b1' <> b1).
          { eapply Mem.valid_block_alloc_inv'; eauto.
            clear -id'_b1' BLKS1. simpl in *.
            exploit find_symbol_valid_block; eauto. }
          specialize (EXT _ NEQ). rewrite EXT in b1'_b2'.
          auto.
        * intros id' b1' PUB_id id_b1'.
          specialize (PUB_FIND id' b1' PUB_id id_b1') as (b2' & b1'_b2' & id'_b2').
          destruct (peq b1' b1) as [-> | NEQ].
          -- eauto.
          -- specialize (EXT _ NEQ). rewrite <- EXT in b1'_b2'.
             eauto.
        * intros b1' b2' delta b1'_b2'.
          (* Like symbols, volatile blocks are declared and defined at
             the outset and this property is invariant throughout
             program execution. See e.g. [Senv.block_is_volatile] and
             connections between pSenv.nextblock], [Genv.genv_next]
             and the initial program memory
             i.e. [Genv.init_mem_genv_next] *)
          destruct (peq b1' b1) as [-> | NEQ].
          -- assert (b2' = b2) as -> by congruence.
             assert (~ Mem.valid_block m1 b1).
             { eapply Mem.fresh_block_alloc; eauto. }
             assert (~ Mem.valid_block m2 b2).
             { eapply Mem.fresh_block_alloc; eauto. }
             assert (Senv.block_is_volatile ge1 b1 = false) as ->.
             { destruct Senv.block_is_volatile eqn:vol_b1; trivial.
               simpl in *. clear BLKS2.
               exploit block_is_volatile_valid_block; eauto. intros m1_b1.
               tauto. }
             assert (Senv.block_is_volatile ge2 b2 = false) as ->.
             { destruct Senv.block_is_volatile eqn:vol_b2; trivial.
               simpl in *. clear BLKS1.
               exploit block_is_volatile_valid_block; eauto. intros m2_b2.
               tauto. }
             reflexivity.
          -- rewrite (EXT _ NEQ) in b1'_b2'.
             exact (VOL _ _ _ b1'_b2').
      + intros b1' b2' b1'' b2'' ofs1 ofs2 b1'_b2' b1'_b1'' b2'_b2''.
        specialize (MI_INJ b1' b2' b1'' b2'' ofs1 ofs2 b1'_b2').
        destruct (peq b1' b1) as [-> | NEQ1].
        * left. intros <-.
          assert (b1'' = b2) as -> by congruence.
          clear b1'_b1''.
          assert (j b2' = Some (b2, ofs2)) as j_b2'.
          { rewrite <- EXT; congruence. }
          pose proof (Mem.mi_mappedblocks _ _ _ MI _ _ _ j_b2').
          clear ALLOC. exploit Mem.fresh_block_alloc; eauto.
        * rewrite (EXT _ NEQ1) in b1'_b1''.
          destruct (peq b2' b1) as [-> | NEQ2].
          -- assert (b2'' = b2) as -> by congruence.
             left. intros ->.
             clear NEQ1.
             pose proof (Mem.mi_mappedblocks _ _ _ MI _ _ _ b1'_b1'').
             clear ALLOC. exploit Mem.fresh_block_alloc; eauto.
          -- rewrite (EXT _ NEQ2) in b2'_b2''.
             auto.
      + intros b cp' FIND. specialize (BLKS1 b cp' FIND).
        change (Mem.block_compartment _ _ = _)
          with (Mem.can_access_block m1' b (Some cp')).
        eapply Mem.alloc_can_access_block_other_inj_1; eauto.
      + intros b cp' FIND. specialize (BLKS2 b cp' FIND).
        change (Mem.block_compartment _ _ = _)
          with (Mem.can_access_block m2' b (Some cp')).
        eapply Mem.alloc_can_access_block_other_inj_1; eauto.
    - assumption.
    - destruct RENVINJ as [ENVSOME ENDNONE]. split.
      + intros id' b ty' GET.
        destruct (peq id' id) as [-> | NEQ].
        * rewrite PTree.gss. rewrite PTree.gss in GET.
          injection GET as <- <-.
          eauto.
        * rewrite PTree.gso; [| assumption].
          rewrite PTree.gso in GET; [| assumption].
          specialize (ENVSOME id' b ty' GET) as (b' & b_b' & id'_b').
          eauto.
      + intros id' GET.
        destruct (peq id' id) as [-> | NEQ].
        * rewrite PTree.gss in GET.
          discriminate.
        * rewrite PTree.gso; [| assumption].
          rewrite PTree.gso in GET; [| assumption].
          specialize (ENDNONE id' GET). auto.
    - intros id' v GET. specialize (RTENVINJ id' v GET) as (v' & INJ' & GET').
      inv INJ'; eauto.
  Qed.

  Lemma right_mem_injection_alloc_variables {j f m1 m1' m2 e1 e1' e2 le1 le2 vars}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (RENVINJ: right_env_injection j e1 e2)
    (RTENVINJ: right_tenv_injection j le1 le2)
    (RIGHT: s |= (f: function) ∈ Right)
    (ALLOC: alloc_variables ge1 (comp_of f) e1 m1 vars e1' m1'):
    exists j' e2' m2',
      alloc_variables ge2 (comp_of f) e2 m2 vars e2' m2' /\
      right_mem_injection s j' ge1 ge2 m1' m2' /\
      inject_incr j j' /\
      right_env_injection j' e1' e2' /\
      right_tenv_injection j' le1 le2.
  Proof.
    revert j m2 e2 le1 le2 RMEMINJ RENVINJ RTENVINJ RIGHT.
    induction ALLOC;
      intros.
    - exists j, e2, m2. split; [constructor | auto].
    - destruct (right_mem_injection_alloc id RMEMINJ RENVINJ RTENVINJ RIGHT H)
        as (j' & m2' & b2 & ALLOC' & RMEMINJ' & INCR & RENVINJ' & RTENVINJ').
      specialize (IHALLOC _ _ _ _ _ RMEMINJ' RENVINJ' RTENVINJ' RIGHT)
        as (j'' & e2' & m2'' & ALLOC2 & RMEMINJ'' & INCR' & RENVINJ'' & RTENVINJ'').
      exists j'', e2', m2''. split; [| split; [| split; [| split]]]; auto.
      + econstructor; eauto.
      + intros b b' delta b_b'.
        specialize (INCR _ _ _ b_b').
        specialize (INCR' _ _ _ INCR).
        auto.
  Qed.

  Lemma right_mem_injection_assign_loc {j f m1 m1' m2 e1 e2 le1 le2 v1 v2 id ty b1}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (RENVINJ: right_env_injection j e1 e2)
    (RTENVINJ: right_tenv_injection j le1 le2)
    (RIGHT: s |= (f: function) ∈ Right)
    (LOOKUP: e1 ! id = Some (b1, ty))
    (VALINJ: Val.inject j v1 v2)
    (ASSIGN: assign_loc ge1 (comp_of f) ty m1 b1 Ptrofs.zero Full v1 m1'):
    exists m2' b2,
      e2 ! id = Some (b2, ty) /\
      assign_loc ge2 (comp_of f) ty m2 b2 Ptrofs.zero Full v2 m2' /\
      right_mem_injection s j ge1 ge2 m1' m2'.
  Proof.
    destruct RMEMINJ as [DOM MI D0 SYMB MI_INJ BLKS1 BLKS2].
    inv ASSIGN.
    - destruct (proj1 RENVINJ _ _ _ LOOKUP) as (b2 & b1_b2 & LOOKUP').
      exploit Mem.store_mapped_inject; eauto.
      intros (m2' & STORE' & INJ').
      exists m2', b2. split; [| split].
      + assumption.
      + eapply assign_loc_value; eauto.
      + constructor; auto.
        * simpl in *. clear STORE'.
          eapply (same_domain_store _ _ _ _ _ _ _ _ _ _ H0 DOM).
        * eapply same_blocks_store; eauto.
        * eapply same_blocks_store; eauto.
    - destruct (proj1 RENVINJ _ _ _ LOOKUP) as (b2 & b1_b2 & LOOKUP').
      rename b' into b1'.
      rename ofs' into ofs1.
      rename H2 into BOUNDS1.
      assert (exists b2' delta,
         j b1' = Some (b2', delta) /\
          v2 = Vptr b2' (Ptrofs.add ofs1 (Ptrofs.repr delta)))
        as (b2' & delta & b1'_b2' & ->).
      { inv VALINJ; eauto. }
      pose proof (D0 _ _ _ b1'_b2') as ->.
      rewrite Ptrofs.add_zero.
      exploit Mem.loadbytes_inject; eauto. intros (bytes2 & LOAD2 & INJ).
      rewrite Z.add_0_r in LOAD2.
      exploit Mem.storebytes_mapped_inject; eauto.
      intros (m2' & STORE2 & INJ').
      exists m2', b2. split; trivial; split.
      + rewrite genv_cenv_preserved.
        eapply assign_loc_copy; eauto.
        destruct BOUNDS1 as [NEQ1|BOUNDS1]; [|now right].
        left.
        destruct (MI_INJ _ _ _ _ _ _ NEQ1 b1'_b2' b1_b2); congruence.
      + constructor; eauto.
        * simpl in *. clear STORE2.
          eapply (same_domain_storebytes _ _ _ _ _ _ _ _ _ H4 DOM).
        * eapply same_blocks_storebytes; eauto.
        * eapply same_blocks_storebytes; eauto.
  Qed.

  Lemma right_mem_injection_bind_parameters
    {j f m1 m1' m2 e1 e2 le1 le2 vargs1 vargs2 params}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (RENVINJ: right_env_injection j e1 e2)
    (RTENVINJ: right_tenv_injection j le1 le2)
    (RIGHT: s |= (f: function) ∈ Right)
    (VALINJ: Val.inject_list j vargs1 vargs2)
    (BIND: bind_parameters ge1 (comp_of f) e1 m1 params vargs1 m1'):
    exists m2',
      bind_parameters ge2 (comp_of f) e2 m2 params vargs2 m2' /\
      right_mem_injection s j ge1 ge2 m1' m2'.
  Proof.
    revert m2 vargs2 RMEMINJ VALINJ.
    induction BIND; intros.
    - exists m2. split.
      + inv VALINJ. constructor.
      + assumption.
    - inv VALINJ.
      destruct (right_mem_injection_assign_loc RMEMINJ RENVINJ RTENVINJ RIGHT H H3 H0)
        as (m2' & b2 & LOOKUP' & ASSIGN' & RMEMINJ').
      destruct (IHBIND _ _ RMEMINJ' H5) as (m2'' & BIND' & RMEMINJ'').
      exists m2''. split.
      + econstructor; eauto.
      + assumption.
  Qed.

  Lemma right_mem_injection_function_entry1: forall
    {j f m1 m2 vargs1 vargs2 e1 le1 m1'},
    right_mem_injection s j ge1 ge2 m1 m2 ->
    Val.inject_list j vargs1 vargs2 ->
    s |= f ∈ Right ->
    function_entry1 ge1 f vargs1 m1 e1 le1 m1' ->
    exists j' e2 le2 m2',
      function_entry1 ge2 f vargs2 m2 e2 le2 m2' /\
      inject_incr j j' /\
      right_mem_injection s j' ge1 ge2 m1' m2' /\
      right_env_injection j' e1 e2 /\
      right_tenv_injection
        j' (create_undef_temps (fn_temps f)) (create_undef_temps (fn_temps f)).
  Proof.
    intros until m1'; intros RMEMINJ VALINJ RIGHT ENTRY.
    inversion ENTRY; subst.
    assert (RENVINJ0 := right_env_injection_empty_env j).
    assert (RTENVINJ0 := right_tenv_injection_create_undef_temps j (fn_temps f)).
    destruct (right_mem_injection_alloc_variables RMEMINJ RENVINJ0 RTENVINJ0 RIGHT H0)
      as (j' & e2 & m2' & ALLOC2 & RMEMINJ' & INCR & RENVINJ' & RTENVINJ').
    assert (VALINJ': Val.inject_list j' vargs1 vargs2). {
      clear -VALINJ INCR.
      induction VALINJ; [constructor |].
      constructor; [| assumption].
      inv H; try constructor.
      eapply Val.inject_ptr; [| reflexivity].
      auto. }
    destruct (right_mem_injection_bind_parameters
                RMEMINJ' RENVINJ' RTENVINJ' RIGHT VALINJ' H1)
      as (m2'' & BIND2 & MEMINJ'').
    exists j', e2, (create_undef_temps (fn_temps f)), m2''.
    split; [| split; [| split]]; auto.
    econstructor; eauto.
  Qed.

  Lemma right_mem_injection_external_call {j ef vargs1 vargs2 vres1 t m1 m1' m2}
    (RMEMINJ : right_mem_injection s j ge1 ge2 m1 m2)
    (EXTCALL: external_call ef ge1 vargs1 m1 t vres1 m1')
    (ARGINJ: Val.inject_list j vargs1 vargs2):
    exists j' m2' vres2,
      external_call ef ge2 vargs2 m2 t vres2 m2' /\
      right_mem_injection s j' ge1 ge2 m1' m2' /\
      inject_incr j j' /\
      Val.inject j' vres1 vres2.
  Proof.
    exploit ec_mem_inject; eauto.
    { apply external_call_spec. }
    { eapply same_symb; eauto. }
    { eapply partial_mem_inject; eauto. }
    intros (j' & vres2 & m2' & ? & ? & ?  & ? & ? & ? & ? & ?).
    exists j', m2', vres2.
    split; [| split; [| split]]; auto.
    constructor; eauto.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma memval_inject_alloc {j m1 m2 b1 b2 ofs delta cp lo hi m1' m2' b1' b2'}
    (INJ: memval_inject j
            (ZMap.get ofs (Mem.mem_contents m1) !! b1)
            (ZMap.get (ofs + delta) (Mem.mem_contents m2) !! b2))
    (b1_b2: j b1 = Some (b2, delta))
    (ALLOC1: Mem.alloc m1 cp lo hi = (m1', b1'))
    (ALLOC2: Mem.alloc m2 cp lo hi = (m2', b2')):
    memval_inject j
      (ZMap.get ofs (Mem.mem_contents m1') !! b1)
      (ZMap.get (ofs + delta) (Mem.mem_contents m2') !! b2).
  Admitted.

  (** Sub-invariant lemmas, mostly on injections *)

  Lemma right_mem_injection_left_step_E0_1: forall j s1 s2 s1',
    right_mem_injection s j ge1 ge2 (memory_of s1) (memory_of s2) ->
    s |= s1 ∈ Left ->
    step1 ge1 s1 E0 s1' ->
  exists j',
    right_mem_injection s j' ge1 ge2 (memory_of s1') (memory_of s2) /\
    inject_incr j j' .
  Proof.
    intros j s1 s2 s1' RMEMINJ LEFT STEP.
    (* exists j. (* FIXME: this falls back to the old form of the lemma *) *)
    inversion RMEMINJ as [DOM MEMINJ ZERO SYMB INJ BLKS].
    inversion STEP; subst; try eauto.
    - (* assign *)
      exists j. split; [| now apply inject_incr_refl].
      constructor; try assumption;
        [| | eapply same_blocks_step1; eassumption].
      {
      - intros b. specialize (DOM b).
        destruct Genv.invert_symbol as [id |] eqn:INVSYM.
        + destruct Senv.public_symbol eqn:PUBSYM; [assumption |].
          simpl. simpl in DOM. split.
          * intros j_b. destruct DOM as [DOM _]. specialize (DOM j_b).
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP;
              [| contradiction].
            rewrite (assign_loc_block_compartment H2) in COMP.
            rewrite COMP. assumption.
          * intros RIGHT. destruct DOM as [_ DOM].
            destruct (Mem.block_compartment m' b) as [cp' |] eqn:COMP';
              [| contradiction].
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP.
            -- assert (cp = cp') as <-
                 by (eapply assign_block_block_compartment_eq; eauto).
               exact (DOM RIGHT).
            -- rewrite (assign_loc_block_compartment H2) in COMP. congruence.
        + simpl. simpl in DOM. split.
          * intros j_b. destruct DOM as [DOM _]. specialize (DOM j_b).
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP;
              [| contradiction].
            rewrite <- (assign_loc_block_compartment H2), COMP. assumption.
          * simpl. simpl in DOM. intros RIGHT. destruct DOM as [_ DOM].
            destruct (Mem.block_compartment m' b) as [cp' |] eqn:COMP';
              [| contradiction].
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP.
            -- assert (cp = cp') as <-
                 by (eapply assign_block_block_compartment_eq; eauto).
               exact (DOM RIGHT).
            -- rewrite (assign_loc_block_compartment H2) in COMP. congruence.
      }
      { inv MEMINJ.
        constructor; auto.
        { (* Factor out lemma *)
          inv mi_inj. constructor.
          - intros b1 b2 delta ofs' k' p' b1_b2 PERM.
            apply (perm_assign_loc_2 H2) in PERM.
            exact (mi_perm b1 b2 delta ofs' k' p' b1_b2 PERM).
          - intros b1 b2 delta [cp |] b1_b2 ACC; [| reflexivity].
            change (Mem.can_access_block _ _ _)
              with (Mem.block_compartment m' b1 = Some cp) in ACC.
            rewrite <- (assign_loc_block_compartment H2) in ACC.
            exact (mi_own b1 b2 delta (Some cp) b1_b2 ACC).
          - intros b1 b2 delta chunk ofs' p b1_b2 PERM.
            apply (assign_loc_range_perm H2) in PERM.
            exact (mi_align b1 b2 delta chunk ofs' p b1_b2 PERM).
          - intros b1 ofs' b2 delta b1_b2 PERM.
            apply (assign_loc_perm H2) in PERM.
            specialize (mi_memval b1 ofs' b2 delta b1_b2 PERM).
            (* b1 is in the injection so it is either
               - a public symbol
               - a non-public symbol on the right
                 (contra, impossible to get ahold of from the left, where we are)
               - a non-symbol on the right
                 (contra, impossible to get ahold of from the left, where we are) *)
            admit.
        }
        { intros b NOTVALID. specialize (mi_freeblocks b).
          apply mi_freeblocks. intro CONTRA. apply NOTVALID.
          eapply assign_loc_valid_block_1; eauto.
        }
        { intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 j_b1 j_b2 PERM1 PERM2.
          specialize (mi_no_overlap b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 j_b1 j_b2).
          apply mi_no_overlap.
          - exact (perm_assign_loc_2 H2 PERM1).
          - exact (perm_assign_loc_2 H2 PERM2).
        }
        { intros b b' delta ofs' b_b' PERM.
          specialize (mi_representable b b' delta ofs' b_b').
          apply mi_representable. destruct PERM as [PERM | PERM].
          - left. exact (perm_assign_loc_2 H2 PERM).
          - right. exact (perm_assign_loc_2 H2 PERM). }
        { intros b1 ofs' b2 delta k' p b1_b2 PERM.
          specialize (mi_perm_inv b1 ofs' b2 delta k' p b1_b2 PERM).
          destruct mi_perm_inv as [PERM' | PERM'].
          - left. exact (perm_assign_loc_1 H2 PERM').
          - right. intros CONTRA. apply PERM'. exact (perm_assign_loc_2 H2 CONTRA). }
      }
    - (* builtin *)
      (* FIXME *)
      exists j. split; [| now apply inject_incr_refl].
      constructor; try assumption;
        [| | eapply same_blocks_step1; eassumption].
      {
      - intros b; specialize (DOM b).
        destruct Genv.invert_symbol as [id |] eqn:INVSYM.
        + destruct Senv.public_symbol eqn:PUBSYM; [assumption |].
          simpl. simpl in DOM. split.
          * intros j_b. destruct DOM as [DOM _]. specialize (DOM j_b).
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP;
              [| contradiction].
            change (Mem.block_compartment _ _ = _ )
              with (Mem.can_access_block m b (Some cp)) in COMP.
            rewrite (external_call_can_access_block _ _ _ _ _ _ _ _ _ H0 COMP).
            assumption.
          * intros RIGHT. destruct DOM as [_ DOM].
            destruct (Mem.block_compartment m' b) as [cp' |] eqn:COMP';
              [| contradiction].
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP.
            -- assert (cp = cp') as <-. {
                 change (Mem.block_compartment _ _ = _ )
                   with (Mem.can_access_block m b (Some cp)) in COMP.
                 rewrite (external_call_can_access_block _ _ _ _ _ _ _ _ _ H0 COMP) in COMP'.
                 congruence. }
               exact (DOM RIGHT).
            -- (* Easy, contra on LEFT and RIGHT with H0 *)
               apply Mem.block_compartment_valid_block in COMP.
               assert (VALID: Mem.valid_block m' b). {
                 destruct (plt b (Mem.nextblock m')) as [G | CONTRA];
                   [exact G |].
                 apply Mem.block_compartment_valid_block in CONTRA.
                 congruence. }
               rewrite (ec_new_valid (external_call_spec ef) _ _ _ _ H0 COMP VALID)
                 in COMP'.
               injection COMP' as <-.
               congruence.
        + simpl. simpl in DOM. split.
          * intros j_b. destruct DOM as [DOM _]. specialize (DOM j_b).
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP;
              [| contradiction].
            change (Mem.block_compartment _ _ = _ )
              with (Mem.can_access_block m b (Some cp)) in COMP.
            rewrite (external_call_can_access_block _ _ _ _ _ _ _ _ _ H0 COMP).
            assumption.
          * intros RIGHT. destruct DOM as [_ DOM].
            destruct (Mem.block_compartment m' b) as [cp' |] eqn:COMP';
              [| contradiction].
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP.
            -- assert (cp = cp') as <-. {
                 change (Mem.block_compartment _ _ = _ )
                   with (Mem.can_access_block m b (Some cp)) in COMP.
                 rewrite (external_call_can_access_block _ _ _ _ _ _ _ _ _ H0 COMP) in COMP'.
                 congruence. }
               exact (DOM RIGHT).
            -- (* If any newly allocated [b] belongs to [comp_of ef] = [comp_of f]
                  (which is on the left), and since [b] belongs to [cp'] (which is
                  on the right), this is a contradiction. *)
               (* same as contra above *)
               apply Mem.block_compartment_valid_block in COMP.
               assert (VALID: Mem.valid_block m' b). {
                 destruct (plt b (Mem.nextblock m')) as [G | CONTRA];
                   [exact G |].
                 apply Mem.block_compartment_valid_block in CONTRA.
                 congruence. }
               rewrite (ec_new_valid (external_call_spec ef) _ _ _ _ H0 COMP VALID)
                 in COMP'.
               injection COMP' as <-.
               congruence.
      }
      { (* New injection *)
        simpl in *.
        inversion MEMINJ.
        constructor.
        - admit.
        - intros b VALID.
          apply mi_freeblocks.
          intros CONTRA. apply VALID.
          eapply (ec_valid_block (external_call_spec ef)); eassumption.
        - intros b b' delta b_b'.
          specialize (mi_mappedblocks b b' delta b_b').
          assumption.
        - intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 b1_b1' b2_b2' PERM1 PERM2.
          assert (VALID1 : Mem.valid_block m b1). { (* lemma *)
            unfold Mem.valid_block. destruct (plt b1 (Mem.nextblock m)) as [| INVALID];
              [assumption |].
            eapply Mem.mi_freeblocks in INVALID; try eassumption.
            congruence. }
          assert (VALID2 : Mem.valid_block m b2). { (* lemma *)
            unfold Mem.valid_block. destruct (plt b2 (Mem.nextblock m)) as [| INVALID];
              [assumption |].
            eapply Mem.mi_freeblocks in INVALID; try eassumption.
            congruence. }
          assert (PERM1' :=
                    ec_max_perm (external_call_spec ef) _ _ _ _ _ _ _ H0 VALID1 PERM1).
          assert (PERM2' :=
                    ec_max_perm (external_call_spec ef) _ _ _ _ _ _ _ H0 VALID2 PERM2).
          eapply mi_no_overlap; eassumption.
        - intros b b' delta ofs b_b' PERM.
          assert (VALID1 : Mem.valid_block m b). { (* lemma *)
            unfold Mem.valid_block. destruct (plt b (Mem.nextblock m)) as [| INVALID];
              [assumption |].
            eapply Mem.mi_freeblocks in INVALID; try eassumption.
            congruence. }
          assert (PERM': Mem.perm m b (Ptrofs.unsigned ofs) Max Nonempty \/
                         Mem.perm m b (Ptrofs.unsigned ofs - 1) Max Nonempty). {
            destruct PERM as [PERM | PERM].
            - left. eapply (ec_max_perm (external_call_spec ef)); eassumption.
            - right. eapply (ec_max_perm (external_call_spec ef)); eassumption. }
          eapply mi_representable; eassumption.
        - intros b1 ofs b2 delta k' p b1_b2 PERM.
          specialize (mi_perm_inv b1 ofs b2 delta k' p b1_b2 PERM).
          admit.
      }
    - (* return 0 *)
      exists j. split; [| now apply inject_incr_refl].
      constructor; try assumption;
        [| | eapply same_blocks_step1; eassumption].
      {
      - eapply same_domain_free_list; eauto.
      }
      {
      eapply Mem.free_list_left_inject; eauto.
      }
    - (* return 1 *)
      exists j. split; [| now apply inject_incr_refl].
      constructor; try assumption;
        [| | eapply same_blocks_step1; eassumption].
      {
      - eapply same_domain_free_list; eauto.
      }
      {
      eapply Mem.free_list_left_inject; eauto.
      }
    - (* skip call *)
      exists j. split; [| now apply inject_incr_refl].
      constructor; try assumption;
        [| | eapply same_blocks_step1; eassumption].
      {
      - eapply same_domain_free_list; eauto.
      }
      {
      eapply Mem.free_list_left_inject; eauto.
      }
    - (* internal function *)
      exists j. split; [| now apply inject_incr_refl].
      constructor; try assumption;
        [| | eapply same_blocks_step1; eassumption].
      {
      - inv H.
        intros b. specialize (DOM b).
        destruct Genv.invert_symbol as [id |] eqn:INVSYM.
        + destruct Senv.public_symbol eqn:PUBSYM; [assumption |].
          simpl. simpl in DOM. split.
          * intros j_b. destruct DOM as [DOM _]. specialize (DOM j_b).
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP;
              [| contradiction].
            change (Mem.block_compartment _ _ = _)
              with (Mem.can_access_block m b (Some cp)) in COMP.
            apply (alloc_variables_can_access_block_1 H1) in COMP.
            apply (bind_parameters_can_access_block_1 H2) in COMP.
            rewrite COMP. assumption.
          * intros RIGHT. destruct DOM as [_ DOM].
            destruct (Mem.block_compartment m1 b) as [cp' |] eqn:COMP';
              [| contradiction].
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP.
            -- assert (cp = cp') as <-. {
                 change (Mem.block_compartment _ _ = _)
                   with (Mem.can_access_block m b (Some cp)) in COMP.
                 apply (alloc_variables_can_access_block_1 H1) in COMP.
                 apply (bind_parameters_can_access_block_1 H2) in COMP.
                 congruence. }
               exact (DOM RIGHT).
            -- (* Easy, contra on LEFT and RIGHT with H1 and H2 *)
               apply Mem.block_compartment_valid_block in COMP.
               change (Mem.block_compartment _ _ = _)
                 with (Mem.can_access_block m1 b (Some cp')) in COMP'.
               apply (bind_parameters_can_access_block_2 H2) in COMP'.
               rewrite <- (alloc_variables_can_access_block_fresh H1 COMP COMP')
                 in RIGHT.
               simpl in LEFT. unfold comp_of in LEFT. simpl in LEFT.
               congruence.
        + simpl. simpl in DOM. split.
          * intros j_b. destruct DOM as [DOM _]. specialize (DOM j_b).
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP;
              [| contradiction].
            (* same as above *)
            change (Mem.block_compartment _ _ = _)
              with (Mem.can_access_block m b (Some cp)) in COMP.
            apply (alloc_variables_can_access_block_1 H1) in COMP.
            apply (bind_parameters_can_access_block_1 H2) in COMP.
            rewrite COMP. assumption.
          * intros RIGHT. destruct DOM as [_ DOM].
            destruct (Mem.block_compartment m1 b) as [cp' |] eqn:COMP';
              [| contradiction].
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP.
            -- assert (cp = cp') as <-.  {
                 change (Mem.block_compartment _ _ = _)
                   with (Mem.can_access_block m b (Some cp)) in COMP.
                 apply (alloc_variables_can_access_block_1 H1) in COMP.
                 apply (bind_parameters_can_access_block_1 H2) in COMP.
                 congruence. }
               exact (DOM RIGHT).
            -- (* Same as above sub-case *)
               apply Mem.block_compartment_valid_block in COMP.
               change (Mem.block_compartment _ _ = _)
                 with (Mem.can_access_block m1 b (Some cp')) in COMP'.
               apply (bind_parameters_can_access_block_2 H2) in COMP'.
               rewrite <- (alloc_variables_can_access_block_fresh H1 COMP COMP')
                 in RIGHT.
               simpl in LEFT. unfold comp_of in LEFT. simpl in LEFT.
               congruence.
      }
      { inv H. inv MEMINJ.
        constructor.
        - { (* Factor out lemma *)
          inv mi_inj. constructor.
          - intros b1 b2 delta ofs' k' p' b1_b2 PERM.
            assert (VALID: Mem.valid_block m b1). { (* extract lemma *)
              destruct (plt b1 (Mem.nextblock m)) as [LT | GE];
                [exact LT |].
              specialize (mi_freeblocks _ GE).
              congruence. }
            specialize (mi_perm b1 b2 delta ofs' k' p' b1_b2).
            apply (bind_parameters_perm_2 H2) in PERM.
            apply (alloc_variables_perm_2 H1) in PERM; auto.
          - intros b1 b2 delta cp b1_b2 ACC.
            assert (VALID: Mem.valid_block m b1). { (* extract lemma *)
              destruct (plt b1 (Mem.nextblock m)) as [LT | GE];
                [exact LT |].
              specialize (mi_freeblocks _ GE).
              congruence. }
            specialize (mi_own b1 b2 delta cp b1_b2). apply mi_own.
            apply (bind_parameters_can_access_block_2 H2) in ACC.
            apply (alloc_variables_can_access_block_2 H1) in ACC; auto.
          - intros b1 b2 delta chunk ofs p b1_b2 PERM.
            assert (VALID: Mem.valid_block m b1). { (* extract lemma *)
              destruct (plt b1 (Mem.nextblock m)) as [LT | GE];
                [exact LT |].
              specialize (mi_freeblocks _ GE).
              congruence. }
            specialize (mi_align b1 b2 delta chunk ofs p b1_b2). apply mi_align.
            apply (bind_parameters_range_perm_2 H2) in PERM.
            apply (alloc_variables_range_perm_2 H1) in PERM; eauto.
          - intros b1 ofs b2 delta b1_b2 PERM.
            assert (VALID: Mem.valid_block m b1). { (* extract lemma *)
              destruct (plt b1 (Mem.nextblock m)) as [LT | GE];
                [exact LT |].
              specialize (mi_freeblocks _ GE).
              congruence. }
            (* easy: [b1] is already present in [m] and consequently its
               contents are not affected by either [alloc_variables] or
               [bind_parameters] *)
            apply (bind_parameters_perm_2 H2) in PERM.
            apply (alloc_variables_perm_2 H1) in PERM; auto.
            specialize (mi_memval b1 ofs b2 delta b1_b2 PERM).
            simpl. simpl in mi_memval.
            admit. (* easy, see above *)
          }
        - intros b VALID. specialize (mi_freeblocks b).
          apply mi_freeblocks. intros CONTRA. apply VALID.
          simpl in *.
          eapply bind_parameters_valid_block_1; eauto.
          eapply alloc_variables_valid_block_1; eauto.
        - auto.
        - intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 b1_b1' b2_b2' PERM1 PERM2.
          specialize (mi_no_overlap
                        b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 b1_b1' b2_b2').
          assert (VALID1: Mem.valid_block m b1). { (* extract lemma *)
            destruct (plt b1 (Mem.nextblock m)) as [LT | GE];
              [exact LT |].
            specialize (mi_freeblocks _ GE).
            congruence. }
          assert (VALID2: Mem.valid_block m b2). { (* extract lemma *)
            destruct (plt b2 (Mem.nextblock m)) as [LT | GE];
              [exact LT |].
            specialize (mi_freeblocks _ GE).
            congruence. }
          apply (bind_parameters_perm_2 H2) in PERM1, PERM2.
          apply (alloc_variables_perm_2 H1) in PERM1, PERM2; eauto.
        - intros b b' delta ofs b_b' PERM.
          specialize (mi_representable b b' delta ofs b_b').
          apply mi_representable.
          destruct PERM as [PERM | PERM].
          + left.
            assert (VALID: Mem.valid_block m b). { (* extract lemma *)
              destruct (plt b (Mem.nextblock m)) as [LT | GE];
                [exact LT |].
              specialize (mi_freeblocks _ GE).
              congruence. }
            apply (alloc_variables_perm_2 H1); eauto.
            apply (bind_parameters_perm_2 H2); eauto.
          + right.
            (* exactly the same script as the previous case *)
            assert (VALID: Mem.valid_block m b). { (* extract lemma *)
              destruct (plt b (Mem.nextblock m)) as [LT | GE];
                [exact LT |].
              specialize (mi_freeblocks _ GE).
              congruence. }
            apply (alloc_variables_perm_2 H1); eauto.
            apply (bind_parameters_perm_2 H2); eauto.
        - intros b1 ofs b2 delta k' p' b1_b2 PERM.
          specialize (mi_perm_inv b1 ofs b2 delta k' p' b1_b2 PERM)
            as [PERM' | PERM'].
          + left.
            eapply bind_parameters_perm_1; eauto.
            eapply alloc_variables_perm_1; eauto.
          + right. intros CONTRA. apply PERM'.
            (* see cases above *)
            assert (VALID: Mem.valid_block m b1). { (* extract lemma *)
              destruct (plt b1 (Mem.nextblock m)) as [LT | GE];
                [exact LT |].
              specialize (mi_freeblocks _ GE).
              congruence. }
            apply (alloc_variables_perm_2 H1); eauto.
            apply (bind_parameters_perm_2 H2); eauto.
      }
    - (* external call *)
      (* FIXME *)
      exists j. split; [| now apply inject_incr_refl].
      constructor; try assumption;
        [| | eapply same_blocks_step1; eassumption].
      {
      - (* See [external_call] above (second sub-case) *)
        (* identical, except H0 is H,
           and LEFT requires simplification in a couple of places:
             [simpl in LEFT. unfold comp_of in LEFT. simpl in LEFT.] *)
        intros b; specialize (DOM b).
        destruct Genv.invert_symbol as [id |] eqn:INVSYM.
        + destruct Senv.public_symbol eqn:PUBSYM; [assumption |].
          simpl. simpl in DOM. split.
          * intros j_b. destruct DOM as [DOM _]. specialize (DOM j_b).
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP;
              [| contradiction].
            change (Mem.block_compartment _ _ = _ )
              with (Mem.can_access_block m b (Some cp)) in COMP.
            rewrite (external_call_can_access_block _ _ _ _ _ _ _ _ _ H COMP).
            assumption.
          * intros RIGHT. destruct DOM as [_ DOM].
            destruct (Mem.block_compartment m' b) as [cp' |] eqn:COMP';
              [| contradiction].
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP.
            -- assert (cp = cp') as <-. {
                 change (Mem.block_compartment _ _ = _ )
                   with (Mem.can_access_block m b (Some cp)) in COMP.
                 rewrite (external_call_can_access_block _ _ _ _ _ _ _ _ _ H COMP) in COMP'.
                 congruence. }
               exact (DOM RIGHT).
            -- (* Easy, contra on LEFT and RIGHT with H0 *)
               apply Mem.block_compartment_valid_block in COMP.
               assert (VALID: Mem.valid_block m' b). {
                 destruct (plt b (Mem.nextblock m')) as [G | CONTRA];
                   [exact G |].
                 apply Mem.block_compartment_valid_block in CONTRA.
                 congruence. }
               rewrite (ec_new_valid (external_call_spec ef) _ _ _ _ H COMP VALID)
                 in COMP'.
               injection COMP' as <-.
               simpl in LEFT. unfold comp_of in LEFT. simpl in LEFT.
               congruence.
        + simpl. simpl in DOM. split.
          * intros j_b. destruct DOM as [DOM _]. specialize (DOM j_b).
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP;
              [| contradiction].
            change (Mem.block_compartment _ _ = _ )
              with (Mem.can_access_block m b (Some cp)) in COMP.
            rewrite (external_call_can_access_block _ _ _ _ _ _ _ _ _ H COMP).
            assumption.
          * intros RIGHT. destruct DOM as [_ DOM].
            destruct (Mem.block_compartment m' b) as [cp' |] eqn:COMP';
              [| contradiction].
            destruct (Mem.block_compartment m b) as [cp |] eqn:COMP.
            -- assert (cp = cp') as <-. {
                 change (Mem.block_compartment _ _ = _ )
                   with (Mem.can_access_block m b (Some cp)) in COMP.
                 rewrite (external_call_can_access_block _ _ _ _ _ _ _ _ _ H COMP) in COMP'.
                 congruence. }
               exact (DOM RIGHT).
            -- (* If any newly allocated [b] belongs to [comp_of ef] = [comp_of f]
                  (which is on the left), and since [b] belongs to [cp'] (which is
                  on the right), this is a contradiction. *)
               (* same as contra above *)
               apply Mem.block_compartment_valid_block in COMP.
               assert (VALID: Mem.valid_block m' b). {
                 destruct (plt b (Mem.nextblock m')) as [G | CONTRA];
                   [exact G |].
                 apply Mem.block_compartment_valid_block in CONTRA.
                 congruence. }
               rewrite (ec_new_valid (external_call_spec ef) _ _ _ _ H COMP VALID)
                 in COMP'.
               injection COMP' as <-.
               simpl in LEFT. unfold comp_of in LEFT. simpl in LEFT.
               congruence.
      }
      { (* New injection *)
        (* external call on the left, isolate effects on injection according to DOM *)
        (* destruct (external_call_spec ef). *)
        (* any new blocks belong to [ef]'s compartment, so they are on the left
           those new blocks do not correspond to any symbol names
           so because they are not on the right, they are not in the injection
           (the external call doesn't produce an observable event either) *)
        (* destruct (external_call_spec ef). *)
        simpl in *.
        inversion MEMINJ.
        constructor.
        - admit.
        - intros b VALID.
          apply mi_freeblocks.
          intros CONTRA. apply VALID.
          eapply (ec_valid_block (external_call_spec ef)); eassumption.
        - intros b b' delta b_b'.
          specialize (mi_mappedblocks b b' delta b_b').
          assumption.
        - intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 b1_b1' b2_b2' PERM1 PERM2.
          assert (VALID1 : Mem.valid_block m b1). { (* lemma *)
            unfold Mem.valid_block. destruct (plt b1 (Mem.nextblock m)) as [| INVALID];
              [assumption |].
            eapply Mem.mi_freeblocks in INVALID; try eassumption.
            congruence. }
          assert (VALID2 : Mem.valid_block m b2). { (* lemma *)
            unfold Mem.valid_block. destruct (plt b2 (Mem.nextblock m)) as [| INVALID];
              [assumption |].
            eapply Mem.mi_freeblocks in INVALID; try eassumption.
            congruence. }
          assert (PERM1' :=
                    ec_max_perm (external_call_spec ef) _ _ _ _ _ _ _ H VALID1 PERM1).
          assert (PERM2' :=
                    ec_max_perm (external_call_spec ef) _ _ _ _ _ _ _ H VALID2 PERM2).
          eapply mi_no_overlap; eassumption.
        - intros b b' delta ofs b_b' PERM.
          assert (VALID1 : Mem.valid_block m b). { (* lemma *)
            unfold Mem.valid_block. destruct (plt b (Mem.nextblock m)) as [| INVALID];
              [assumption |].
            eapply Mem.mi_freeblocks in INVALID; try eassumption.
            congruence. }
          assert (PERM': Mem.perm m b (Ptrofs.unsigned ofs) Max Nonempty \/
                         Mem.perm m b (Ptrofs.unsigned ofs - 1) Max Nonempty). {
            destruct PERM as [PERM | PERM].
            - left. eapply (ec_max_perm (external_call_spec ef)); eassumption.
            - right. eapply (ec_max_perm (external_call_spec ef)); eassumption. }
          eapply mi_representable; eassumption.
        - intros b1 ofs b2 delta k' p b1_b2 PERM.
          specialize (mi_perm_inv b1 ofs b2 delta k' p b1_b2 PERM).
          admit.
      }
  Admitted.

  Lemma right_cont_injection_left_step_E0_1: forall j s1 s2 s1',
    right_cont_injection s j (remove_until_right s (cont_of s1)) (remove_until_right s (cont_of s2)) ->
    s |= s1 ∈ Left ->
    step1 ge1 s1 E0 s1' ->
    right_cont_injection s j (remove_until_right s (cont_of s1')) (remove_until_right s (cont_of s2)).
  Admitted.

  Lemma right_cont_injection_left_step_E0_2: forall j s1 s2 s1',
    right_cont_injection s j (cont_of s1) (cont_of s2) ->
    s |= s1 ∈ Left ->
    step1 ge1 s1 E0 s1' ->
    right_cont_injection s j (cont_of s1') (cont_of s2).
  Admitted. (* Symmetric, unused? *)

Scheme statement_ind2 := Induction for statement Sort Prop
  with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme statement_labeled_statements_ind from statement_ind2, labeled_statements_ind2.

Inductive right_cont_injection_find_label_spec j:
  option (statement * cont) -> option (statement * cont) -> Prop :=
| rcifls_Some: forall stmt k1 k2,
    right_cont_injection s j k1 k2 ->
    right_cont_injection_find_label_spec j (Some (stmt, k1)) (Some (stmt, k2))
| rcifls1_None:
  right_cont_injection_find_label_spec j None None
.

Lemma right_cont_injection_find_label_aux: forall j lbl,
  (forall stmt k1 k2
          (RCONTINJ : right_cont_injection s j k1 k2),
     right_cont_injection_find_label_spec j (find_label lbl stmt k1) (find_label lbl stmt k2))
  /\
  (forall sl k1 k2
          (RCONTINJ : right_cont_injection s j k1 k2),
     right_cont_injection_find_label_spec j (find_label_ls lbl sl k1) (find_label_ls lbl sl k2)).
Proof.
  intros j lbl.
  apply statement_labeled_statements_ind;
    simpl; intros; subst;
    eauto using right_cont_injection_find_label_spec.
  - assert (RCONTINJ' := right_cont_injection_kseq _ _ s1 _ _ RCONTINJ).
    specialize (H _ _ RCONTINJ') as [|];
      eauto using right_cont_injection_find_label_spec.
  - specialize (H _ _ RCONTINJ) as [|];
      eauto using right_cont_injection_find_label_spec.
  - assert (RCONTINJ' := right_cont_injection_kloop1 _ _ s0 s1 _ _ RCONTINJ).
    specialize (H _ _ RCONTINJ') as [|];
      eauto using right_cont_injection_find_label_spec, right_cont_injection.
  - assert (RCONTINJ' := right_cont_injection_kswitch _ _ _ _ RCONTINJ).
    specialize (H _ _ RCONTINJ') as [|];
      eauto using right_cont_injection_find_label_spec.
  - destruct (ident_eq lbl l) as [-> |] eqn:IDEQ;
      specialize (H _ _ RCONTINJ) as [|];
      eauto using right_cont_injection_find_label_spec.
  - assert (RCONTINJ' := right_cont_injection_kseq _ _ (seq_of_labeled_statement l) _ _ RCONTINJ).
    specialize (H _ _ RCONTINJ') as [|];
      eauto using right_cont_injection_find_label_spec.
Qed.

Lemma right_cont_injection_find_label:
  forall j stmt lbl k1 k2 stmt' k1'
         (RCONTINJ : right_cont_injection s j k1 k2)
         (LABEL : find_label lbl stmt k1 = Some (stmt', k1')),
  exists k2',
    find_label lbl stmt k2 = Some (stmt', k2') /\
    right_cont_injection s j k1' k2'.
Proof.
  intros.
  destruct (proj1 (right_cont_injection_find_label_aux j lbl) stmt _ _ RCONTINJ);
    [| discriminate].
  injection LABEL as -> ->. eauto.
Qed.

  (* WIP *)
  Definition abstract_step_inj (j: meminj): meminj :=
    j.

  (** Step diagram lemmas *)

  Lemma parallel_concrete: forall j s1 s2 s1' t,
      right_state_injection s j ge1 ge2 s1 s2 ->
      s |= s1 ∈ Right ->
      step1 ge1 s1 t s1' ->
      exists j' s2',
        step1 ge2 s2 t s2' /\
          right_state_injection s j' ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' t rs_inj is_r1 step1.
    destruct rs_inj as [? | st1 st2 _ is_r2 right_exec_inj].
    { (* contradiction *)
      destruct st1; simpl in *; congruence. }
    inv step1; inv right_exec_inj.
    + (* step_assign *)
      rename m into m1. rename m' into m1'.
      rename k into k1. rename e into e1.
      rename le into le1.
      rename a1 into lhs. rename a2 into rhs.
      rename v2 into v1. rename v into v1'.
      rename loc into loc1. rename ofs into ofs1.
      rename H into eval_lhs1.
      rename H0 into eval_rhs1.
      rename H1 into cast_v1.
      rename H2 into ASSIGN.
      assert (f_right : s (comp_of f) = Right) by exact is_r2.
      exploit eval_lvalue_injection; eauto.
      exploit eval_expr_injection; eauto.
      intros [v2 [v1_v2 eval_rhs2]] [loc2 [loc1_ofs [j_loc1 eval_lhs2]]].
      destruct_mem_inj.
      exploit sem_cast_inject; eauto.
      intros [v2' [cast_v2 v1'_v2']].
      exploit delta_zero; eauto. intros ?; subst loc1_ofs.
      rewrite Ptrofs.add_zero in *.
      inv ASSIGN.
      * rename H into ACCESS.
        rename H0 into store_v1'.
        exploit Mem.store_mapped_inject; eauto.
        rewrite Z.add_0_r.
        intros [m2' [store_v2' mem_inject']].
        exists j; eexists; split.
        - econstructor; eauto.
          econstructor; eauto.
        - apply RightControl; eauto.
          constructor; eauto.
          split; eauto.
          ++ unfold same_domain in *.
             intros b. specialize same_dom with b.
             enough (((s, m1') |= b ∈ Right) = ((s, m1) |= b ∈ Right))
               as -> by easy.
             unfold Mem.has_side_block. simpl.
             erewrite Mem.store_block_compartment; eauto.
          ++ unfold same_blocks in *.
             intros b cp b_cp.
             specialize (SAMEBLKS b cp b_cp).
             erewrite Mem.store_block_compartment; eauto.
          ++ unfold same_blocks in *.
             intros b cp b_cp.
             specialize (same_blks3 b cp b_cp).
             erewrite Mem.store_block_compartment; eauto.
      * rename b' into b1'. rename ofs' into ofs1'.
        rename H into ACCESS.
        rename H0 into align_lhs1'.
        rename H1 into align_lhs1.
        rename H2 into sizes1.
        rename H3 into load_b1'.
        rename H4 into store_loc1.
        inv v1'_v2'.
        rename b2 into b2'. rename H1 into j_b1'.
        rename bytes into bytes1.
        exploit delta_zero; try exact j_b1'; eauto. intros ?; subst delta.
        exploit Mem.loadbytes_inj; eauto using Mem.mi_inj.
        rewrite Z.add_0_r.
        intros [bytes2 [load_b2' MVALINJ]].
        exploit Mem.storebytes_mapped_inject; eauto using Mem.mi_inj.
        rewrite Z.add_0_r.
        intros [m2' [store_loc2 mem_inject']].
        exists j; eexists; split.
        - econstructor; eauto.
          rewrite genv_cenv_preserved in *.
          eapply assign_loc_copy; try rewrite Ptrofs.add_zero; eauto.
          { destruct sizes1.
            - exploit injective; eauto. intros []; [now left| contradiction].
            - auto. }
        - apply RightControl; eauto.
          constructor; eauto.
          split; eauto.
          ++ clear -same_dom store_loc1.
             unfold same_domain in *.
             intros b.
             unfold in_side in *; simpl in *.
             erewrite Mem.storebytes_block_compartment; eauto.
             exact (same_dom b).
          ++ eapply same_blocks_storebytes; eauto.
          ++ eapply same_blocks_storebytes; eauto.
      * inv H.
        exploit Mem.load_inject; eauto using Mem.mi_inj.
        intros [? [? ?]].
        exploit Mem.store_mapped_inject; eauto.
        intros [? [? ?]].
        inv H8.
        exploit delta_zero; eauto; intros; subst.
        rewrite Z.add_0_r in *.
        exists j; eexists; split.
        - econstructor; eauto.
          eapply assign_loc_bitfield. rewrite <- H0. inv H4. inv v1'_v2'.
          econstructor; eauto.
        - apply RightControl; eauto.
          constructor; eauto.
          split; eauto.
          ++ clear -same_dom H6.
             unfold same_domain in *.
             intros b.
             unfold in_side in *; simpl in *.
             erewrite Mem.store_block_compartment; eauto.
             exact (same_dom b).
          ++ now constructor.
          ++ eapply same_blocks_store; eauto.
          ++ eapply same_blocks_store; eauto.
    + (* step_set *)
      exploit eval_expr_injection; eauto.
      auto.
      intros [v' [? ?]].
      exists j; eexists; split.
      * econstructor; eauto.
      * apply RightControl; eauto.
        constructor; eauto.
        unfold right_tenv_injection in *.
        intros; rewrite PTree.gsspec in *.
        destruct (peq i id); eauto. inv H2; subst.
        eexists; split; eauto.
    + (* step_call *)
      rename m into m1.
      rename k into k1.
      rename e into e1.
      rename le into le1.
      rename vf into vf1. rename fd into fd1.
      rename vargs into vargs1.
      rename H into a_type.
      rename H0 into eval_a1.
      rename H1 into eval_vargs1.
      rename H2 into find_vf1.
      rename H3 into type_fd1.
      rename ALLOWED into ALLOWED1.
      rename NO_CROSS_PTR into NO_CROSS_PTR1.
      rename EV into EV1.
      assert (Genv.find_comp ge1 vf1 = Some (comp_of fd1)) as comp_vf1.
      { now apply Genv.find_funct_find_comp. }
      exploit eval_expr_injection; eauto; eauto.
      intros [vf2 [vf1_vf2 eval_a2]].
      exploit eval_exprlist_injection; eauto; eauto.
      intros [vargs2 [vargs1_vargs2 eval_vargs2]].
      destruct (s (comp_of fd1)) eqn:s_fd1.
      * (* Next function is on the left *)
        assert (CROSS1 : Genv.allowed_cross_call ge1 (comp_of f) vf1).
        { destruct ALLOWED1 as [CONTRA|CROSS1]; trivial.
          rewrite (Genv.find_funct_find_comp _ _ find_vf1) in CONTRA.
          congruence. }
        destruct (Genv.allowed_cross_call_public_symbol
                    _ _ _ CROSS1)
          as (id & b1 & off1 & evf1 & ge1_id & pub_id1).
        assert (off1 = Ptrofs.zero /\ Genv.find_def ge1 b1 = Some (Gfun fd1))
          as [-> find_vf1'].
        { rewrite evf1 in find_vf1. simpl in find_vf1.
          destruct Ptrofs.eq_dec as [->|_]; try easy.
          split; trivial.
          unfold Genv.find_funct_ptr in find_vf1.
          unfold ge1. simpl.
          destruct (Genv.find_def _ b1) as [def1|]; try easy.
          destruct def1 as [fd1'|?]; try easy.
          now injection find_vf1 as ->. }
        exploit (@match_prog_globdefs _ _ _ match_W1_W2 id (comp_of fd1)); eauto.
        { left.
          unfold Genv.find_comp_of_ident.
          rewrite ge1_id.
          unfold Genv.find_comp_of_block. now rewrite find_vf1'. }
        intros (b1' & b2 & ge1_id' & ge2_id & match_fd).
        assert (b1' = b1) as -> by congruence. clear ge1_id'.
        rewrite find_vf1', s_fd1 in match_fd.
        simpl in match_fd.
        assert (exists def2,
                   Genv.find_def ge2 b2 = Some def2 /\
                     match_globdef (Gfun fd1) def2)
          as (def2 & ge2_b2 & match_fd').
        { inv match_fd. eauto. }
        assert (exists fd2,
                   def2 = Gfun fd2 /\
                   match_fundef tt fd1 fd2)
          as (fd2 & -> & match_fd'').
        { inv match_fd'. eauto. }
        assert (vf2 = Vptr b2 Ptrofs.zero) as evf2.
        { exploit same_symb; eauto. intros (_ & _ & INJ & _).
          destruct (INJ _ _ pub_id1 ge1_id) as (b2' & j_b1 & ge2_id').
          assert (b2' = b2) as -> by (simpl in *; congruence).
          inv vf1_vf2; try congruence.
          match goal with
          | [ _ : j b1 = Some (b2, 0),
              H1 : j ?b1' = Some (?b2', ?delta),
              H2 : Vptr _ ?ofs1 = Vptr b1 _ |- _ ]
            => assert (b1' = b1) as -> by congruence;
               assert (ofs1 = Ptrofs.zero) as -> by congruence;
               assert (b2' = b2) as -> by congruence;
               assert (delta = 0) as -> by congruence;
               clear H1 H2
          end.
          now rewrite Ptrofs.add_zero. }
        assert (Genv.find_funct ge2 vf2 = Some fd2) as find_vf2'.
        { unfold Genv.find_funct, Genv.find_funct_ptr. rewrite evf2.
          destruct Ptrofs.eq_dec as [_|?]; try congruence.
          now rewrite ge2_b2. }
        assert (type_of_fundef fd2 = Tfunction tyargs tyres cconv)
          as type_fd2.
        { inv match_fd''; eauto. }
        assert (Genv.allowed_call ge2 (comp_of f) vf2) as ALLOWED2.
        { eapply allowed_call_preserved; eauto.
        (*   right. rewrite evf2. simpl. exists id, (comp_of fd2). *)
        (*   split. *)
        (*   { now apply Genv.find_invert_symbol. } *)
        (*   (* unfold Genv.find_comp. rewrite <- evf2. unfold ge2 in find_vf2'. *) *)
        (*   (* simpl in find_vf2'. rewrite find_vf2'. split; trivial. *) *)
        (*   admit. *)
        }

        assert (COMP_fd1_fd2: comp_of fd1 = comp_of fd2)
              by (inv match_fd''; auto).
        exists j, (Callstate fd2 vargs2 (Kcall optid f e2 le2 k2) m2).
        (*  This proof is nearly identical to the sub-case immediately below *)
        split.
        { econstructor; eauto.
          - rewrite <- COMP_fd1_fd2. intros CROSS. specialize (NO_CROSS_PTR1 CROSS).
            eapply inject_list_not_ptr; eauto.
          - rewrite <- COMP_fd1_fd2.
            inv EV1.
            + apply call_trace_intra. assumption.
            + inv vf1_vf2.
              eapply call_trace_cross.
              * assumption.
              * reflexivity.
              * injection H0 as <- <-.
                apply Genv.find_invert_symbol.
                apply Genv.invert_find_symbol in H1.
                eapply right_mem_injection_find_symbol; eauto.
              * eapply right_mem_injection_list_match; eauto. }
        { apply LeftControl.
          - assumption.
          - simpl. rewrite <- COMP_fd1_fd2. assumption.
          - assumption.
          - simpl. rewrite is_r1.
            now apply right_cont_injection_kcall_right. }
      * rename fd1 into fd.
        rename type_fd1 into type_fd.
        (* rewrite comp_vf1 in *. *)
        exploit find_funct_preserved; eauto.
        { eapply same_symb; eauto. }
        intros find_vf2.
        (* assert (Genv.find_comp ge2 vf2 = comp_of fd) as comp_vf2. *)
        (* { unfold Genv.find_comp. now rewrite find_vf2. } *)
        assert (Genv.allowed_call ge2 (comp_of f) vf2) as ALLOWED2.
        { eapply allowed_call_preserved; eauto. }
        exists j.
        exists (Callstate fd vargs2 (Kcall optid f e2 le2 k2) m2).
        split.
        { econstructor; eauto.
          - intros CROSS. specialize (NO_CROSS_PTR1 CROSS).
            eapply inject_list_not_ptr; eauto.
          - inv EV1.
            + apply call_trace_intra. assumption.
            + inv vf1_vf2.
              eapply call_trace_cross.
              * assumption.
              * reflexivity.
              * apply Genv.find_invert_symbol.
                apply Genv.invert_find_symbol in H1.
                eapply right_mem_injection_find_symbol; eauto.
              * eapply right_mem_injection_list_match; eauto. }
        apply RightControl; trivial.
        constructor; trivial.
        now apply right_cont_injection_kcall_right.
      (* Stopped here... *)
      (* assert (vf = v') by admit. subst v'. *)
      (* exists j; eexists; split. *)
      (* * econstructor; eauto. *)
      (*   - inv match_fd'; eauto. *)
      (*   - exploit (Genv.match_genvs_allowed_calls match_W1_W2); eauto. *)
      (*   - eapply (Genv.match_genvs_not_ptr_list_inj); eauto. *)
      (*     exploit (Genv.match_genvs_find_comp match_W1_W2); eauto. intros <-. *)
      (*     erewrite <- (Genv.match_genvs_type_of_call); eauto. *)
      (*   - exploit (Genv.match_genvs_find_comp match_W1_W2); eauto. intros <-. *)
      (*     exploit (@call_trace_inj _ _ _ _ ge1 ge2); eauto. *)
      (*     simpl. apply Genv.globalenvs_match in match_W1_W2. *)
      (*     intros sy. pose proof (Genv.mge_symb match_W1_W2 sy). unfold Genv.find_symbol; eauto. *)
      (* * (* Case analysis: are we changing side or not? *) *)
      (*   destruct (s (comp_of fd)) eqn:side. *)
      (*   - apply LeftControl; eauto; try now inv match_fd'; auto. *)
      (*     simpl. apply right_cont_injection_kcall_right; eauto. *)
      (*   - inv match_fd'; unfold in_side in *; simpl in *; *)
      (*       unfold comp_of in *; simpl in side; unfold comp_of in *; simpl in side; *)
      (*       try congruence. *)
      (*     apply RightControl; eauto. *)
      (*     constructor; eauto. *)
      (*     simpl. apply right_cont_injection_kcall_right; eauto. *)
    + (* step_builtin *)
      (* prefix *)
      exploit eval_exprlist_injection; eauto.
      auto.
      intros [vs' [? ?]].
      (* same as step_external_function *)
      destruct (right_mem_injection_external_call RMEMINJ H0 H1)
        as (j' & m2' & vres' & EXTCALL' & RMEMINJ' & INCR & RESINJ).
      exists j'; eexists; split.
      econstructor; eauto.
      apply RightControl; eauto.
      constructor; eauto.
      (* suffix *)
      * eapply right_cont_injection_inject_incr; eauto.
      * destruct RENVINJ as [RENVINJ_SOME RENVINJ_NONE].
        split.
        { intros ? ? ? ?.
          exploit RENVINJ_SOME; eauto. intros [b' [? ?]].
          exists b'; split; eauto. }
        { intros ? ?.
          specialize (RENVINJ_NONE _ H3); eauto. }
      * intros ? ? ?.
        destruct optid.
        - simpl in *. rewrite PTree.gsspec in *.
          destruct (peq i i0); subst.
          { inv H3. eexists; split; eauto. }
          { specialize (RTENVINJ _ _ H3) as [? [? ?]]; eauto. }
        - specialize (RTENVINJ _ _ H3) as [? [? ?]]; eauto.
    + (* step_seq*)
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto. constructor; auto.
    + (* step_skip_seq *)
      inv RCONTINJ.
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_continue_seq *)
      inv RCONTINJ.
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_break_seq *)
      inv RCONTINJ.
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_ifthenelse *)
      exploit eval_expr_injection; simpl in is_r1; eauto.
      intros [v' [? ?]].
      destruct_mem_inj.
      exploit bool_val_inject; eauto. intros ?.
      exists j; eexists; split; [econstructor | apply RightControl]; eauto.
      constructor; auto. constructor; auto.
    + (* step_loop *)
      exists j; eexists; split; [econstructor | apply RightControl]; eauto.
      constructor; auto. constructor; auto.
    + (* step_skip_or_continue_loop1 *)
      inv RCONTINJ. exists j; eexists; split; [constructor | apply RightControl]; eauto.
      constructor; auto. constructor; auto.
    + (* step_break_loop1 *)
      inv RCONTINJ. exists j; eexists; split; [apply step_break_loop1 | apply RightControl]; eauto.
      constructor; auto.
    + (* step_skip_loop2 *)
      inv RCONTINJ. exists j; eexists; split; [apply step_skip_loop2 | apply RightControl]; eauto.
      constructor; auto.
    + (* step_break_loop2 *)
      inv RCONTINJ. exists j; eexists; split; [apply step_break_loop2 | apply RightControl]; eauto.
      constructor; auto.
    + (* step_return_0 *)
      destruct (right_mem_injection_free_list RMEMINJ RENVINJ H is_r1) as (m2' & FREE' & RMEMINJ').
      inv RMEMINJ. exists j; eexists; split; [apply step_return_0 | apply RightControl]; eauto.
      constructor; auto.
      apply right_cont_injection_call_cont; auto.
    + (* step_return_1 *)
      destruct (right_mem_injection_free_list RMEMINJ RENVINJ H1 is_r1) as (m2' & FREE' & RMEMINJ').
      exploit eval_expr_injection;
        try eapply RMEMINJ; (* pick right injection *)
        simpl in is_r1; eauto. intros (v2 & VINJ2 & EVAL2).
      exploit sem_cast_inject; eauto; [inv RMEMINJ; eauto |]. intros (v2' & CAST2' & VINJ2').
      exists j. eexists. split.
      * eapply step_return_1; eauto.
      * apply RightControl; auto.
        constructor; auto.
        apply right_cont_injection_call_cont; auto.
    + (* step_skip_call *)
      destruct (right_mem_injection_free_list RMEMINJ RENVINJ H0 is_r1) as (m2' & FREE' & RMEMINJ').
      exists j. eexists. split.
      { apply step_skip_call; eauto.
        destruct k; try contradiction H;
          inv RCONTINJ; reflexivity. }
      apply RightControl; auto.
      constructor; auto.
    + (* step_switch *)
      exploit eval_expr_injection; simpl in is_r1; eauto.
      intros [v' [? ?]].
      assert (sem_switch_arg v (typeof a) = Some n -> sem_switch_arg v' (typeof a) = Some n).
      { intros. unfold sem_switch_arg in *.
        destruct (classify_switch (typeof a)); simpl in *; try easy; inv H1; try easy. }
      exists j; eexists; split; [econstructor | apply RightControl]; eauto.
      constructor; auto.
      constructor; auto.
    + (* step_break_switch *)
      inv RCONTINJ. exists j; eexists; split; [constructor | apply RightControl]; eauto.
      constructor; auto.
    + (* step_continue_switch *)
      inv RCONTINJ. exists j; eexists; split; [apply step_continue_switch | apply RightControl]; eauto.
      constructor; auto.
    + (* step_label *)
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_goto *)
      assert (exists k2',
                 find_label lbl (fn_body f) (call_cont k2) = Some (s', k2') /\
                 right_cont_injection s j k' k2')
        as (k2' & LABEL & RCONTINJ'). {
        clear -H RCONTINJ.
        eapply right_cont_injection_find_label; eauto.
        apply right_cont_injection_call_cont; auto.
      }
      exists j; eexists; split; [constructor | apply RightControl]; eauto.
      constructor; auto.
    + (* step_internal_function *)
      destruct (right_mem_injection_function_entry1 RMEMINJ ARGINJ is_r1 H)
        as (j' & e2 & le2 & m2' & ENTRY' & INCR & RMEMINJ' & RENVINJ' & RTENVINJ').
      exists j'. eexists. split.
      { apply step_internal_function; eauto. }
      { apply RightControl; auto.
        constructor; auto.
        { eapply right_cont_injection_inject_incr; eauto. }
        inv H. inv ENTRY'. apply right_tenv_injection_create_undef_temps. }
      (* { (* Factor out lemma *) (* see original instance below *) *)
      (*   inversion H. inversion ENTRY'. *)
      (*   inv partial_mem_inject0. constructor. *)
      (*   - { *)
      (*     inv mi_inj. constructor. *)
      (*     - intros b1 b2 delta ofs' k' p' b1_b2 PERM. *)
      (*       assert (VALID: Mem.valid_block m b1). { (* extract lemma *) *)
      (*         destruct (plt b1 (Mem.nextblock m)) as [LT | GE]; *)
      (*           [exact LT |]. *)
      (*         specialize (mi_freeblocks _ GE). *)
      (*         congruence. } *)
      (*       specialize (mi_perm b1 b2 delta ofs' k' p' b1_b2). *)
      (*       apply (bind_parameters_perm_2 H2) in PERM. *)
      (*       apply (alloc_variables_perm_2 H1) in PERM; auto. *)
      (*       (* new sub-proof *) *)
      (*       specialize (mi_perm PERM). *)
      (*       apply (alloc_variables_perm_1 H1) in mi_perm. *)
      (*       apply (bind_parameters_perm_1 H6) in mi_perm. *)
      (*       exact mi_perm. *)
      (*     - intros b1 b2 delta cp b1_b2 ACC. *)
      (*       assert (VALID: Mem.valid_block m b1). { (* extract lemma *) *)
      (*         destruct (plt b1 (Mem.nextblock m)) as [LT | GE]; *)
      (*           [exact LT |]. *)
      (*         specialize (mi_freeblocks _ GE). *)
      (*         congruence. } *)
      (*       specialize (mi_own b1 b2 delta cp b1_b2). *)
      (*       (* apply mi_own. *) *)
      (*       apply (bind_parameters_can_access_block_2 H2) in ACC. *)
      (*       apply (alloc_variables_can_access_block_2 H1) in ACC; auto. *)
      (*       (* new sub-proof *) *)
      (*       specialize (mi_own ACC). *)
      (*       apply (alloc_variables_can_access_block_1 H5) in mi_own. *)
      (*       apply (bind_parameters_can_access_block_1 H6) in mi_own. *)
      (*       exact mi_own. *)
      (*     - intros b1 b2 delta chunk ofs p b1_b2 PERM. *)
      (*       assert (VALID: Mem.valid_block m b1). { (* extract lemma *) *)
      (*         destruct (plt b1 (Mem.nextblock m)) as [LT | GE]; *)
      (*           [exact LT |]. *)
      (*         specialize (mi_freeblocks _ GE). *)
      (*         congruence. } *)
      (*       specialize (mi_align b1 b2 delta chunk ofs p b1_b2). apply mi_align. *)
      (*       apply (bind_parameters_range_perm_2 H2) in PERM. *)
      (*       apply (alloc_variables_range_perm_2 H1) in PERM; eauto. *)
      (*     - intros b1 ofs b2 delta b1_b2 PERM. *)
      (*       assert (VALID: Mem.valid_block m b1). { (* extract lemma *) *)
      (*         destruct (plt b1 (Mem.nextblock m)) as [LT | GE]; *)
      (*           [exact LT |]. *)
      (*         specialize (mi_freeblocks _ GE). *)
      (*         congruence. } *)
      (*       (* easy: [b1] is already present in [m] and consequently its *)
      (*          contents are not affected by either [alloc_variables] or *)
      (*          [bind_parameters] *) *)
      (*       apply (bind_parameters_perm_2 H2) in PERM. *)
      (*       apply (alloc_variables_perm_2 H1) in PERM; auto. *)
      (*       specialize (mi_memval b1 ofs b2 delta b1_b2 PERM). *)
      (*       simpl. simpl in mi_memval. *)
      (*       admit. (* easy, see above *) (* document proof variant *) *)
      (*     } *)
      (*   - intros b VALID. specialize (mi_freeblocks b). *)
      (*     apply mi_freeblocks. intros CONTRA. apply VALID. *)
      (*     simpl in *. *)
      (*     eapply bind_parameters_valid_block_1; eauto. *)
      (*     eapply alloc_variables_valid_block_1; eauto. *)
      (*   - (* new sub-case *) *)
      (*     intros b b' delta b_b'. specialize (mi_mappedblocks b b' delta b_b'). *)
      (*     eapply bind_parameters_valid_block_1; eauto. *)
      (*     eapply alloc_variables_valid_block_1; eauto. *)
      (*   - intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 b1_b1' b2_b2' PERM1 PERM2. *)
      (*     specialize (mi_no_overlap *)
      (*                   b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 b1_b1' b2_b2'). *)
      (*     assert (VALID1: Mem.valid_block m b1). { (* extract lemma *) *)
      (*       destruct (plt b1 (Mem.nextblock m)) as [LT | GE]; *)
      (*         [exact LT |]. *)
      (*       specialize (mi_freeblocks _ GE). *)
      (*       congruence. } *)
      (*     assert (VALID2: Mem.valid_block m b2). { (* extract lemma *) *)
      (*       destruct (plt b2 (Mem.nextblock m)) as [LT | GE]; *)
      (*         [exact LT |]. *)
      (*       specialize (mi_freeblocks _ GE). *)
      (*       congruence. } *)
      (*     apply (bind_parameters_perm_2 H2) in PERM1, PERM2. *)
      (*     apply (alloc_variables_perm_2 H1) in PERM1, PERM2; eauto. *)
      (*   - intros b b' delta ofs b_b' PERM. *)
      (*     specialize (mi_representable b b' delta ofs b_b'). *)
      (*     apply mi_representable. *)
      (*     destruct PERM as [PERM | PERM]. *)
      (*     + left. *)
      (*       assert (VALID: Mem.valid_block m b). { (* extract lemma *) *)
      (*         destruct (plt b (Mem.nextblock m)) as [LT | GE]; *)
      (*           [exact LT |]. *)
      (*         specialize (mi_freeblocks _ GE). *)
      (*         congruence. } *)
      (*       apply (alloc_variables_perm_2 H1); eauto. *)
      (*       apply (bind_parameters_perm_2 H2); eauto. *)
      (*     + right. *)
      (*       (* exactly the same script as the previous case *) *)
      (*       assert (VALID: Mem.valid_block m b). { (* extract lemma *) *)
      (*         destruct (plt b (Mem.nextblock m)) as [LT | GE]; *)
      (*           [exact LT |]. *)
      (*         specialize (mi_freeblocks _ GE). *)
      (*         congruence. } *)
      (*       apply (alloc_variables_perm_2 H1); eauto. *)
      (*       apply (bind_parameters_perm_2 H2); eauto. *)
      (*   - intros b1 ofs b2 delta k' p' b1_b2 PERM. *)
      (*     (* early sub-proof changes *) *)
      (*     specialize (mi_perm_inv b1 ofs b2 delta k' p' b1_b2). *)
      (*     assert (VALID':  Mem.valid_block m2 b2). { *)
      (*       exact (mi_mappedblocks _ _ _ b1_b2). } *)
      (*     apply (bind_parameters_perm_2 H6) in PERM. *)
      (*     apply (alloc_variables_perm_2 H5) in PERM; auto. *)
      (*     (* former proof resumes *) *)
      (*     specialize (mi_perm_inv PERM) *)
      (*       as [PERM' | PERM']. *)
      (*     + left. *)
      (*       eapply bind_parameters_perm_1; eauto. *)
      (*       eapply alloc_variables_perm_1; eauto. *)
      (*     + right. intros CONTRA. apply PERM'. *)
      (*       (* see cases above *) *)
      (*       assert (VALID: Mem.valid_block m b1). { (* extract lemma *) *)
      (*         destruct (plt b1 (Mem.nextblock m)) as [LT | GE]; *)
      (*           [exact LT |]. *)
      (*         specialize (mi_freeblocks _ GE). *)
      (*         congruence. } *)
      (*       apply (alloc_variables_perm_2 H1); eauto. *)
      (*       apply (bind_parameters_perm_2 H2); eauto. *)
      (* } *)
      (*     + eapply same_blocks_function_entry1; eauto. *)
      (*     + eapply same_blocks_function_entry1; eauto. *)
      (* } *)
    + (* step_external_function *)
      (* very similar to step_builtin *)
      destruct (right_mem_injection_external_call RMEMINJ H ARGINJ)
        as (j' & m2' & vres' & EXTCALL' & RMEMINJ' & INCR & RESINJ).
      exists j'; eexists; split.
      econstructor; eauto.
      apply RightControl; eauto.
      constructor; eauto.
      { eapply right_cont_injection_inject_incr; eauto. }
    + (* step_returnstate *)
      inv RCONTINJ.
      * (* assert (COMP: comp_of f = comp_of f2) by admit. (* need to know this at least *) *)
        (* rewrite COMP in *. *)
        exists j. eexists. split.
        { apply step_returnstate.
          - intros CALLTYPE. specialize (NO_CROSS_PTR CALLTYPE).
            destruct v; try contradiction; inv RVALINJ; reflexivity.
          - inv EV.
            + apply return_trace_intra; auto.
            + apply return_trace_cross; auto.
              specialize (NO_CROSS_PTR H).
              destruct v; try contradiction; inv RVALINJ; inv H0; constructor.
        }
        { apply LeftControl; auto.
          (* simpl. admit. *)
        }
      * (* assert (f = f2) as <- by admit. (* here the injection needs more *) *)
        exists j. eexists. split.
        { apply step_returnstate.
          - intros CALLTYPE. specialize (NO_CROSS_PTR CALLTYPE).
            destruct v; try contradiction; inv RVALINJ; reflexivity.
          - inv EV.
            + apply return_trace_intra; auto.
            + apply return_trace_cross; auto.
              specialize (NO_CROSS_PTR H).
              destruct v; try contradiction; inv RVALINJ; inv H0; constructor.
        }
        { apply RightControl; auto.
          constructor; auto.
          { destruct optid as [id |];
              [| assumption].
            simpl. intros id' v'' GET.
            destruct (peq id' id) as [-> | NEQ].
            - rewrite PTree.gss.
              rewrite PTree.gss in GET. injection GET as <-.
              eauto.
            - rewrite PTree.gso; [| assumption].
              rewrite PTree.gso in GET; [| assumption].
              eauto. }
        }
  Qed.

    (* Example that shows why Blame doesn't hold in the C semantics.
       Because the semantics are not determinate we can end up in situation like this one:


    int f();
    int x;

    int main() {
      int a[2];
      a[0] = (x = 0) + f();
      if x { a[5] = 42; }
      else { }
    }

    (* 2 executions *)
    (* We know that f(y) produces the same trace. Can the value of x change? *)
    (* Let's say f() does x = 1 - x *)

    (* execution 1: assignment first: x = 1 we take the if branch *)
    (* execution 2: call first:       x = 0 we take the else branch *)
    *)

  Lemma parallel_concrete_E0: forall j s1 s2 s1' s2' t,
    right_state_injection s j ge1 ge2 s1 s2 ->
    s |= s1 ∈ Right -> (* in the context *)
    step1 ge1 s1 E0 s1' ->
    step1 ge2 s2 t s2' ->
  exists j',
    t = E0 /\ right_state_injection s j' ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' s2' t INJ RIGHT STEP1 STEP2.
    exploit parallel_concrete; eauto.
    intros [j' [s2'' [STEP2' INJ']]].
    destruct t as [| e [| e' t]].
    - destruct (step1_E0_determ STEP2 STEP2').
      eauto.
    - exfalso. eapply step1_E0_event_False; eassumption.
    - apply (sr_traces (semantics_receptive _)) in STEP2.
      inv STEP2. inv H0.
  Qed.

  (* Can get rid of uses of this? *)
  Lemma parallel_concrete_E0': forall j s1 s2 s1' s2' t,
    right_state_injection s j ge1 ge2 s1 s2 ->
    s |= s1 ∈ Right -> (* in the context *)
    step1 ge2 s2 E0 s2' ->
    step1 ge1 s1 t s1' ->
  exists j',
    t = E0 /\ right_state_injection s j' ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' s2' t INJ RIGHT STEP1 STEP2.
    exploit parallel_concrete; eauto.
    intros [j' [s2'' [STEP2' INJ']]].
    destruct t as [| e [| e' t]].
    - destruct (step1_E0_determ STEP1 STEP2').
      eauto.
    - exfalso. eapply step1_E0_event_False; eassumption.
    - apply (sr_traces (semantics_receptive _)) in STEP2.
      inv STEP2. inv H0.
  Qed.

  Lemma parallel_abstract_E0_1: forall j s1 s2 s1',
    right_state_injection s j ge1 ge2 s1 s2 ->
    s |= s1 ∈ Left ->
    step1 ge1 s1 E0 s1' ->
  exists j',
    right_state_injection s j' ge1 ge2 s1' s2.
  Proof.
    intros j s1 s2 s1' INJ LEFT STEP.
    inversion INJ as [? ? SIDE1 SIDE2 MEMINJ CONTINJ |]; subst; clear INJ;
      [| exfalso; eapply state_split_contra; eassumption].
    apply (step_E0_same_side STEP) in LEFT.
    exploit right_mem_injection_left_step_E0_1; eauto.
    intros (j' & MEMINJ' & INCR).
    exploit right_cont_injection_left_step_E0_1; eauto.
    intros CONTINJ'.
    exists j'.
    constructor; try assumption.
    eapply right_cont_injection_inject_incr; eauto.
  Qed.

  Lemma parallel_abstract_E0_2: forall j s1 s2 s2',
    right_state_injection s j ge1 ge2 s1 s2 ->
    s |= s1 ∈ Left ->
    step1 ge2 s2 E0 s2' ->
  exists j',
    right_state_injection s j' ge1 ge2 s1 s2'.
  Admitted. (* Symmetric *)

  (* NOTE: Currently unused by proofs below (useful for E0 star?) *)
  (* Lemma parallel_abstract_E0: forall j s1 s2 s1' s2', *)
  (*   right_state_injection s j ge1 ge2 s1 s2 -> *)
  (*   s |= s1 ∈ Left -> *)
  (*   step1 ge1 s1 E0 s1' -> *)
  (*   step1 ge2 s2 E0 s2' -> *)
  (*   right_state_injection s j ge1 ge2 s1' s2'. *)
  (* Proof. *)
  (*   intros s1 s2 s1' t rs_inj is_l step1. *)
  (*   (* inv rs_inj. *) *)
  (*   (* - admit. *) *)
  (*   (* - admit. (* contradiction *) *) *)
  (*   admit. *)
  (* Admitted. *)

  Lemma parallel_abstract_ev: forall j s1 s2 s1' s2' e,
    right_state_injection s j ge1 ge2 s1 s2 ->
    s |= s1 ∈ Left ->
    step1 ge1 s1 (e :: nil) s1' ->
    step1 ge2 s2 (e :: nil) s2' ->
  exists j',
    right_state_injection s j' ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' s2' e INJ LEFT STEP1 STEP2.
    inv STEP1.
    - (* step_call *)
      inv EV. inv STEP2.
      + (* matching case *)
        inv EV.
        simpl in H2. destruct Ptrofs.eq_dec; [| discriminate]. subst ofs.
        simpl in H9. destruct Ptrofs.eq_dec; [| discriminate]. subst ofs0.
        inv INJ; [| congruence].
        destruct (state_split_decidable (Callstate fd vargs (Kcall optid f e0 le k) m))
          as [LEFT' | RIGHT'].
        * exists j. apply LeftControl.
          -- assumption.
          -- congruence.
          -- assumption.
          -- simpl. rewrite H14, H15. assumption.
        * exists j. apply RightControl.
          -- assumption.
          -- congruence.
          -- assert (fd = fd0) as <-. {
               admit. }
             apply inject_callstates.
             ++ assumption.
             ++ (* apply right_cont_injection_kcall_left; try assumption. *)
                admit.
             ++ specialize (NO_CROSS_PTR H5).
                specialize (NO_CROSS_PTR0 H21).
                admit. (* easy *)
      + destruct (ec_no_crossing (external_call_spec ef) _ _ _ _ _ _ H6).
      + destruct (ec_no_crossing (external_call_spec ef) _ _ _ _ _ _ H4).
      + inv EV.
    - (* step_builtin *)
      inv INJ; [| congruence]. inv STEP2.
      + admit.
      + (* matching case *) admit.
      + admit.
      + admit.
        (* inv EV. simpl in *. inv H4. *)
        (* * admit. *)
        (* * admit. *)
    - (* step_external_function *)
      inv INJ; [| congruence]. inv STEP2.
      + inv EV. admit. (* contra? *)
      + admit. (* contra? *)
      + (* matching case *)
        simpl in *.
        assert (ARGS: Val.inject_list j vargs vargs0) by admit.
        destruct (external_call_spec ef).
        specialize (ec_mem_inject _ _ _ _ _ _ _ _ _ _
                      (same_symb _ _ _ _ _ _ H2) H
                      (partial_mem_inject _ _ _ _ _ _ H2) ARGS)
          as (j' & vres' & m2' & EXT & VINJ & MINJ & MAPPED & REACH & INCR & SEP & BLOCKS).
        exists j'. apply LeftControl; try assumption.
        assert (vres0 = vres' /\ m'0 = m2') as [<- <-]. {
          (* Assuming [ef0] corresponds to the original [ef], we can
             use [external_call_deterministic] to yield this. *)
          admit.
        }
        constructor.
        * destruct H2 as [DOM _ _ _ _ _ _].
          admit. (* see comments *)
        * exact MINJ.
        * destruct H2 as [_ _ DELTA _ _ _ _].
          admit. (* should follow from the properties of external calls, like INCR *)
        * destruct H2 as [_ _ _ (SINJ1 & SINJ2 & SINJ3 & SINJ4) _ _ _]. simpl.
          split; [assumption |].
          split.
          { (* external calls don't modify the global environment, so any mapped block
               after the call should also be mapped before the call, making the property
               invariant *)
            intros id b1 b2 delta b1_b2 FIND. specialize (SINJ2 id b1 b2 delta).
            apply SINJ2; [| assumption].
            admit. }
          split.
          { intros id b1 PUB FIND.
            specialize (SINJ3 id b1 PUB FIND) as (b2 & b1_b2 & FIND').
            exists b2. split; [| assumption].
            apply INCR. assumption. }
          { (* volatile global variables aren't modifed by external calls, so new
               mappings to those shouldn't be added, making the property invariant *)
            intros b1 b2 delta b1_b2. admit. }
        * destruct H2 as [_ MEMINJ _ _ INJ _ _].
          intros b1 b2 b1' b2' ofs1 ofs2 NEQ b1_b1' b2_b2'.
          specialize (INJ b1 b2 b1' b2' ofs1 ofs2 NEQ).
          destruct (j b1) as [[b1'' ofs1']|] eqn:b1_b1''.
          -- rewrite (INCR _ _ _ b1_b1'') in b1_b1'. injection b1_b1' as -> ->.
             destruct (j b2) as [[b2'' ofs2']|] eqn:b2_b2''.
             ++ rewrite (INCR _ _ _ b2_b2'') in b2_b2'. injection b2_b2' as -> ->.
                apply INJ; reflexivity.
             ++ destruct (SEP _ _ _ b2_b2'' b2_b2') as [m_b2 m0_b2'].
                assert (m'_b2: Mem.valid_block m' b2). {
                  destruct (plt b2 (Mem.nextblock m')) as [LT | GE];
                    [exact LT |].
                  rewrite (Mem.mi_freeblocks _ _ _ MINJ _ GE) in b2_b2'.
                  discriminate. }
                assert (m'0_b2' := Mem.mi_mappedblocks _ _ _ MINJ _ _ _ b2_b2').
                Check b1_b1''.
                Check b2_b2''.
                (* - [b2] is not valid in [m] (before the external call) but
                     it is valid in [m'] (after the call)
                   - same for [b2'] between [m0] and [m'0] *)
                clear ec_well_typed ec_max_perm ec_symbols_preserved ec_valid_block ec_can_access_block ec_readonly ec_trace_length ec_receptive ec_determ ec_no_crossing.
                Check Mem.mi_mappedblocks _ _ _ MEMINJ _ _ _ b1_b1''.
                Check BLOCKS _ m_b2 m'_b2.
                Check INCR _ _ _ b1_b1''.
                admit.
          -- destruct (SEP _ _ _ b1_b1'' b1_b1') as [m_b1 m0_b1'].
             destruct (j b2) as [[b2'' ofs2']|] eqn:b2_b2''.
             ++ rewrite (INCR _ _ _ b2_b2'') in b2_b2'. injection b2_b2' as -> ->.
                admit.
             ++ destruct (SEP _ _ _ b2_b2'' b2_b2') as [m_b2 m0_b2'].
                admit.
        * destruct H2 as [_ _ _ _ _ SAME _]. simpl.
          intros b cp' FIND. specialize (SAME b cp' FIND).
          change (Mem.block_compartment m b = Some cp')
            with (Mem.can_access_block m b (Some cp')) in SAME.
          exact (external_call_can_access_block _ _ _ _ _ _ _ _ _ H SAME).
        * destruct H2 as [_ _ _ _ _ _ SAME]. simpl.
          intros b cp' FIND. specialize (SAME b cp' FIND).
          change (Mem.block_compartment m0 b = Some cp')
            with (Mem.can_access_block m0 b (Some cp')) in SAME.
          exact (external_call_can_access_block _ _ _ _ _ _ _ _ _ H4 SAME).
        * eapply right_cont_injection_inject_incr; eauto.
      + inv EV. admit.  (* contra? *)
    - (* step_returnstate *)
      inv EV. inv STEP2.
      + inv EV.
      + destruct (ec_no_crossing (external_call_spec ef) _ _ _ _ _ _ H1).
      + destruct (ec_no_crossing (external_call_spec ef) _ _ _ _ _ _ H).
      + (* matching case *)
        inv EV.
        inv INJ; [| congruence].
        simpl in *.
        destruct (state_split_decidable (State f Sskip k e0 (set_opttemp optid v le) m))
          as [LEFT' | RIGHT'].
        * exists j. apply LeftControl.
          -- assumption.
          -- congruence.
          -- assumption.
          -- rewrite H, LEFT' in H4. assumption.
        * exists j. apply RightControl.
          -- assumption.
          -- congruence.
          -- assert (f = f0) as <-. {
               admit. }
             apply inject_states.
             ++ assumption.
             ++ rewrite RIGHT' in H4. inv H4.
                ** congruence.
                ** assumption.
             ++ admit. (* right_env_injection *)
             ++ admit. (* right_tenv_injection *)
  Admitted.

  Lemma parallel_abstract_t: forall j s1 s2 s1' s2' t,
    right_state_injection s j ge1 ge2 s1 s2 ->
    s |= s1 ∈ Left ->
    step1 ge1 s1 t s1' ->
    step1 ge2 s2 t s2' ->
  exists j',
    right_state_injection s j' ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' s2' t RINJ LEFT STEP1 STEP2.
    destruct t as [| e1 [| e2 t]].
    - destruct (parallel_abstract_E0_1 _ _ _ _ RINJ LEFT STEP1) as [j' RINJ'].
      apply (step_E0_same_side STEP1) in LEFT.
      destruct (parallel_abstract_E0_2 _ _ _ _ RINJ' LEFT STEP2) as [j'' RINJ''].
      exists j''. assumption.
    - eapply parallel_abstract_ev; eauto.
    - assert (CONTRA := sr_traces (semantics_receptive _) _ _ _ STEP1).
      inv CONTRA. inv H0.
  Qed.

(* Lemma parallel_concrete p1 p2 scs1 scs2: *)
(*   left_side s p1 -> (* use definitions from RSC.v *) *)
(*   left_side s p2 -> (* use definitions from RSC.v *) *)
(*   partial_state_equivalent s scs1 scs2 -> (* to define --> using memory injections? *) *)
(*   pc_in_left_part scs1 -> (* to define *) *)
(*   CS.kstep (prepare_global_env (program_link p p1)) scs1 t scs1' -> (* use step of Csem instead *) *)
(*   exists2 scs2', *)
(*     CS.kstep (prepare_global_env (program_link p p2)) scs2 t scs2' /\ (* use step of Csem instead *) *)
(*       partial_state_equivalent s scs1' scs2'. (* to define *) *)

Definition comp_of_event_or_default (e: event) (cp: compartment) :=
  match e with
  | Event_syscall _ _ _ => cp
  | Event_vload _ _ _ _ => cp
  | Event_vstore _ _ _ _ => cp
  | Event_annot _ _ => cp
  | Event_call _ cp' _ _ => cp'
  | Event_return _ cp' _ => cp'
  end.

Fixpoint last_comp_in_trace' (t: trace) (cp: compartment): compartment :=
  match t with
  | nil => cp
  | e :: t' => last_comp_in_trace' t' (comp_of_event_or_default e cp)
  end.

Definition last_comp_in_trace (t: trace): compartment :=
  last_comp_in_trace' t default_compartment.

Definition blame_on_program (t: trace) :=
  s (last_comp_in_trace t) = Left.

(** Traces and prefixes *)

Inductive finpref_behavior : Type :=
  | FTerminates (t: trace) (n: int)
  | FGoes_wrong (t: trace)
  | FTbc (t: trace).

Definition not_wrong_finpref (m:finpref_behavior) : Prop :=
  match m with
  | FGoes_wrong _ => False
  | _             => True
  end.

Definition prefix (m:finpref_behavior) (b:program_behavior) : Prop :=
  match m, b with
  | FTerminates t1 n1, Terminates t2 n2 => n1 = n2 /\ t1 = t2
  | FGoes_wrong t1, Goes_wrong t2 => t1 = t2
  | FTbc t1, b => behavior_prefix t1 b
  | _, _ => False
  end.

Definition finpref_trace (m : finpref_behavior) : trace :=
  match m with
  | FTerminates t _ | FGoes_wrong t | FTbc t => t
  end.

Definition trace_finpref_prefix (t : trace) (m : finpref_behavior) : Prop :=
  match m with
  | FTerminates t' _ | FGoes_wrong t' | FTbc t' => trace_prefix t t'
  end.

Definition finpref_trace_prefix (m : finpref_behavior) (t : trace) : Prop :=
  match m with
  | FTerminates _ t' | FGoes_wrong t' => False
  | FTbc t' => trace_prefix t' t
  end.

Definition behavior_improves_finpref (b:program_behavior) (m:finpref_behavior) :=
  exists t, b = Goes_wrong t /\ trace_finpref_prefix t m.

Definition does_prefix (L: semantics) (m: finpref_behavior) : Prop :=
  exists b, program_behaves L b /\ prefix m b.

(** Standard blame proof components *)

(* parallel_concrete' goes away *)

Lemma parallel_concrete_star_E0: forall {j s1 s1' s1'' s2 s2' s2'' e},
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s1 ∈ Right ->
  Star (semantics1 W1) s1 E0 s1' ->
  Step (semantics1 W1) s1' (e :: nil) s1'' ->
  Star (semantics1 W2) s2 E0 s2' ->
  Step (semantics1 W2) s2' (e :: nil) s2'' ->
exists j',
  right_state_injection s j' ge1 ge2 s1' s2'.
Proof.
  intros j s1 s1' s1'' s2 s2' s2'' e INJ RIGHT STAR1.
  revert j s1'' s2 s2' s2'' e INJ RIGHT.
  remember E0 as t eqn:SILENT. revert SILENT.
  induction STAR1 as [s1' | s1 t1 s1' t2 s1'' ? STEP1 STAR1 IH SILENT].
  - intros _ j s1'' s2 s2' s2'' e INJ RIGHT STEP1 STAR2 STEP2.
    revert s1' j s1'' s2'' e INJ RIGHT STEP1 STEP2.
    remember E0 as t eqn:SILENT. revert SILENT.
    induction STAR2 as [s2' | s2 t1 s2' t2 s2'' ? STEP2 STAR2 IH SILENT];
      [now eauto |].
    intros -> s1' j s1'' s2''' e INJ RIGHT STEP1 STEP2'.
    symmetry in SILENT. apply Eapp_E0_inv in SILENT as [-> ->].
    destruct (parallel_concrete_E0' _ _ _ _ _ _ INJ RIGHT STEP2 STEP1)
      as (_ & CONTRA & _).
    discriminate.
  - intros -> j s1''' s2 s2' s2'' e INJ RIGHT STEP1' STAR2 STEP2.
    symmetry in SILENT. apply Eapp_E0_inv in SILENT as [-> ->].
    remember E0 as t eqn:SILENT.
    revert SILENT j s1 s1' s1'' STEP1 STAR1 IH s1''' s2'' e INJ RIGHT STEP1' STEP2.
    induction STAR2 as [s2' | s2 t1 s2' t2 s2'' ? STEP2 STAR2 IH' SILENT].
    + intros _ j s1 s1' s1'' STEP1 STAR1 IH s1''' s2'' e INJ RIGHT STEP1' STEP2.
      destruct (parallel_concrete_E0 _ _ _ _ _ _ INJ RIGHT STEP1 STEP2)
        as (_ & CONTRA & _).
      discriminate.
    + intros -> j s1 s1' s1'' STEP1 STAR1 IH s1''' s2''' e INJ RIGHT STEP1' STEP2'.
      symmetry in SILENT. apply Eapp_E0_inv in SILENT as [-> ->].
      destruct (parallel_concrete_E0  _ _ _ _ _ _ INJ RIGHT STEP1 STEP2)
        as (j' & _ & INJ').
      apply (step_E0_same_side STEP1) in RIGHT.
      exact (IH eq_refl
               _ _ _ _ _ _
               INJ' RIGHT STEP1' STAR2 STEP2').
Qed.

Lemma parallel_abstract_star_E0: forall {j s1 s1' s1'' s2 s2' s2'' e},
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s1 ∈ Left ->
  Star (semantics1 W1) s1 E0 s1' ->
  Step (semantics1 W1) s1' (e :: nil) s1'' ->
  Star (semantics1 W2) s2 E0 s2' ->
  Step (semantics1 W2) s2' (e :: nil) s2'' ->
exists j',
  right_state_injection s j' ge1 ge2 s1' s2'.
Proof.
  intros j s1 s1' s1'' s2 s2' s2'' e INJ LEFT STAR1.
  revert j s1'' s2 s2' s2'' e INJ LEFT.
  remember E0 as t eqn:SILENT. revert SILENT.
  induction STAR1 as [s1' | s1 t1 s1' t2 s1'' ? STEP1 STAR1 IH SILENT].
  - intros _ j s1'' s2 s2' s2'' e INJ LEFT STEP1 STAR2 STEP2.
    revert s1' j s1'' s2'' e INJ LEFT STEP1 STEP2.
    remember E0 as t eqn:SILENT. revert SILENT.
    induction STAR2 as [s2' | s2 t1 s2' t2 s2'' ? STEP2 STAR2 IH SILENT];
      [now eauto |].
    intros -> s1' j s1'' s2''' e INJ LEFT STEP1 STEP2'.
    symmetry in SILENT. apply Eapp_E0_inv in SILENT as [-> ->].
    exploit parallel_abstract_E0_2; eauto. intros [j' INJ'].
    now eapply IH; eauto.
  - intros -> j s1''' s2 s2' s2'' e INJ LEFT STEP1' STAR2 STEP2.
    symmetry in SILENT. apply Eapp_E0_inv in SILENT as [-> ->].
    remember E0 as t eqn:SILENT.
    revert SILENT j s1''' s2'' e INJ LEFT STEP1' STEP2.
    induction STAR2 as [s2' | s2 t1 s2' t2 s2'' ? STEP2 STAR2 IH' SILENT].
    + intros _ j s1''' s2'' e INJ LEFT STEP1' STEP2.
      assert (exists j', right_state_injection s j' ge1 ge2 s1' s2')
        as [j' INJ'] by (eapply parallel_abstract_E0_1; eauto).
      apply (step_E0_same_side STEP1) in LEFT.
      exact (IH eq_refl _ _ _ _ _ _
               INJ' LEFT STEP1' (star_refl _ _ _) STEP2).
    + intros -> j s1''' s2''' e INJ LEFT STEP1' STEP2'.
      symmetry in SILENT. apply Eapp_E0_inv in SILENT as [-> ->].
      assert (exists j', right_state_injection s j' ge1 ge2 s1 s2')
        as [j' INJ'] by (eapply parallel_abstract_E0_2; eauto).
      exact (IH'
               STEP1 STAR1 IH eq_refl
               _ _ _ _
               INJ' LEFT STEP1' STEP2').
Qed.

(* Related to old [context_epsilon_star_is_silent'] *)
Lemma parallel_star_E0: forall {j s1 s1' s1'' s2 s2' s2'' e},
  right_state_injection s j ge1 ge2 s1 s2 ->
  Star (semantics1 W1) s1 E0 s1' ->
  Step (semantics1 W1) s1' (e :: nil) s1'' ->
  Star (semantics1 W2) s2 E0 s2' ->
  Step (semantics1 W2) s2' (e :: nil) s2'' ->
exists j',
  right_state_injection s j' ge1 ge2 s1' s2'.
Proof.
  intros j s1.
  destruct (state_split_decidable s1) as [LEFT | RIGHT].
  - intros; eapply parallel_abstract_star_E0; eassumption.
  - intros; eapply parallel_concrete_star_E0; eassumption.
Qed.

(* Lemma state_determinism': forall {p s s1 s2 e1 e2}, *)
(*   step1 (globalenv p) s (e1 :: nil) s1 -> *)
(*   step1 (globalenv p) s (e2 :: nil) s2 -> *)
(*   e1 = e2 /\ s1 = s2. *)

(* - [scs] naming scheme no longer makes sense, retooled
   - No need for [s |= s1 ∈ Left] type assumption *)
Lemma parallel_exec1: forall j s1 s2 s1'' s2'' t t1 t2,
  right_state_injection s j ge1 ge2 s1 s2 ->
  Star (semantics1 W1) s1 (t ** t1) s1'' ->
  Star (semantics1 W2) s2 (t ** t2) s2'' ->
  exists s1' s2' j',
    Star (semantics1 W1) s1 t s1' /\
    Star (semantics1 W2) s2 t s2' /\
    Star (semantics1 W1) s1' t1 s1'' /\
    Star (semantics1 W2) s2' t2 s2'' /\
    right_state_injection s j' ge1 ge2 s1' s2'.
Proof.
  intros j s1 s2 s1'' s2'' t; revert j s1 s2 s1'' s2''.
  induction t as [| e t IH];
    intros j s1 s2 s1'' s2'' t1 t2 RINJ STAR1 STAR2;
    (* Base case: follows trivially from the assumptions *)
    [do 3 eexists; now eauto using star_refl |].
  (* Inductive case *)
  destruct (star_cons_inv (sr_traces (semantics_receptive _)) STAR1)
    as (s1_1 & s1_2 & STAR1_1 & STEP1_2 & STAR1_3).
  change (_ t t1) with (t ** t1) in STAR1_3. clear STAR1.
  destruct (star_cons_inv (sr_traces (semantics_receptive _)) STAR2)
    as (s2_1 & s2_2 & STAR2_1 & STEP2_2 & STAR2_3).
  change (_ t t2) with (t ** t2) in STAR2_3. clear STAR2.
  pose proof parallel_star_E0 RINJ STAR1_1 STEP1_2 STAR2_1 STEP2_2 as [j' RINJ'].
  assert (exists j', right_state_injection s j' ge1 ge2 s1_2 s2_2)
    as [j'' RINJ'']. { (* This can be made into a helper lemma *)
    destruct (state_split_decidable s1_1) as [LEFT | RIGHT].
    - exploit parallel_abstract_t; eauto.
    - exploit parallel_concrete; eauto. intros (j'' & s2_2' & STEP2_2' & RINJ'').
      assert (s2_2 = s2_2') as <-
        by exact (step1_event_determ STEP2_2 STEP2_2').
      now eauto. }
  destruct (IH _ _ _ _ _ _ _ RINJ'' STAR1_3 STAR2_3)
    as (s1' & s2' & j''' & STAR1_3_1 & STAR2_3_1 & STAR1_3_2 & STAR2_3_2 & RINJ''').
  assert (STAR1' := star_trans
                      (star_trans STAR1_1 (star_one _ _ _ _ _ STEP1_2) eq_refl)
                      STAR1_3_1 eq_refl).
  assert (STAR2' := star_trans
                      (star_trans STAR2_1 (star_one _ _ _ _ _ STEP2_2) eq_refl)
                      STAR2_3_1 eq_refl).
  now eauto 8.
Qed.

Lemma parallel_exec j s1 s1' s2 s2' n t t':
  right_state_injection s j ge1 ge2 s1 s2 ->
  Star (semantics1 W1) s1 (t ** t') s1' ->
  Star (semantics1 W2) s2  t        s2' ->
  Nostep (semantics1 W2) s2' ->
  Smallstep.final_state (semantics1 W1) s1' n ->
  s |= s2' ∈ Right ->
  Smallstep.final_state (semantics1 W2) s2' n.
Proof.
  rewrite <- (E0_right t) at 2.
  intros part star1 star2.
  exploit parallel_exec1; eauto.
  clear j star1 star2 part. intros (s1'' & s2'' & (j' & _ & _ & star1 & star2 & part)).
  clear s1 s2 t. rename s1'' into s1. rename s2'' into s2. rename j' into j.
  intros nostep2 final1 in_prog.
  apply (star_E0_same_side star2) in in_prog.
  revert j s2 part star2 nostep2 final1 in_prog.
  induction star1 as [s1 | s1 t1 s1' t2 s1'' t step1 _ IH].
  - intros j s2 part star2 nostep2 final1 in_prog.
    assert (final2: Smallstep.final_state (semantics1 W2) s2 n). {
      inv part.
      - exfalso. eapply state_split_contra; now eauto.
      - inv final1.
        inv H1. inv RCONTINJ. inv RVALINJ.
        inv star2.
        + now constructor.
        + now inv H1. }
    inv final2.
    inv star2.
    + now constructor.
    + now inv H.
  - intros j s2 part star2 nostep2 final1 in_prog2.
    pose proof right_state_injection_same_side_left part in_prog2 as in_prog1.
    pose proof parallel_concrete _ _ _ _ _ part in_prog1 step1 as pc.
    revert part nostep2 in_prog2 IH pc.
    elim star2 using star_E0_ind'; clear s2 s2' star2.
    + intros s2 _ nostep2 _ _ (_ & s2' & step2 & _).
      apply nostep2 in step2. contradiction.
    + intros s2 s21' s2'' step21 star2 ? part nostep2 in_prog2 IH (j' & s22' & step22 & part').
      apply (star_E0_same_side (star_one _ _ _ _ _ step21)) in in_prog2.
      assert (s21' = s22') as <-. {
        destruct t1 as [| e1 [| e1' t1]].
        - exact (step1_E0_determ step21 step22).
        - now destruct (step1_E0_event_False step21 step22).
        - apply (sr_traces (semantics_receptive _)) in step22.
          inv step22. now inv H2. }
      clear step21 step22.
      exact (IH _ _ part' star2 nostep2 final1 in_prog2).
Qed.

Lemma parallel_exec' j s1 s1' s2 s2' t e t':
  right_state_injection s j ge1 ge2 s1 s2 ->
  Star (semantics1 W1) s1 (t ** e :: t') s1' ->
  Star (semantics1 W2) s2  t             s2' ->
  Nostep (semantics1 W2) s2' ->
  s |= s2' ∈ Left.
Proof.
  rewrite <- (E0_right t) at 2.
  intros part star1 star2.
  exploit parallel_exec1; eauto.
  clear j star1 star2 part.
  intros (s1'' & s2'' & (j' & _ & _ & star1 & star2 & part)) nostep2.
  clear s1 s2 t. rename s1'' into s1. rename s2'' into s2. rename j' into j.
  apply (star_E0_same_side star2).
  destruct (state_split_decidable s2) as [in_prog2 | in_prog2];
    [exact in_prog2 |].
  exfalso.
  destruct (star_cons_inv (sr_traces (semantics_receptive _)) star1)
    as (s1a & s1b & star1a & step1b & _).
  clear star1.
  revert j s1 star1a part nostep2 in_prog2. elim star2 using star_E0_ind';
    clear s2 s2' star2.
  - intros s2 j s1 star1a.
    assert (exists t s1a', Step (semantics1 W1) s1 t s1a') as (t & s1a' & step). {
      revert step1b. elim star1a using star_E0_ind'; now eauto. }
    intros part nostep2 in_prog2.
    apply (right_state_injection_same_side_left part) in in_prog2.
    exploit parallel_concrete; eauto. intros (j' & s2' & step2 & part').
    specialize (nostep2 _ _ step2). contradiction.
  - intros s2 s2' s2'' step2 star2 IH j s1 star1 part nostep2 in_prog2.
    revert step1b IH part. elim star1 using star_E0_ind'; clear s1 s1a star1.
    + intros s1 step1b _ part.
      apply (right_state_injection_same_side_left part) in in_prog2.
      destruct (parallel_concrete _ _ _ _ _ part in_prog2 step1b)
        as (j' & s2a & step2' & part').
      exact (step1_E0_event_False step2 step2').
    + intros s1 s1a s1a' step1a star1 _ step1b IH part.
      pose proof right_state_injection_same_side_left part in_prog2 as in_prog1.
      destruct (parallel_concrete_E0 _ _ _ _ _ _ part in_prog1 step1a step2)
        as (j' & _ & part').
      apply (star_E0_same_side (star_one _ _ _ _ _ step2)) in in_prog2.
      exact (IH _ _ star1 part' nostep2 in_prog2).
Qed.

(* CS.s_component scs2 \in domm (prog_interface c) -> *)
(* last_comp t \in domm (prog_interface c). *)
Lemma blame_last_comp_star p s1 t s2:
  Smallstep.initial_state (semantics1 p) s1 ->
  Star (semantics1 p) s1 t s2 ->
  s |= s2 ∈ Left ->
  blame_on_program t.
Proof.
Admitted. (* With default_compartment gone, needs minor adjustments *)

(* - Related to old [partialize_partition]
   - We may want to be more explicit about the initial injection *)
Lemma initial_state_injection s1 s2 :
  Smallstep.initial_state (semantics1 W1) s1 ->
  Smallstep.initial_state (semantics1 W2) s2 ->
  exists j,
    right_state_injection s j ge1 ge2 s1 s2.
Proof.
Admitted. (* Another standard assumption about initial states *)

(* - Quantify over p vs. W1 *)
Lemma does_prefix_star
  (m : finpref_behavior)
  (Hprefix : does_prefix (semantics1 W1) m)
  (NOT_WRONG : not_wrong_finpref m) :
  exists (sti : Smallstep.state (semantics1 W1))
         (stf : Smallstep.state (semantics1 W1)),
    Smallstep.initial_state (semantics1 W1) sti /\
    Star (semantics1 W1) sti (finpref_trace m) stf  /\
    (forall n,
      (exists t, m = FTerminates t n) ->
      Smallstep.final_state (semantics1 W1) stf n).
Proof.
  destruct Hprefix as [b [Hb Hmb]].
  inversion Hb as [s0 beh Hini Hbeh | Hini]; subst.
  - inversion Hbeh as [? ? ? Hstar | ? ? Hstar | ? Hreact | ? ? Hstar]; subst.
    (* Matching case. *)
    + destruct m as [tm | tm | tm].
      * simpl in *. destruct Hmb. subst.
        exists s0, s'. split; [| split]; try assumption.
        intros n [? EQ]. injection EQ as ?; subst. assumption.
      * contradiction.
      * (* This is like the contradictory cases below. *)
        destruct Hmb as [b Hb'].
        destruct b as [tb | tb | tb | tb];
          try discriminate.
        inversion Hb'; subst.
        destruct (star_app_inv (sr_traces (semantics_receptive _)) _ _ Hstar)
          as [s1 [Hstar1 Hstar2]].
        exists s0, s1. split; [| split]; try assumption.
        now intros ? [t' Hcontra].
    (* The remaining cases are essentially identical. *)
    + destruct m as [tm | tm | tm];
        try contradiction.
      destruct Hmb as [b Hb'].
      destruct b as [tb | tb | tb | tb];
        try discriminate.
      inversion Hb'; subst.
      destruct (star_app_inv (sr_traces (semantics_receptive _)) _ _ Hstar)
        as [s1 [Hstar1 Hstar2]].
      exists s0, s1. split; [| split]; try assumption.
      now intros ? [t' Hcontra].
    + destruct m as [tm | tm | tm];
        try contradiction.
      destruct Hmb as [b Hb'].
      destruct b as [tb | tb | tb | tb];
        try discriminate.
      inversion Hb'; subst.
      (* The only difference in this case is the lemma to be applied here. *)
      destruct (forever_reactive_app_inv (sr_traces (semantics_receptive _)) _ _ Hreact)
        as [s1 [Hstar Hreact']].
      exists s0, s1. split; [| split]; try assumption.
      now intros ? [t' Hcontra].
    + (* Same script as Diverges. *)
      destruct m as [tm | tm | tm];
        try contradiction.
      destruct Hmb as [b Hb'].
      destruct b as [tb | tb | tb | tb];
        try discriminate.
      inversion Hb'; subst.
      destruct (star_app_inv (sr_traces (semantics_receptive _)) _ _ Hstar)
        as [s1 [Hstar1 Hstar2]].
      exists s0, s1. split; [| split]; try assumption.
      now intros ? [t' Hcontra].
  - (* Contradiction on the existence of an initial state *)
    destruct W1_ini as [s1 initial_s1]. specialize (Hini s1). contradiction.
Qed.

(* - What to say about the interfaces of p1 and p2?
   - Closed, linkable, well-formed *)
Lemma blame_program (m: finpref_behavior) (t': trace)
  (HpCs_beh: program_behaves (semantics1 W2) (Goes_wrong t'))
  (HP'_Cs_beh_new: does_prefix (semantics1 W1) m)
  (Hnot_wrong': not_wrong_finpref m)
  (K: trace_finpref_prefix t' m):
  prefix m (Goes_wrong t') \/ blame_on_program t'.
Proof.
  apply does_prefix_star in HP'_Cs_beh_new; [| easy].
  destruct HP'_Cs_beh_new as [sini1 [sfin1 [Hini1 [HStar1 Hfinal1']]]].
  inversion HpCs_beh as [sini2 ? Hini2 Hstbeh2 | Hnot_initial2]; subst;
    [| destruct W2_ini as [s2 initial_s2];
       specialize (Hnot_initial2 s2);
       contradiction].
  inversion Hstbeh2 as [| | | ? sfin2 HStar2 HNostep2 Hnot_final2]; subst.
  assert (exists j0, right_state_injection s j0 ge1 ge2 sini1 sini2)
    as [j0 Hpartialize].
  { apply initial_state_injection; assumption. }
  (* Case analysis on m. FGoes_wrong can be ruled out by contradiction,
     but also solved exactly like the others. *)
  destruct m as [tm | tm | tm];
    (destruct K as [tm' Htm']; subst tm;
     unfold finpref_trace in HStar1).
  - simpl. right.
    assert (Hfinal1 : Smallstep.final_state (semantics1 W1) sfin1 n).
      apply Hfinal1'. eauto.
    (* A good amount of simplification is possible in the new proof *)
    assert (HNostep1 : Nostep (semantics1 W1) sfin1).
    { simpl in Hfinal1. simpl.
      inv Hfinal1.
      intros tcon scon Hcontra.
      inversion Hcontra. }
    pose proof parallel_exec _ _ _ _ _ _ _ _
      Hpartialize
      HStar1 HStar2 HNostep2 Hfinal1
      as Hparallel.
    destruct (state_split_decidable sfin2) as [Hparallel1 | Hparallel1].
    + exact (blame_last_comp_star _ _ _ _ Hini2 HStar2 Hparallel1).
    + specialize (Hparallel Hparallel1) as Hfinal2.
      specialize (Hnot_final2 n). contradiction.
  - simpl in Hnot_wrong'. contradiction.
  - simpl. destruct tm'.
    + left. exists (Goes_wrong nil). simpl. repeat rewrite E0_right. reflexivity.
    + right.
      pose proof parallel_exec' _ _ _ _ _ _ _ _
        Hpartialize
        HStar1 HStar2 HNostep2
        as Hparallel.
      eapply blame_last_comp_star; eassumption.
Qed.

Theorem blame (t m: trace):
  clight_program_has_initial_trace W2 t ->
  trace_prefix m t ->
  m <> t ->
  program_behaves (semantics1 W1) (Goes_wrong m) ->
  blame_on_program m.
Proof.
Admitted.

End Simulation.
