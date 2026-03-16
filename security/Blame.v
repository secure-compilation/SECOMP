Require Import String.
Require Import Coqlib Maps Errors Integers.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.
Require Import SimplLocalsproof.
Require Import Complements.
Require Import Ctypes Cop Clight.
Require Import Split.

Variant match_fundef (s: split): unit -> fundef -> fundef -> Prop :=
  | match_function_left: forall cp ty cc params vars vars' temps temps' body body',
      s |= cp ∈ Left ->
      match_fundef s tt (Internal {| fn_comp := cp; fn_return := ty; fn_callconv := cc;
                                fn_params := params; fn_vars := vars; fn_temps := temps;
                                fn_body := body |})
                     (Internal {| fn_comp := cp; fn_return := ty; fn_callconv := cc;
                                fn_params := params; fn_vars := vars'; fn_temps := temps';
                                fn_body := body' |})
  | match_external_left: forall ef tys ty cc,
      (* s |= ef ∈ Left -> *) (* FIXME merge *)
      match_fundef s tt (External ef tys ty cc)
                     (External ef tys ty cc)
  | match_right: forall fd,
      s |= fd ∈ Right ->
      match_fundef s tt fd fd
.

#[local] Instance has_comp_match_fundef (s: split): has_comp_match (match_fundef s).
intros ? x y H.
inv H; auto.
Qed.


Definition match_varinfo (ty1 ty2: type): Prop := ty1 = ty2.

Definition match_prog (s: split) := match_program_gen (match_fundef s) match_varinfo.

Section Equivalence.
  Variable s: split.
  Variable j: meminj.

  Definition same_domain_right (ge: genv) (m1: mem) :=
    forall b, j b <> None <-> (s, m1) |= b ∈ Right \/ exists fd, Genv.find_def ge b = Some (Gfun fd).

  Definition same_domain_left (ge1: genv) :=
    forall b,
      j b <> None <->
      exists cp, Genv.find_comp_of_block ge1 b = cp /\
                 s cp = Left.

  (* TODO: Move to memory (now redundant) *)
  Lemma free_block_compartment {m b lo hi cp m' b'} :
    Mem.free m b lo hi cp = Some m' ->
    Mem.block_compartment m b' = Mem.block_compartment m' b'.
  Proof.
    intros FREE.
    eapply Mem.free_preserves_comp; eassumption.
  Qed.

  Lemma same_domain_right_free ge m b lo hi cp m'
    (FREE : Mem.free m b lo hi cp = Some m')
    (BLOCKS : same_domain_right ge m) :
    same_domain_right ge m'.
  Proof.
    intros b'. specialize (BLOCKS b'). simpl in *.
    now rewrite <- (free_block_compartment FREE).
  Qed.

  Lemma same_domain_right_free_list ge m bs cp m'
    (FREE : Mem.free_list m bs cp = Some m')
    (BLOCKS : same_domain_right ge m) :
    same_domain_right ge m'.
  Proof.
    revert m cp m' FREE BLOCKS.
    induction bs as [| [[b lo] hi] ? IH]; intros.
    - now inv FREE.
    - simpl in FREE.
      destruct (Mem.free m b lo hi cp) as [m1 |] eqn:FREE1; [| discriminate].
      eapply same_domain_right_free in FREE1; [| exact BLOCKS].
      now eapply IH; eauto.
  Qed.

  Lemma same_domain_right_store ge chunk m b off v cp m' :
    Mem.store chunk m b off v cp = Some m' ->
    same_domain_right ge m ->
    same_domain_right ge m'.
  Proof.
    intros STORE DOM b'. specialize (DOM b'). simpl in *.
    now rewrite (Mem.store_block_compartment _ _ _ _ _ _ _ STORE).
  Qed.

  Lemma same_domain_right_storebytes ge m b ofs sz ocp m' :
    Mem.storebytes m b ofs sz ocp = Some m' ->
    same_domain_right ge m ->
    same_domain_right ge m'.
  Proof.
    intros STORE DOM b'. specialize (DOM b'). simpl in *.
    now rewrite (Mem.storebytes_block_compartment _ _ _ _ _ _ STORE).
  Qed.


  Record same_blocks (ge: genv) (m: mem) : Prop := {
    same_blocks_comp: forall b gd, Genv.find_def ge b = Some gd ->
                      Mem.block_compartment m b = comp_of gd;
    same_blocks_next: Ple (Genv.genv_next ge) (Mem.nextblock m)
  }.


  Lemma same_blocks_store chunk m b ofs sz cp m' ge
    (STORE : Mem.store chunk m b ofs sz cp = Some m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    constructor.
    - intros b' gd FIND.
      pose proof (Mem.store_block_compartment _ _ _ _ _ _ _ STORE b') as EQ.
      rewrite EQ. eapply same_blocks_comp; eauto.
    - rewrite (Mem.nextblock_store _ _ _ _ _ _ _ STORE).
      exact (same_blocks_next _ _ BLOCKS).
  Qed.

  Lemma same_blocks_storebytes m b ofs sz ocp m' ge
    (STORE : Mem.storebytes m b ofs sz ocp = Some m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    constructor.
    - intros b' gd FIND.
      pose proof (Mem.storebytes_block_compartment _ _ _ _ _ _ STORE b') as EQ.
      rewrite EQ. eapply same_blocks_comp; eauto.
    - rewrite (Mem.nextblock_storebytes _ _ _ _ _ _ STORE).
      exact (same_blocks_next _ _ BLOCKS).
  Qed.

  Lemma same_blocks_alloc m cp lo hi m' b ge
    (ALLOC : Mem.alloc m cp lo hi = (m', b))
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    constructor.
    - intros b' gd FIND.
      rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC).
      destruct eq_block as [->|].
      + exfalso.
        apply Genv.genv_defs_range in FIND.
        assert (b = Mem.nextblock m) by (eapply Mem.alloc_result; eauto).
        subst b.
        pose proof (same_blocks_next _ _ BLOCKS).
        unfold Plt, Ple in *. lia.
      + eapply same_blocks_comp; eauto.
    - rewrite (Mem.nextblock_alloc _ _ _ _ _ _ ALLOC).
      apply Ple_trans with (Mem.nextblock m).
      + exact (same_blocks_next _ _ BLOCKS).
      + apply Ple_succ.
  Qed.
  Lemma same_blocks_free m b lo hi cp m' ge
    (FREE : Mem.free m b lo hi cp = Some m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    constructor.
    - intros b' gd FIND.
      rewrite <- (Mem.free_preserves_comp _ _ _ _ _ _ FREE b').
      eapply same_blocks_comp; eauto.
    - rewrite (Mem.nextblock_free _ _ _ _ _ _ FREE).
      exact (same_blocks_next _ _ BLOCKS).
  Qed.

  Lemma same_blocks_free_list m bs cp m' ge
    (FREE : Mem.free_list m bs cp = Some m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    revert m BLOCKS FREE. induction bs as [|[[b lo] hi] bs IH]; intros m BLOCKS FREE.
    - simpl in FREE. inv FREE. assumption.
    - simpl in FREE. destruct (Mem.free m b lo hi cp) eqn:F; [|discriminate].
      eapply IH; [|eassumption].
      eapply same_blocks_free; eauto.
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
    { same_dom: same_domain_right ge1 m1;
      partial_mem_inject: Mem.inject j m1 m2;
      j_delta_zero: Mem.delta_zero j;
      j_injective: forall b1 b1' b2,
        j b1 = Some (b2, 0) -> j b1' = Some (b2, 0) -> b1 = b1';
      same_symb: forall cp, s cp = Right -> symbols_inject j ge1 ge2 cp;
      j_preserves_symbols: forall id b1 b2 delta,
        j b1 = Some (b2, delta) ->
        Genv.find_symbol ge1 id = Some b1 ->
        delta = 0 /\ Genv.find_symbol ge2 id = Some b2;
      same_blks1: same_blocks ge1 m1;
      same_blks2: same_blocks ge2 m2;
      right_side_image: forall b1 b2 delta,
        j b1 = Some (b2, delta) ->
        s (Mem.block_compartment m2 b2) = Right \/
        Genv.find_def ge2 b2 <> None;
      target_gvar_right: forall b1 b2 delta gv,
        j b1 = Some (b2, delta) ->
        Genv.find_def ge2 b2 = Some (Gvar gv) ->
        s (comp_of gv) = Right;
    }.


Lemma right_mem_injection_right ge1 ge2 m1 m2 b1 b2 delta :
  right_mem_injection ge1 ge2 m1 m2 ->
  j b1 = Some (b2, delta) ->
  s (Mem.block_compartment m2 b2) = Right \/ Genv.find_def ge2 b2 <> None.
Proof.
  intros RMI JB. exact (right_side_image _ _ _ _ RMI _ _ _ JB).
Qed.

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

Lemma remove_until_right_kcall_right: forall id f en le k,
    s (comp_of f) = Right ->
    remove_until_right (Kcall id f en le k) = Kcall id f en le k.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma remove_until_right_kcall_left: forall id f en le k,
    s (comp_of f) = Left ->
    remove_until_right (Kcall id f en le k) = remove_until_right k.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

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
| right_cont_injection_kcall_left: forall id1 id2 f1 f2 en1 en2 le1 le2 k1 k2,
    s |= f1 ∈ Left ->
    (* s |= f2 ∈ Left -> *)
    comp_of f1 = comp_of f2 ->
    right_cont_injection (remove_until_right k1) (remove_until_right k2) ->
    right_cont_injection (Kcall id1 f1 en1 le1 k1) (Kcall id2 f2 en2 le2 k2)
(* | right_cont_injection_kcall_left: forall id f en1 en2 le1 le2 k1 k2, *)
(*     s |= f ∈ Left -> *)
(*     right_cont_injection (remove_until_right k1) (remove_until_right k2) -> *)
(*     right_cont_injection (Kcall id f en1 le1 k1) (Kcall id f en2 le2 k2) *)
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
    right_mem_injection ge1 ge2 m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    (* the environments satisfy the injection *)
    right_env_injection e1 e2 ->
    right_tenv_injection le1 le2 ->

    right_executing_injection ge1 ge2 (State f s k1 e1 le1 m1) (State f s k2 e2 le2 m2)
| inject_callstates: forall f vs vs' k1 k2 m1 m2,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    (* the parameters are related by the memory injection *)
    Val.inject_list j vs vs' ->

    right_executing_injection ge1 ge2 (Callstate f vs k1 m1) (Callstate f vs' k2 m2)
| inject_returnstates: forall v v' k1 k2 m1 m2 ty cp,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    (* The return values are related by the injection *)
    Val.inject j v v' ->

    right_executing_injection ge1 ge2 (Returnstate v k1 m1 ty cp) (Returnstate v' k2 m2 ty cp)
.

(* Extract the caller's compartment from a continuation.
   Used for Callstate/Returnstate with comp_of = bottom (External functions),
   to inherit the caller's side rather than using bottom's side. *)
Fixpoint cont_caller_comp (k: cont) : compartment :=
  match k with
  | Kstop => top (* fallback; should not arise in well-formed executions *)
  | Kcall _ f _ _ _ => comp_of f
  | Kseq _ k' | Kloop1 _ _ k' | Kloop2 _ _ k' | Kswitch k' => cont_caller_comp k'
  end.

Definition state_comp (st: state) : compartment :=
  match st with
  | State f _ _ _ _ _ => comp_of f
  | Callstate fd _ k _ =>
      match fd with
      | Internal f => comp_of f
      | External _ _ _ _ => cont_caller_comp k
      end
  | Returnstate _ k _ _ cp =>
      if cp_eq_dec cp bottom
      then cont_caller_comp k
      else cp
  end.

#[export] Instance state_has_side: has_side state :=
    { in_side s := fun st δ => s (state_comp st) = δ }.

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

Variant right_state_injection (ge1 ge2: genv) (st1 st2: state) : Prop :=
| LeftControl:
    (* program (left) has control *)
    s |= st1 ∈ Left ->
    s |= st2 ∈ Left ->

    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 (memory_of st1) (memory_of st2) ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection (remove_until_right (cont_of st1)) (remove_until_right (cont_of st2)) ->

    right_state_injection ge1 ge2 st1 st2
| RightControl:
    (* context (right) has control *)
    s |= st1 ∈ Right ->
    s |= st2 ∈ Right ->
    right_executing_injection ge1 ge2 st1 st2 ->
    right_state_injection ge1 ge2 st1 st2.


End Equivalence.

Lemma init_mem_same_blocks (p: program) m1
      (MEM: Genv.init_mem p = Some m1):
  same_blocks (globalenv p) m1.
Proof.
  constructor.
  - intros b gd FIND.
    exact (Genv.init_mem_find_def _ _ MEM FIND).
  - unfold Ple.
    replace (Genv.genv_next (globalenv p)) with (Mem.nextblock m1). lia.
    symmetry. apply Genv.init_mem_genv_next. exact MEM.
Qed.

(* Wellformedness: all Internal functions appearing in states/continuations
   have proper compartments (neither bottom nor top). *)
Fixpoint cont_proper (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ f _ _ k' => comp_of f <> bottom /\ comp_of f <> top /\ cont_proper k'
  | Kseq _ k' | Kloop1 _ _ k' | Kloop2 _ _ k' | Kswitch k' => cont_proper k'
  end.

Definition state_wf (st: state) : Prop :=
  match st with
  | State f _ k _ _ _ => comp_of f <> bottom /\ comp_of f <> top /\ cont_proper k
  | Callstate fd _ k _ =>
      (match fd with Internal f => comp_of f <> bottom /\ comp_of f <> top | External _ _ _ _ => True end) /\
      cont_proper k
  | Returnstate _ k _ _ _ => cont_proper k
  end.

Lemma cont_proper_call_cont k :
  cont_proper k -> cont_proper (call_cont k).
Proof.
  induction k; simpl; try tauto.
Qed.

Lemma flowsto_no_bottom_no_top cp1 cp2 :
  flowsto cp1 cp2 -> cp1 <> bottom -> cp2 <> top -> cp1 = cp2.
Proof.
  intros FL NB NT. inv FL; congruence.
Qed.

Lemma find_funct_find_def_clight
      (ge0: genv) vf (fd: Clight.fundef) :
  Genv.find_funct ge0 vf = Some fd ->
  exists b, Genv.find_def ge0 b = Some (Gfun fd).
Proof.
  unfold Genv.find_funct, Genv.find_funct_ptr. intros.
  destruct vf; try discriminate.
  destruct (Ptrofs.eq_dec i Ptrofs.zero); try discriminate.
  destruct (Genv.find_def ge0 b) as [[] |] eqn:DEF; try discriminate.
  inv H. exists b. exact DEF.
Qed.

Scheme find_label_stmt_ind := Induction for statement Sort Prop
  with find_label_ls_ind := Induction for labeled_statements Sort Prop.
Combined Scheme find_label_combined_ind from find_label_stmt_ind, find_label_ls_ind.

Lemma find_label_cont_proper lbl :
  (forall s0 k s' k',
    find_label lbl s0 k = Some (s', k') ->
    cont_proper k -> cont_proper k') /\
  (forall ls k s' k',
    find_label_ls lbl ls k = Some (s', k') ->
    cont_proper k -> cont_proper k').
Proof.
  apply find_label_combined_ind;
    simpl; intros; try discriminate; eauto.
  - (* Ssequence *)
    destruct (find_label lbl s (Kseq s0 k)) eqn:E.
    + inv H1. eauto.
    + eauto.
  - (* Sifthenelse *)
    destruct (find_label lbl s k) eqn:E.
    + inv H1. eauto.
    + eauto.
  - (* Sloop *)
    destruct (find_label lbl s (Kloop1 s s0 k)) eqn:E.
    + inv H1. eauto.
    + eauto.
  - (* Slabel *)
    destruct (ident_eq lbl l).
    + inv H0. exact H1.
    + destruct (find_label lbl s k) eqn:E; [inv H0; eauto | discriminate].
  - (* LScons *)
    destruct (find_label lbl s (Kseq (seq_of_labeled_statement l) k)) eqn:E.
    + inv H1. eauto.
    + eauto.
Qed.

Section Simulation.
  Context (c p1 p2: Clight.program).
  Variable s: split.

  Context (W1 W2: Clight.program).
  Hypothesis c_p1: link p1 c = Some W1.
  Hypothesis c_p2: link p2 c = Some W2.

  Hypothesis match_W1_W2: match_prog s tt W1 W2.

  Hypothesis c_Right: s |= c ∈ Right.
  Hypothesis p1_Left: s |= p1 ∈ Left.
  Hypothesis p2_Left: s |= p2 ∈ Left.

  (* Context (ge1 ge2: genv). *)
  Let ge1 := globalenv W1.
  Let ge2 := globalenv W2.
  Let cpm1 := comp_of_main W1.
  Let cpm2 := comp_of_main W2.
  (* Is this hypothesis realistic? *)
  Hypothesis same_cenv: genv_cenv ge1 = genv_cenv ge2.

  Hypothesis s_top_left: s top = Left.
  Hypothesis s_bottom_left: s bottom = Left.

  (* Internal functions always have proper (non-bottom, non-top) compartments *)
  Hypothesis no_bottom_W1: forall b f,
    Genv.find_def ge1 b = Some (Gfun (Internal f)) -> comp_of f <> bottom.
  Hypothesis no_bottom_W2: forall b f,
    Genv.find_def ge2 b = Some (Gfun (Internal f)) -> comp_of f <> bottom.
  Hypothesis no_top_W1: forall b f,
    Genv.find_def ge1 b = Some (Gfun (Internal f)) -> comp_of f <> top.
  Hypothesis no_top_W2: forall b f,
    Genv.find_def ge2 b = Some (Gfun (Internal f)) -> comp_of f <> top.

  (* Global variables also have proper compartments *)
  Hypothesis no_bottom_var_W1: forall b v,
    Genv.find_def ge1 b = Some (Gvar v) -> comp_of v <> bottom.
  Hypothesis no_top_var_W1: forall b v,
    Genv.find_def ge1 b = Some (Gvar v) -> comp_of v <> top.

  (* Right-side variables' init data only references Right-side or function globals *)
  Hypothesis init_addrof_right_closed:
    forall b v id ofs b' v',
      Genv.find_def ge1 b = Some (Gvar v) ->
      s (comp_of v) = Right ->
      In (Init_addrof id ofs) (gvar_init v) ->
      Genv.find_symbol ge1 id = Some b' ->
      Genv.find_def ge1 b' = Some (Gvar v') ->
      s (comp_of v') = Right.

  (* Policy compartments agree with definition compartments *)
  Hypothesis policy_comp_def_W1: forall id b gd,
    Genv.find_symbol ge1 id = Some b ->
    Genv.find_def ge1 b = Some gd ->
    Senv.find_comp ge1 id = comp_of gd.

  Hypothesis s_main_left: s (comp_of_main W1) = Left.
  Hypothesis cpm1_not_bottom: comp_of_main W1 <> bottom.
  Hypothesis cpm1_not_top: comp_of_main W1 <> top.

  (* TODO: derivable from match_W1_W2 + W1 hypotheses *)
  Hypothesis s_main_left_2: s (comp_of_main W2) = Left.
  Hypothesis cpm2_not_bottom: comp_of_main W2 <> bottom.
  Hypothesis cpm2_not_top: comp_of_main W2 <> top.

  Hypothesis W1_ini: exists s, Smallstep.initial_state (semantics1 W1) s.
  Hypothesis W2_ini: exists s, Smallstep.initial_state (semantics1 W2) s.


Lemma W1_norepet: list_norepet (prog_defs_names W1).
Proof.
  unfold prog_defs_names.
  Transparent Linker_prog Linker_program.
  assert (H := c_p1). unfold link, Linker_program, link_program in H.
  simpl in H.
  destruct (link_prog (program_of_program p1) (program_of_program c)) as [p|] eqn:LP; try discriminate.
  destruct (lift_option _) as [[typs LT]|]; try discriminate.
  destruct (link_build_composite_env _ _ _ _ _ _ _ _) as [env [P Q]].
  inv H.
  simpl.
  destruct (link_prog_inv _ _ _ LP) as (_ & _ & yes & EQ).
  rewrite EQ. simpl.
  pose proof PTree.elements_keys_norepet as EKN.
  exact (EKN _ _).
Qed.
Lemma W2_norepet: list_norepet (prog_defs_names W2).
Proof.
  unfold prog_defs_names.
  Transparent Linker_prog Linker_program.
  assert (H := c_p2). unfold link, Linker_program, link_program in H.
  simpl in H.
  destruct (link_prog (program_of_program p2) (program_of_program c)) as [p|] eqn:LP; try discriminate.
  destruct (lift_option _) as [[typs LT]|]; try discriminate.
  destruct (link_build_composite_env _ _ _ _ _ _ _ _) as [env [P Q]].
  inv H.
  simpl.
  destruct (link_prog_inv _ _ _ LP) as (_ & _ & yes & EQ).
  rewrite EQ. simpl.
  pose proof PTree.elements_keys_norepet as EKN.
  exact (EKN _ _).
Qed.
Opaque Linker_prog Linker_program.

Lemma call_cont_cont_caller_comp k:
  forall oid f0 e0 le0 k', call_cont k = Kcall oid f0 e0 le0 k' ->
  cont_caller_comp k = comp_of f0.
Proof.
  induction k; simpl; intros; try congruence; eauto.
Qed.

(* call_cont only returns Kstop or Kcall *)
Lemma call_cont_is_stop_or_kcall k:
  call_cont k = Kstop \/
  exists oid f0 e le k', call_cont k = Kcall oid f0 e le k'.
Proof.
  induction k; simpl; try tauto.
  right. eauto 6.
Qed.

Lemma call_comp_left k:
  cont_proper k ->
  s (cont_caller_comp k) = Left ->
  s (call_comp cpm1 k) = Left.
Proof.
  intros KP LEFT.
  unfold call_comp. destruct (call_cont_is_stop_or_kcall k) as [CC | (oid & f0 & e0 & le0 & k' & CC)];
    rewrite CC.
  - exact s_main_left.
  - pose proof (call_cont_cont_caller_comp k _ _ _ _ _ CC) as EQ.
    rewrite EQ in LEFT. exact LEFT.
Qed.

Lemma cont_proper_call_comp_not_bottom k:
  cont_proper k ->
  call_comp cpm1 k <> bottom.
Proof.
  intros KP.
  unfold call_comp. destruct (call_cont_is_stop_or_kcall k) as [CC | (oid & f0 & e0 & le0 & k' & CC)];
    rewrite CC.
  - exact cpm1_not_bottom.
  - pose proof (cont_proper_call_cont k KP) as KP'.
    rewrite CC in KP'. destruct KP' as [NB _]. exact NB.
Qed.

Lemma cont_proper_call_comp_not_top k:
  cont_proper k ->
  call_comp cpm1 k <> top.
Proof.
  intros KP.
  unfold call_comp. destruct (call_cont_is_stop_or_kcall k) as [CC | (oid & f0 & e0 & le0 & k' & CC)];
    rewrite CC.
  - exact cpm1_not_top.
  - pose proof (cont_proper_call_cont k KP) as KP'.
    rewrite CC in KP'. destruct KP' as [_ [NT _]]. exact NT.
Qed.

Lemma call_comp_left_2 k:
  cont_proper k ->
  s (cont_caller_comp k) = Left ->
  s (call_comp cpm2 k) = Left.
Proof.
  intros KP LEFT.
  unfold call_comp. destruct (call_cont_is_stop_or_kcall k) as [CC | (oid & f0 & e0 & le0 & k' & CC)];
    rewrite CC.
  - exact s_main_left_2.
  - pose proof (call_cont_cont_caller_comp k _ _ _ _ _ CC) as EQ.
    rewrite EQ in LEFT. exact LEFT.
Qed.

Lemma cont_proper_call_comp_not_bottom_2 k:
  cont_proper k ->
  call_comp cpm2 k <> bottom.
Proof.
  intros KP.
  unfold call_comp. destruct (call_cont_is_stop_or_kcall k) as [CC | (oid & f0 & e0 & le0 & k' & CC)];
    rewrite CC.
  - exact cpm2_not_bottom.
  - pose proof (cont_proper_call_cont k KP) as KP'.
    rewrite CC in KP'. destruct KP' as [NB _]. exact NB.
Qed.

Lemma cont_proper_call_comp_not_top_2 k:
  cont_proper k ->
  call_comp cpm2 k <> top.
Proof.
  intros KP.
  unfold call_comp. destruct (call_cont_is_stop_or_kcall k) as [CC | (oid & f0 & e0 & le0 & k' & CC)];
    rewrite CC.
  - exact cpm2_not_top.
  - pose proof (cont_proper_call_cont k KP) as KP'.
    rewrite CC in KP'. destruct KP' as [_ [NT _]]. exact NT.
Qed.

Lemma right_cont_injection_call_comp j0 k1 k2:
  right_cont_injection s j0 k1 k2 ->
  call_cont k1 <> Kstop ->
  call_comp cpm1 k1 = call_comp cpm2 k2.
Proof.
  intros RCONTINJ NOTSTOP.
  induction RCONTINJ; simpl in *.
  - congruence.
  - apply IHRCONTINJ. exact NOTSTOP.
  - apply IHRCONTINJ. exact NOTSTOP.
  - apply IHRCONTINJ. exact NOTSTOP.
  - apply IHRCONTINJ. exact NOTSTOP.
  - unfold call_comp. simpl. congruence.
  - unfold call_comp. simpl. reflexivity.
Qed.

Lemma state_split_decidable:
  forall st, s |= st ∈ Left \/ s |= st ∈ Right.
Proof.
  intros st. simpl. destruct (s (state_comp st)); auto.
Qed.

Lemma state_split_contra:
  forall st, s |= st ∈ Left -> s |= st ∈ Right -> False.
Proof.
  intros st. simpl. destruct (s (state_comp st)); discriminate.
Qed.

Lemma step_E0_state_wf_preserved: forall (ge0: genv) cpm0 s1 s2,
  (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  step1 cpm0 ge0 s1 E0 s2 ->
  state_wf s1 ->
  state_wf s2.
Proof.
  intros ge0 cpm0 s1 s2 PROPER STEP WF.
  inv STEP; simpl in *; try tauto.
  - (* step_call *)
    destruct WF as (NB & NT & KP).
    destruct fd.
    + destruct (find_funct_find_def_clight _ _ _ H2) as [b DEF].
      split; [exact (PROPER _ _ DEF) |]. tauto.
    + split; [exact I |]. tauto.
  - (* step_return_0 *)
    destruct WF as (NB & NT & KP). exact (cont_proper_call_cont _ KP).
  - (* step_return_1 *)
    destruct WF as (NB & NT & KP). exact (cont_proper_call_cont _ KP).
  - (* step_goto *)
    destruct WF as (NB & NT & KP).
    split; [exact NB |]. split; [exact NT |].
    eapply (proj1 (find_label_cont_proper _)); eauto.
    exact (cont_proper_call_cont _ KP).
Qed.

Lemma step_state_wf_preserved: forall (ge0: genv) cpm0 s1 t s2,
  (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  step1 cpm0 ge0 s1 t s2 ->
  state_wf s1 ->
  state_wf s2.
Proof.
  intros ge0 cpm0 s1 t s2 PROPER STEP WF.
  inv STEP; simpl in *; try tauto;
  try (destruct WF as (NB & NT & KP);
    try (exact (cont_proper_call_cont _ KP));
    try tauto; fail).
  - (* step_call *)
    destruct WF as (NB & NT & KP).
    destruct fd.
    + destruct (find_funct_find_def_clight _ _ _ H2) as [b DEF].
      split; [exact (PROPER _ _ DEF) |]. tauto.
    + split; [exact I |]. tauto.
  - (* step_goto *)
    destruct WF as (NB & NT & KP).
    split; [exact NB |]. split; [exact NT |].
    eapply (proj1 (find_label_cont_proper _)); eauto.
    exact (cont_proper_call_cont _ KP).
Qed.

Lemma star_state_wf_preserved: forall (ge0: genv) cpm0 s1 t s2,
  (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  star (step1 cpm0) ge0 s1 t s2 ->
  state_wf s1 ->
  state_wf s2.
Proof.
  intros ge0 cpm0 s1 t s2 PROPER STAR WF.
  induction STAR; auto.
  apply IHSTAR. eapply step_state_wf_preserved; eauto.
Qed.

Lemma initial_state_wf: forall (p: program) st,
  (forall b f, Genv.find_def (Genv.globalenv p) b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  initial_state p st ->
  state_wf st.
Proof.
  intros p0 st PROPER INI. inv INI.
  simpl. split; [| exact I].
  assert (FD: Genv.find_def ge b = Some (Gfun (Internal f))).
  { unfold Genv.find_funct_ptr in H1.
    destruct (Genv.find_def ge b) as [[fi|ef]|]; try discriminate.
    congruence. }
  exact (PROPER _ _ FD).
Qed.

Lemma call_trace_E0_flowsto (ge0: genv)
      cp cp' vf vargs ty :
  call_trace ge0 cp cp' vf vargs ty E0 ->
  flowsto cp' cp.
Proof.
  intros CT. inv CT.
  unfold Genv.type_of_call in H.
  destruct (flowsto_dec cp' cp); [assumption | congruence].
Qed.


Lemma return_trace_E0_flowsto (ge0: genv)
      cp cp' v ty :
  return_trace ge0 cp cp' v ty E0 ->
  flowsto cp' cp.
Proof.
  intros RT. inv RT.
  unfold Genv.type_of_call in H.
  destruct (flowsto_dec cp' cp); [assumption | congruence].
Qed.

Lemma step_E0_same_side: forall (ge0: genv) cpm0 s1 s2 sd,
  (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  state_wf s1 ->
  step1 cpm0 ge0 s1 E0 s2 ->
  s |= s1 ∈ sd <-> s |= s2 ∈ sd.
Proof.
  intros ge0 cpm0 s1 s2 sd PROPER WF STEP.
  simpl in *.
  inv STEP; simpl in *; try tauto.
  - (* step_call *)
    destruct WF as (NB & NT & KP).
    destruct fd.
    + (* Internal *)
      apply call_trace_E0_flowsto in EV.
      destruct (find_funct_find_def_clight _ _ _ H2) as [b DEF].
      destruct (PROPER _ _ DEF) as [NB' NT'].
      replace (comp_of f0) with (comp_of f) by (symmetry; eapply flowsto_no_bottom_no_top; eauto).
      tauto.
    + (* External *) tauto.
  - (* step_return_0 *)
    destruct WF as (NB & NT & KP).
    destruct (cp_eq_dec (comp_of f) bottom); [congruence | tauto].
  - (* step_return_1 *)
    destruct WF as (NB & NT & KP).
    destruct (cp_eq_dec (comp_of f) bottom); [congruence | tauto].
  - (* step_skip_call *)
    destruct WF as (NB & NT & KP).
    destruct (cp_eq_dec (comp_of f) bottom); [congruence | tauto].
  - (* step_returnstate *)
    destruct WF as (NB' & NT' & KP).
    destruct (cp_eq_dec cp bottom); [tauto |].
    apply return_trace_E0_flowsto in EV.
        assert (cp = comp_of f) by (eapply flowsto_no_bottom_no_top; eassumption).
    subst cp. tauto.
Qed.
Lemma star_E0_same_side: forall (ge0: genv) cpm0 s1 s2 sd,
  (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  state_wf s1 ->
  star (step1 cpm0) ge0 s1 E0 s2 ->
  s |= s1 ∈ sd <-> s |= s2 ∈ sd.
Proof.
  intros ge0 cpm0 s1 s2 sd PROPER WF STAR.
  remember E0 as t.
  induction STAR; subst.
  - tauto.
  - destruct (Eapp_E0_inv _ _ (eq_sym H0)) as [E1 E2]. subst.
    assert (WF2: state_wf s2) by (eapply step_E0_state_wf_preserved; eauto).
    rewrite (step_E0_same_side _ _ _ _ _ PROPER WF H).
    apply IHSTAR; auto.
Qed.

Lemma right_state_injection_same_side_left: forall {j ge1 ge2 s1 s2 sd},
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s2 ∈ sd ->
  s |= s1 ∈ sd.
Proof.
  intros j0 ge1' ge2' s1 s2 sd RINJ SIDE.
  destruct sd; inv RINJ.
  - assumption.
  - exfalso. eapply state_split_contra; eauto.
  - exfalso. eapply state_split_contra; eauto.
  - assumption.
Qed.

Lemma right_state_injection_same_side_right: forall {j ge1 ge2 s1 s2 sd},
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s1 ∈ sd ->
  s |= s2 ∈ sd.
Proof.
  intros j0 ge1' ge2' s1 s2 sd RINJ SIDE.
  destruct sd; inv RINJ.
  - assumption.
  - exfalso. eapply state_split_contra; eauto.
  - exfalso. eauto using state_split_contra.
  - assumption.
Qed.

Lemma right_state_injection_left_rmi: forall {j ge1 ge2 s1 s2},
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s1 ∈ Left ->
  right_mem_injection s j ge1 ge2 (memory_of s1) (memory_of s2).
Proof.
  intros j0 ge1' ge2' s1 s2 RINJ LEFT.
  inv RINJ.
  - assumption.
  - exfalso. eapply state_split_contra; eauto.
Qed.

Lemma right_state_injection_left_rcinj: forall {j ge1 ge2 s1 s2},
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s1 ∈ Left ->
  right_cont_injection s j (remove_until_right s (cont_of s1)) (remove_until_right s (cont_of s2)).
Proof.
  intros j0 ge1' ge2' s1 s2 RINJ LEFT.
  inv RINJ.
  - assumption.
  - exfalso. eapply state_split_contra; eauto.
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
    (COMP: Mem.block_compartment m b' = cp')
    (COMP': Mem.block_compartment m' b' = cp''):
    cp' = cp''.
  Proof.
    rewrite (assign_loc_block_compartment ASGN) in COMP.
    congruence.
  Qed.

  (* NOTE: assign_loc_can_access_block removed - false for By_copy with sizeof=0.
     Use alloc_variables_env_block_compartment to track block compartments instead. *)

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
  Proof. eapply perm_assign_loc_2; eauto. Qed.

  (* TODO: move, remove transparency hacks, add other direction *)
  Lemma assign_loc_range_perm {ce cp ty m b b' ofs lo hi k p bf v m'}
    (ASGN: assign_loc ce cp ty m b ofs bf v m')
    (PERM: Mem.range_perm m' b' lo hi k p):
    Mem.range_perm m b' lo hi k p.
  Proof. intros delta RANGE. eapply perm_assign_loc_2; eauto. Qed.

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
    unfold Mem.can_access_block in *.
    revert b ACC.
    induction BIND; intros;
      [assumption |].
    apply IHBIND.
    rewrite <- (assign_loc_block_compartment H0). exact ACC.
  Qed.

  Lemma bind_parameters_can_access_block_2 {ge cp e m1 params vl m2 b cp'}
    (BIND: bind_parameters ge cp e m1 params vl m2)
    (ACC : Mem.can_access_block m2 b cp'):
    Mem.can_access_block m1 b cp'.
  Proof.
    unfold Mem.can_access_block in *.
    revert b ACC.
    induction BIND; intros;
      [assumption |].
    apply IHBIND in ACC.
    rewrite <- (assign_loc_block_compartment H0) in ACC.
    exact ACC.
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

  (* NOTE: alloc_variables_can_access_block_fresh removed - needs reformulation for new compartment model *)

  Lemma alloc_variables_env_block_compartment ge0 cp e1 m1 vars e2 m2
    (ALLOC: alloc_variables ge0 cp e1 m1 vars e2 m2)
    (ENV: forall id b ty, e1 ! id = Some (b, ty) ->
                          Mem.block_compartment m1 b = cp):
    forall id b ty, e2 ! id = Some (b, ty) ->
                    Mem.block_compartment m2 b = cp.
  Proof.
    induction ALLOC; [exact ENV|].
    apply IHALLOC.
    intros id0 b0 ty0. rewrite PTree.gsspec.
    destruct (peq id0 id) as [->|Hne].
    - injection 1 as <- <-.
      rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ H).
      destruct eq_block; [reflexivity | contradiction].
    - intros Hid.
      rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ H).
      destruct eq_block as [->|]; [reflexivity | eauto].
  Qed.

  Lemma alloc_variables_env_not_global ge0 cp e1 m1 vars e2 m2
    (ALLOC: alloc_variables ge0 cp e1 m1 vars e2 m2)
    (BLOCKS: same_blocks ge0 m1)
    (ENV: forall id b ty, e1 ! id = Some (b, ty) ->
                          Genv.find_def ge0 b = None):
    forall id b ty, e2 ! id = Some (b, ty) ->
                    Genv.find_def ge0 b = None.
  Proof.
    induction ALLOC; [exact ENV|].
    apply IHALLOC.
    - eapply same_blocks_alloc; eauto.
    - intros id0 b0 ty0. rewrite PTree.gsspec.
      destruct (peq id0 id) as [->|Hne].
      + injection 1 as <- <-.
        destruct (Genv.find_def ge0 b1) as [gd|] eqn:FD; [|reflexivity].
        exfalso. apply Genv.genv_defs_range in FD.
        assert (b1 = Mem.nextblock m) by (eapply Mem.alloc_result; eauto).
        subst b1. pose proof (same_blocks_next _ _ BLOCKS).
        unfold Plt, Ple in *. lia.
      + eauto.
  Qed.

  Lemma same_blocks_alloc_variables ge0 cp e1 m1 vars e2 m2
    (ALLOC : alloc_variables ge0 cp e1 m1 vars e2 m2)
    (BLOCKS : same_blocks ge0 m1) :
    same_blocks ge0 m2.
  Proof.
    induction ALLOC; [assumption|].
    apply IHALLOC. eapply same_blocks_alloc; eauto.
  Qed.

  Lemma same_blocks_bind_parameters ge0 cp e m1 params vargs m2
    (BIND : bind_parameters ge0 cp e m1 params vargs m2)
    (BLOCKS : same_blocks ge0 m1) :
    same_blocks ge0 m2.
  Proof.
    induction BIND; [assumption|].
    apply IHBIND. eapply same_blocks_assign_loc; eauto.
  Qed.

  Lemma same_blocks_function_entry1 ge f vargs m e le m'
    (ENTRY : function_entry1 ge f vargs m e le m')
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    inv ENTRY.
    eapply same_blocks_bind_parameters; eauto.
    eapply same_blocks_alloc_variables; eauto.
  Qed.

  Lemma same_blocks_set_perm_list m l p m' ge0
    (SPL : Mem.set_perm_list m l p = Some m')
    (BLOCKS : same_blocks ge0 m) :
    same_blocks ge0 m'.
  Proof.
    constructor.
    - intros b' gd FIND.
      rewrite (Mem.set_perm_list_block_compartment _ _ _ _ _ SPL).
      eapply same_blocks_comp; eauto.
    - pose proof (same_blocks_next _ _ BLOCKS).
      cut (Mem.nextblock m' = Mem.nextblock m). { intros ->. assumption. }
      clear -SPL. revert m SPL.
      induction l as [|[[b lo] hi] l IH]; simpl; intros.
      + inv SPL. reflexivity.
      + destruct (Mem.set_perm m b p) eqn:SP; [|discriminate].
        transitivity (Mem.nextblock m0).
        * eapply IH; eauto.
        * unfold Mem.set_perm in SP. destruct plt in SP; [|discriminate].
          inv SP. reflexivity.
  Qed.

  Lemma same_blocks_external_call ef (sge: Senv.t) ge0 cp vargs m t vres m'
    (EC : external_call ef sge cp vargs m t vres m')
    (BLOCKS : same_blocks ge0 m) :
    same_blocks ge0 m'.
  Proof.
    constructor.
    - intros b gd FIND.
      assert (VB: Mem.valid_block m b).
      { unfold Mem.valid_block.
        eapply Plt_Ple_trans; [| exact (same_blocks_next _ _ BLOCKS)].
        eapply Genv.genv_defs_range; eauto. }
      erewrite <- ec_preserves_comp; eauto using external_call_spec.
      eapply same_blocks_comp; eauto.
    - eapply Ple_trans; [exact (same_blocks_next _ _ BLOCKS) |].
      destruct (Pos.lt_total (Mem.nextblock m) (Mem.nextblock m')) as [LT | [EQ | GT]].
      + unfold Ple. lia.
      + unfold Ple. lia.
      + exfalso. apply (Plt_strict (Mem.nextblock m')).
        eapply ec_valid_block; eauto using external_call_spec.
  Qed.

  Lemma same_blocks_step1 s1 t s1'
    (BLKS : same_blocks ge1 (memory_of s1))
    (STEP : step1 cpm1 ge1 s1 t s1'):
    same_blocks ge1 (memory_of s1').
  Proof.
    inv STEP; simpl in *; eauto using same_blocks_assign_loc,
      same_blocks_store, same_blocks_free_list, same_blocks_function_entry1,
      same_blocks_external_call.
    - (* set_perm case in call *)
      destruct (cp_eq_dec (comp_of f) (comp_of fd)); [subst; auto|].
      destruct (cp_eq_dec (comp_of fd) bottom); [subst; auto|].
      eapply same_blocks_set_perm_list; eauto.
    - (* set_perm case in returnstate *)
      destruct (cp_eq_dec (comp_of f) cp); [subst; auto|].
      destruct (cp_eq_dec cp bottom); [subst; auto|].
      eapply same_blocks_set_perm_list; eauto.
  Qed.

  Lemma same_blocks_step ge0 cpm0 st t st'
    (BLKS : same_blocks ge0 (memory_of st))
    (STEP : step1 cpm0 ge0 st t st'):
    same_blocks ge0 (memory_of st').
  Proof.
    inv STEP; simpl in *; eauto using same_blocks_assign_loc,
      same_blocks_store, same_blocks_free_list, same_blocks_function_entry1,
      same_blocks_external_call.
    - (* set_perm case in call *)
      destruct (cp_eq_dec (comp_of f) (comp_of fd)); [subst; auto|].
      destruct (cp_eq_dec (comp_of fd) bottom); [subst; auto|].
      eapply same_blocks_set_perm_list; eauto.
    - (* set_perm case in returnstate *)
      destruct (cp_eq_dec (comp_of f) cp); [subst; auto|].
      destruct (cp_eq_dec cp bottom); [subst; auto|].
      eapply same_blocks_set_perm_list; eauto.
  Qed.

  (* Blocks above genv_next have no definition *)
  Lemma find_def_above_genv_next (ge: genv) b:
    Ple (Genv.genv_next ge) b -> Genv.find_def ge b = None.
  Proof.
    intros GE.
    destruct (Genv.find_def ge b) as [gd|] eqn:FD; [|reflexivity].
    exfalso.
    apply Genv.genv_defs_range in FD.
    unfold Plt, Ple in *. lia.
  Qed.

  (* If j maps only blocks with invert_symbol, then j maps only blocks below genv_next *)
  Lemma j_has_symbol_maps_below_genv_next (j: meminj) (ge: genv) b:
    (forall b', j b' <> None -> exists id, Genv.invert_symbol ge b' = Some id) ->
    j b <> None ->
    Plt b (Genv.genv_next ge).
  Proof.
    intros JHS Jb.
    destruct (JHS _ Jb) as [id INV].
    apply Genv.invert_find_symbol in INV.
    eapply Genv.genv_symb_range; eauto.
  Qed.

  (* env_blocks_unmapped follows from j_has_symbol + env blocks above genv_next *)
  Lemma env_blocks_unmapped_from_above (j: meminj) (ge: genv) (e: env) b:
    (forall b', j b' <> None -> exists id, Genv.invert_symbol ge b' = Some id) ->
    (forall b' lo hi, In (b', lo, hi) (blocks_of_env ge e) -> Ple (Genv.genv_next ge) b') ->
    (exists lo hi, In (b, lo, hi) (blocks_of_env ge e)) ->
    j b = None.
  Proof.
    intros JHS ABOVE [lo [hi IN]].
    destruct (j b) as [[b2 delta]|] eqn:Jb; [|reflexivity].
    exfalso.
    assert (Ple (Genv.genv_next ge) b) as GE by (eapply ABOVE; eauto).
    assert (Plt b (Genv.genv_next ge)) as LT.
    { eapply j_has_symbol_maps_below_genv_next; eauto. congruence. }
    unfold Plt, Ple in *. lia.
  Qed.

  (* Alternative: env blocks unmapped using same_domain_right instead of JHS.
     For Left-side env blocks: block_compartment = comp_of f (Left),
     and find_def = None (above genv_next), so same_domain_right gives j b = None. *)
  Lemma env_blocks_unmapped_via_same_domain (j: meminj) (ge0: genv) (m: mem) (e: env) b cp:
    same_domain_right s j ge0 m ->
    same_blocks ge0 m ->
    s cp = Left ->
    (forall b' lo hi, In (b', lo, hi) (blocks_of_env ge0 e) ->
       Ple (Genv.genv_next ge0) b' /\ Mem.block_compartment m b' = cp) ->
    (exists lo hi, In (b, lo, hi) (blocks_of_env ge0 e)) ->
    j b = None.
  Proof.
    intros DOM BLKS CP_LEFT ABOVE [lo [hi IN]].
    destruct (j b) as [[b2 delta]|] eqn:Jb; [|reflexivity].
    exfalso.
    destruct (ABOVE _ _ _ IN) as [GE BCC].
    assert (FDEF: Genv.find_def ge0 b = None) by (eapply find_def_above_genv_next; exact GE).
    assert (JBN: j b <> None) by congruence.
    apply DOM in JBN.
    destruct JBN as [RSIDE | [fd GFUN]].
    - unfold in_side, Mem.has_side_block in RSIDE.
      rewrite BCC in RSIDE. rewrite CP_LEFT in RSIDE. discriminate.
    - congruence.
  Qed.

  (* env_blocks_info follows from env blocks above genv_next + block_compartment *)
  Lemma env_blocks_info_from_above (ge: genv) (e: env) (m: mem) cp b lo hi:
    In (b, lo, hi) (blocks_of_env ge e) ->
    (forall b' lo' hi', In (b', lo', hi') (blocks_of_env ge e) ->
       Ple (Genv.genv_next ge) b' /\ Mem.block_compartment m b' = cp) ->
    Mem.block_compartment m b = cp /\ Genv.find_def ge b = None.
  Proof.
    intros IN ABOVE.
    destruct (ABOVE _ _ _ IN) as [GE BC].
    split; [exact BC | eapply find_def_above_genv_next; exact GE].
  Qed.

  (* gfun_no_perm is preserved by alloc *)
  Lemma gfun_no_perm_alloc (ge: genv) m cp lo hi m' b:
    Mem.alloc m cp lo hi = (m', b) ->
    same_blocks ge m ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m b0 ofs k p) ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m' b0 ofs k p).
  Proof.
    intros ALLOC BLKS GNP b0 fd DEF ofs k p PERM.
    assert (b0 <> b) as NEQ.
    { intros ->.
      pose proof (Mem.alloc_result _ _ _ _ _ _ ALLOC) as ->.
      apply Genv.genv_defs_range in DEF.
      pose proof (same_blocks_next _ _ BLKS).
      unfold Plt, Ple in *. lia. }
    eapply GNP; eauto.
    eapply Mem.perm_alloc_4; eauto.
  Qed.

  (* gfun_no_perm is preserved by store *)
  Lemma gfun_no_perm_store (ge: genv) chunk m b ofs v cp m':
    Mem.store chunk m b ofs v cp = Some m' ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs' k p, ~ Mem.perm m b0 ofs' k p) ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs' k p, ~ Mem.perm m' b0 ofs' k p).
  Proof.
    intros STORE GNP b0 fd DEF ofs' k p PERM.
    eapply GNP; eauto.
    eapply Mem.perm_store_2; eauto.
  Qed.

  (* gfun_no_perm is preserved by storebytes *)
  Lemma gfun_no_perm_storebytes (ge: genv) m b ofs bytes cp m':
    Mem.storebytes m b ofs bytes cp = Some m' ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs' k p, ~ Mem.perm m b0 ofs' k p) ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs' k p, ~ Mem.perm m' b0 ofs' k p).
  Proof.
    intros STORE GNP b0 fd DEF ofs' k p PERM.
    eapply GNP; eauto.
    eapply Mem.perm_storebytes_2; eauto.
  Qed.

  (* gfun_no_perm is preserved by free *)
  Lemma gfun_no_perm_free (ge: genv) m b lo hi cp m':
    Mem.free m b lo hi cp = Some m' ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m b0 ofs k p) ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m' b0 ofs k p).
  Proof.
    intros FREE GNP b0 fd DEF ofs k p PERM.
    eapply GNP; eauto.
    eapply Mem.perm_free_3; eauto.
  Qed.

  (* gfun_no_perm is preserved by free_list *)
  Lemma gfun_no_perm_free_list (ge: genv) m bs cp m':
    Mem.free_list m bs cp = Some m' ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m b0 ofs k p) ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m' b0 ofs k p).
  Proof.
    revert m. induction bs as [| [[b lo] hi] bs IH]; intros m FREE GNP.
    - simpl in FREE. inv FREE. exact GNP.
    - simpl in FREE.
      destruct (Mem.free m b lo hi cp) eqn:F; [|discriminate].
      eapply IH; eauto.
      eapply gfun_no_perm_free; eauto.
  Qed.

  (* gfun_no_perm is preserved by set_perm_list when listed blocks don't overlap with Gfun *)
  Lemma gfun_no_perm_set_perm_list (ge: genv) m l p m':
    Mem.set_perm_list m l p = Some m' ->
    same_blocks ge m ->
    (forall b lo hi, In (b, lo, hi) l -> Ple (Genv.genv_next ge) b) ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k pp, ~ Mem.perm m b0 ofs k pp) ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k pp, ~ Mem.perm m' b0 ofs k pp).
  Proof.
    intros SPL BLKS ABOVE GNP b0 fd DEF ofs k pp PERM.
    assert (Plt b0 (Genv.genv_next ge)) as LT.
    { eapply Genv.genv_defs_range; eauto. }
    assert (~In b0 (map (fun '(b, _, _) => b) l)) as NIN.
    { intros IN. apply in_map_iff in IN.
      destruct IN as [[[b' lo'] hi'] [EQ IN]]. simpl in EQ. subst b'.
      pose proof (ABOVE _ _ _ IN).
      unfold Plt, Ple in *. lia. }
    eapply GNP; eauto.
    eapply Mem.set_perm_list_perm_not_in; eauto.
    intros [[xb xlo] xhi] IN. simpl.
    intros ->. apply NIN. apply in_map_iff.
    exists (b0, xlo, xhi). auto.
  Qed.

  (* gfun_no_perm is preserved by assign_loc *)
  Lemma gfun_no_perm_assign_loc (ge: genv) ce cp ty m b ofs bf v m':
    assign_loc ce cp ty m b ofs bf v m' ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs' k p, ~ Mem.perm m b0 ofs' k p) ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs' k p, ~ Mem.perm m' b0 ofs' k p).
  Proof.
    intros ASSIGN GNP.
    inv ASSIGN.
    - eapply gfun_no_perm_store; eauto.
    - eapply gfun_no_perm_storebytes; eauto.
    - inv H. eapply gfun_no_perm_store; eauto.
  Qed.

  (* gfun_no_perm is preserved by external calls *)
  Lemma gfun_no_perm_external_call (ge: genv) ef sge cp vargs m t vres m':
    external_call ef sge cp vargs m t vres m' ->
    same_blocks ge m ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m b0 ofs k p) ->
    (forall b0 fd, Genv.find_def ge b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m' b0 ofs k p).
  Proof.
    intros EC BLKS GNP b0 fd DEF ofs k p PERM.
    assert (Mem.valid_block m b0) as VB.
    { unfold Mem.valid_block.
      eapply Plt_Ple_trans; [| exact (same_blocks_next _ _ BLKS)].
      eapply Genv.genv_defs_range; eauto. }
    eapply (GNP b0 fd DEF ofs Max p).
    eapply ec_max_perm; eauto using external_call_spec.
    destruct k; [exact PERM | eapply Mem.perm_cur_max; exact PERM].
  Qed.

  (* gfun_no_perm is preserved by alloc_variables *)
  Lemma gfun_no_perm_alloc_variables ge0 cp e1 m1 vars e2 m2:
    alloc_variables ge0 cp e1 m1 vars e2 m2 ->
    same_blocks ge0 m1 ->
    (forall b0 fd, Genv.find_def ge0 b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m1 b0 ofs k p) ->
    (forall b0 fd, Genv.find_def ge0 b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m2 b0 ofs k p).
  Proof.
    induction 1; intros BLKS GNP; [exact GNP|].
    apply IHalloc_variables.
    - eapply same_blocks_alloc; eauto.
    - eapply gfun_no_perm_alloc; eauto.
  Qed.

  (* gfun_no_perm is preserved by bind_parameters *)
  Lemma gfun_no_perm_bind_parameters ge0 cp e m1 params vargs m2:
    bind_parameters ge0 cp e m1 params vargs m2 ->
    (forall b0 fd, Genv.find_def ge0 b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m1 b0 ofs k p) ->
    (forall b0 fd, Genv.find_def ge0 b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m2 b0 ofs k p).
  Proof.
    induction 1; intros GNP; [exact GNP|].
    apply IHbind_parameters.
    eapply gfun_no_perm_assign_loc; eauto.
  Qed.

  (* gfun_no_perm is preserved by function_entry1 *)
  Lemma gfun_no_perm_function_entry1 ge0 f vargs m e le m':
    function_entry1 ge0 f vargs m e le m' ->
    same_blocks ge0 m ->
    (forall b0 fd, Genv.find_def ge0 b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m b0 ofs k p) ->
    (forall b0 fd, Genv.find_def ge0 b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m' b0 ofs k p).
  Proof.
    intros ENTRY BLKS GNP. inv ENTRY.
    eapply gfun_no_perm_bind_parameters; eauto.
    eapply gfun_no_perm_alloc_variables; eauto.
  Qed.

  (* alloc_variables produces env blocks above genv_next *)
  Lemma alloc_variables_blocks_above ge0 cp e1 m1 vars e2 m2:
    alloc_variables ge0 cp e1 m1 vars e2 m2 ->
    same_blocks ge0 m1 ->
    (forall id b ty, e1 ! id = Some (b, ty) -> Ple (Genv.genv_next ge0) b) ->
    (forall id b ty, e2 ! id = Some (b, ty) -> Ple (Genv.genv_next ge0) b).
  Proof.
    induction 1; intros BLKS ABOVE; [exact ABOVE|].
    apply IHalloc_variables.
    - eapply same_blocks_alloc; eauto.
    - intros id' b' ty' GET.
      destruct (peq id' id) as [->|NEQ].
      + rewrite PTree.gss in GET. inv GET.
        pose proof (Mem.alloc_result _ _ _ _ _ _ H) as ->.
        exact (same_blocks_next _ _ BLKS).
      + rewrite PTree.gso in GET by exact NEQ.
        eapply ABOVE; eauto.
  Qed.

  (* alloc_variables produces env blocks above genv_next with correct compartment.
     Combined lemma to avoid redundant induction. *)
  Lemma alloc_variables_env_ok ge0 cp e1 m1 vars e2 m2:
    alloc_variables ge0 cp e1 m1 vars e2 m2 ->
    same_blocks ge0 m1 ->
    (forall id b ty, e1 ! id = Some (b, ty) ->
       Ple (Genv.genv_next ge0) b /\ Mem.block_compartment m1 b = cp /\
       Mem.valid_block m1 b) ->
    (forall id b ty, e2 ! id = Some (b, ty) ->
       Ple (Genv.genv_next ge0) b /\ Mem.block_compartment m2 b = cp /\
       Mem.valid_block m2 b).
  Proof.
    induction 1; intros BLKS ENV; [exact ENV|].
    apply IHalloc_variables.
    - eapply same_blocks_alloc; eauto.
    - intros id' b' ty' GET.
      destruct (peq id' id) as [->|NEQ].
      + rewrite PTree.gss in GET. inv GET.
        pose proof (Mem.alloc_result _ _ _ _ _ _ H) as RES.
        split; [| split].
        * rewrite RES. exact (same_blocks_next _ _ BLKS).
        * erewrite Mem.alloc_block_compartment; eauto.
          rewrite RES. destruct (eq_block (Mem.nextblock m) (Mem.nextblock m)); congruence.
        * eapply Mem.valid_new_block; eauto.
      + rewrite PTree.gso in GET by exact NEQ.
        destruct (ENV _ _ _ GET) as [GE [BC VB]].
        split; [exact GE | split].
        * erewrite Mem.alloc_block_compartment; eauto.
          pose proof (Mem.alloc_result _ _ _ _ _ _ H) as RES. subst b1.
          destruct (eq_block b' (Mem.nextblock m)); [| exact BC].
          subst b'. exfalso. unfold Mem.valid_block, Plt in VB. lia.
        * eapply Mem.valid_block_alloc; eauto.
  Qed.

  (* bind_parameters preserves block_compartment *)
  Lemma bind_parameters_block_compartment ge0 cp e m1 params vargs m2 b:
    bind_parameters ge0 cp e m1 params vargs m2 ->
    Mem.block_compartment m1 b = Mem.block_compartment m2 b.
  Proof.
    induction 1; [reflexivity|].
    etransitivity; [| exact IHbind_parameters].
    inv H0.
    - symmetry. eapply Mem.store_block_compartment; eauto.
    - symmetry. eapply Mem.storebytes_block_compartment; eauto.
  Qed.

  (* env blocks in blocks_of_env are above genv_next after function_entry1 *)
  Lemma function_entry1_env_above ge0 f vargs m e le m':
    function_entry1 ge0 f vargs m e le m' ->
    same_blocks ge0 m ->
    forall b lo hi, In (b, lo, hi) (blocks_of_env ge0 e) ->
      Ple (Genv.genv_next ge0) b.
  Proof.
    intros ENTRY BLKS b lo hi IN. inv ENTRY.
    unfold blocks_of_env in IN.
    apply in_map_iff in IN. destruct IN as [[id' [b' ty']] [EQ IN]].
    simpl in EQ. inv EQ.
    apply PTree.elements_complete in IN.
    eapply alloc_variables_env_ok in H0; eauto.
    - exact (proj1 H0).
    - intros id0 b0 ty0 GET. rewrite PTree.gempty in GET. discriminate.
  Qed.


  (* alloc_variables preserves block_compartment for blocks valid before *)
  Lemma alloc_variables_block_compartment_old ge0 cp e1 m1 vars e2 m2 b:
    alloc_variables ge0 cp e1 m1 vars e2 m2 ->
    Mem.valid_block m1 b ->
    Mem.block_compartment m2 b = Mem.block_compartment m1 b.
  Proof.
    induction 1; intros VB; [reflexivity|].
    rewrite IHalloc_variables.
    - erewrite Mem.alloc_block_compartment; eauto.
      pose proof (Mem.alloc_result _ _ _ _ _ _ H) as RES. subst b1.
      destruct (eq_block b (Mem.nextblock m)); [| reflexivity].
      subst b. exfalso. unfold Mem.valid_block, Plt in VB. lia.
    - eapply Mem.valid_block_alloc; eauto.
  Qed.

  (* env blocks have correct compartment and are valid after function_entry1 *)
  Lemma function_entry1_env_comp ge0 f vargs m e le m':
    function_entry1 ge0 f vargs m e le m' ->
    same_blocks ge0 m ->
    forall b lo hi, In (b, lo, hi) (blocks_of_env ge0 e) ->
      Mem.block_compartment m' b = comp_of f /\ Mem.valid_block m' b.
  Proof.
    intros ENTRY BLKS b lo hi IN. inv ENTRY.
    unfold blocks_of_env in IN.
    apply in_map_iff in IN. destruct IN as [[id' [b' ty']] [EQ IN]].
    simpl in EQ. inv EQ.
    apply PTree.elements_complete in IN.
    assert (ENV_OK: Ple (Genv.genv_next ge0) b /\
                    Mem.block_compartment m1 b = comp_of f /\
                    Mem.valid_block m1 b).
    { eapply alloc_variables_env_ok; eauto.
      intros id0 b0 ty0 GET. rewrite PTree.gempty in GET. discriminate. }
    destruct ENV_OK as [_ [BC VB]].
    split.
    - erewrite <- bind_parameters_block_compartment; eauto.
    - clear -H1 VB. induction H1; [exact VB|].
      apply IHbind_parameters. inv H0;
        [eapply Mem.store_valid_block_1 | eapply Mem.storebytes_valid_block_1]; eauto.
  Qed.

  Lemma free_list_block_compartment' l cp m m' b':
    Mem.free_list m l cp = Some m' ->
    Mem.block_compartment m' b' = Mem.block_compartment m b'.
  Proof.
    revert m. induction l as [| [[b lo] hi] l IH]; simpl; intros m H.
    - inv H; reflexivity.
    - destruct (Mem.free m b lo hi cp) eqn:F; [| discriminate].
      rewrite (IH _ H). symmetry. eapply free_block_compartment; eauto.
  Qed.

  (* external_call preserves block_compartment for valid blocks *)
  Lemma external_call_block_compartment ef ge0 cp vargs m t vres m' b:
    external_call ef ge0 cp vargs m t vres m' ->
    Mem.valid_block m b ->
    Mem.block_compartment m' b = Mem.block_compartment m b.
  Proof.
    intros EC VB.
    symmetry. eapply ec_preserves_comp; [exact (external_call_spec ef cp) | exact EC | exact VB].
  Qed.

  (* gfun_no_perm is preserved by any Clight step *)
  Lemma gfun_no_perm_step ge0 cpm0 st t st':
    step1 cpm0 ge0 st t st' ->
    same_blocks ge0 (memory_of st) ->
    (forall b0 fd, Genv.find_def ge0 b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm (memory_of st) b0 ofs k p) ->
    (match st with
     | State _ _ _ e _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge0 e) ->
           Ple (Genv.genv_next ge0) b
     | Returnstate _ (Kcall _ _ e _ _) _ _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge0 e) ->
           Ple (Genv.genv_next ge0) b
     | _ => True end) ->
    (forall b0 fd, Genv.find_def ge0 b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm (memory_of st') b0 ofs k p).
  Proof.
    intros STEP BLKS GNP ENV.
    inv STEP; simpl in *; eauto.
    - (* step_assign *)
      eapply gfun_no_perm_assign_loc; eauto.
    - (* step_call: set_perm case *)
      destruct (cp_eq_dec (comp_of f) (comp_of fd)); [subst; eauto|].
      destruct (cp_eq_dec (comp_of fd) bottom); [subst; eauto|].
      eapply gfun_no_perm_set_perm_list; eauto.
    - (* step_builtin *)
      eapply gfun_no_perm_external_call; eauto.
    - (* step_return_0 *)
      eapply gfun_no_perm_free_list; eauto.
    - (* step_return_1 *)
      eapply gfun_no_perm_free_list; eauto.
    - (* step_skip_call *)
      eapply gfun_no_perm_free_list; eauto.
    - (* step_internal_function *)
      eapply gfun_no_perm_function_entry1; eauto.
    - (* step_external_function *)
      eapply gfun_no_perm_external_call; eauto.
    - (* step_returnstate: set_perm case *)
      destruct (cp_eq_dec (comp_of f) cp); [subst; eauto|].
      destruct (cp_eq_dec cp bottom); [subst; eauto|].
      eapply gfun_no_perm_set_perm_list; eauto.
  Qed.

  (* Env blocks in continuation frames are above genv_next *)
  Fixpoint cont_env_above (ge: genv) (k: cont) : Prop :=
    match k with
    | Kstop => True
    | Kcall _ _ e _ k' =>
        (forall b lo hi, In (b, lo, hi) (blocks_of_env ge e) ->
           Ple (Genv.genv_next ge) b) /\
        cont_env_above ge k'
    | Kseq _ k' | Kloop1 _ _ k' | Kloop2 _ _ k' | Kswitch k' =>
        cont_env_above ge k'
    end.

  Lemma cont_env_above_call_cont ge0 k:
    cont_env_above ge0 k -> cont_env_above ge0 (call_cont k).
  Proof.
    induction k; simpl; try tauto.
  Qed.

  (* Env blocks in continuation frames have correct block_compartment and are valid.
     Validity is needed to transfer the invariant across alloc_variables. *)
  Fixpoint cont_env_comp (ge: genv) (m: mem) (k: cont) : Prop :=
    match k with
    | Kstop => True
    | Kcall _ f e _ k' =>
        (forall b lo hi, In (b, lo, hi) (blocks_of_env ge e) ->
           Mem.block_compartment m b = comp_of f /\ Mem.valid_block m b) /\
        cont_env_comp ge m k'
    | Kseq _ k' | Kloop1 _ _ k' | Kloop2 _ _ k' | Kswitch k' =>
        cont_env_comp ge m k'
    end.

  Lemma cont_env_comp_call_cont ge0 m k:
    cont_env_comp ge0 m k -> cont_env_comp ge0 m (call_cont k).
  Proof.
    induction k; simpl; try tauto.
  Qed.

  (* cont_env_comp is preserved when block_compartment doesn't change for valid blocks
     and valid blocks remain valid *)
  Lemma cont_env_comp_mem_eq ge0 m1 m2 k:
    cont_env_comp ge0 m1 k ->
    (forall b, Mem.valid_block m1 b -> Mem.block_compartment m2 b = Mem.block_compartment m1 b) ->
    (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
    cont_env_comp ge0 m2 k.
  Proof.
    revert m1 m2. induction k; simpl; intros m1 m2; try tauto;
      try (intros; eapply IHk; eauto; fail).
    (* Kcall *)
    intros [BC CEC] EQ VB. split.
    - intros b lo hi IN. destruct (BC _ _ _ IN) as [BC' VB']. split; [rewrite EQ; eauto | eauto].
    - eapply IHk; eauto.
  Qed.

  (* Combined state invariant *)
  Definition state_inv (ge: genv) (st: state) : Prop :=
    (forall b fd, Genv.find_def ge b = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm (memory_of st) b ofs k p) /\
    same_blocks ge (memory_of st) /\
    cont_env_above ge (cont_of st) /\
    (match st with
     | State _ _ _ e _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge e) ->
           Ple (Genv.genv_next ge) b
     | _ => True
     end) /\
    cont_env_comp ge (memory_of st) (cont_of st) /\
    (match st with
     | State f _ _ e _ m =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge e) ->
           Mem.block_compartment m b = comp_of f /\ Mem.valid_block m b
     | _ => True
     end).

  Lemma state_inv_gfun_no_perm ge0 st:
    state_inv ge0 st ->
    forall b fd, Genv.find_def ge0 b = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm (memory_of st) b ofs k p.
  Proof. intros [? _]; auto. Qed.

  Lemma state_inv_same_blocks ge0 st:
    state_inv ge0 st ->
    same_blocks ge0 (memory_of st).
  Proof. intros [_ [? _]]; auto. Qed.

  (* env_blocks_above for the match shape needed by gfun_no_perm_step *)
  Lemma state_inv_env_above ge0 st:
    state_inv ge0 st ->
    (match st with
     | State _ _ _ e _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge0 e) ->
           Ple (Genv.genv_next ge0) b
     | Returnstate _ (Kcall _ _ e _ _) _ _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge0 e) ->
           Ple (Genv.genv_next ge0) b
     | _ => True
     end).
  Proof.
    intros [_ [_ [CONT [ENV _]]]].
    destruct st; simpl in *; auto.
    destruct k; simpl in *; auto.
    destruct CONT as [? _]; auto.
  Qed.

  Lemma find_label_cont_env_above:
    forall ge0 lbl st k st' k',
      find_label lbl st k = Some (st', k') ->
      cont_env_above ge0 k -> cont_env_above ge0 k'.
  Proof.
    intros ge0 lbl st.
    induction st using find_label_stmt_ind
      with (P0 := fun ls => forall k st' k',
        find_label_ls lbl ls k = Some (st', k') ->
        cont_env_above ge0 k -> cont_env_above ge0 k');
      simpl; intros; try discriminate; eauto.
    - (* Ssequence *)
      destruct (find_label lbl st1 (Kseq st2 k)) eqn:E; [inv H; eauto | eauto].
    - (* Sifthenelse *)
      destruct (find_label lbl st1 k) eqn:E; [inv H; eauto | eauto].
    - (* Sloop *)
      destruct (find_label lbl st1 (Kloop1 st1 st2 k)) eqn:E; [inv H; eauto | eauto].
    - (* Slabel *)
      destruct (ident_eq lbl l); [inv H; eauto | eauto].
    - (* LScons *)
      destruct (find_label lbl st (Kseq (seq_of_labeled_statement l) k)) eqn:E;
        [inv H; eauto | eauto].
  Qed.

  Lemma find_label_cont_env_comp:
    forall ge0 m lbl st k st' k',
      find_label lbl st k = Some (st', k') ->
      cont_env_comp ge0 m k -> cont_env_comp ge0 m k'.
  Proof.
    intros ge0 m lbl st.
    induction st using find_label_stmt_ind
      with (P0 := fun ls => forall k st' k',
        find_label_ls lbl ls k = Some (st', k') ->
        cont_env_comp ge0 m k -> cont_env_comp ge0 m k');
      simpl; intros; try discriminate; eauto.
    - destruct (find_label lbl st1 (Kseq st2 k)) eqn:E; [inv H; eauto | eauto].
    - destruct (find_label lbl st1 k) eqn:E; [inv H; eauto | eauto].
    - destruct (find_label lbl st1 (Kloop1 st1 st2 k)) eqn:E; [inv H; eauto | eauto].
    - destruct (ident_eq lbl l); [inv H; eauto | eauto].
    - destruct (find_label lbl st (Kseq (seq_of_labeled_statement l) k)) eqn:E;
        [inv H; eauto | eauto].
  Qed.

  (* Helper: alloc_variables preserves valid_block for pre-existing blocks *)
  Lemma alloc_variables_valid_block ge0 cp e1 m1 vars e2 m2 b:
    alloc_variables ge0 cp e1 m1 vars e2 m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b.
  Proof.
    induction 1; [auto|].
    intros VB. apply IHalloc_variables. eapply Mem.valid_block_alloc; eauto.
  Qed.

  Lemma bind_parameters_valid_block ge0 cp e m1 params vargs m2 b:
    bind_parameters ge0 cp e m1 params vargs m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b.
  Proof.
    induction 1; [auto|].
    intros VB. apply IHbind_parameters.
    inv H0; [eapply Mem.store_valid_block_1 | eapply Mem.storebytes_valid_block_1]; eauto.
  Qed.

  Lemma function_entry1_valid_block ge0 f vargs m e le m' b:
    function_entry1 ge0 f vargs m e le m' ->
    Mem.valid_block m b -> Mem.valid_block m' b.
  Proof.
    intros ENTRY VB. inv ENTRY.
    eapply bind_parameters_valid_block; eauto.
    eapply alloc_variables_valid_block; eauto.
  Qed.

  Lemma free_list_valid_block l cp m m' b:
    Mem.free_list m l cp = Some m' ->
    Mem.valid_block m b -> Mem.valid_block m' b.
  Proof.
    revert m. induction l as [| [[b0 lo] hi] l IH]; simpl; intros m H VB.
    - inv H; exact VB.
    - destruct (Mem.free m b0 lo hi cp) eqn:F; [| discriminate].
      eapply IH; eauto. eapply Mem.valid_block_free_1; eauto.
  Qed.

  Lemma step_valid_block ge0 cpm0 st t st':
    step1 cpm0 ge0 st t st' ->
    forall b, Mem.valid_block (memory_of st) b -> Mem.valid_block (memory_of st') b.
  Proof.
    intros STEP b VB.
    inv STEP; simpl in *; try exact VB;
      try (eapply free_list_valid_block; eauto; fail);
      try (eapply (ec_valid_block (external_call_spec _ _)); eauto; fail);
      try (eapply function_entry1_valid_block; eauto; fail).
    - (* step_assign *)
      match goal with AL: assign_loc _ _ _ _ _ _ _ _ _ |- _ =>
        inv AL end; eauto using Mem.store_valid_block_1, Mem.storebytes_valid_block_1.
      match goal with SBF: store_bitfield _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        inv SBF end.
      unfold Mem.storev in *. destruct (Vptr _ _); try discriminate.
      eapply Mem.store_valid_block_1; eauto.
    - (* step_call/returnstate: set_perm *)
      match goal with SP: (if cp_eq_dec ?a ?b then _ else _) |- _ =>
        destruct (cp_eq_dec a b) in SP; [subst; exact VB|];
        destruct (cp_eq_dec _ bottom) in SP; [subst; exact VB|];
        eapply Mem.set_perm_list_valid_block_1; eauto end.
    - (* step_returnstate: set_perm *)
      match goal with SP: (if cp_eq_dec ?a ?b then _ else _) |- _ =>
        destruct (cp_eq_dec a b) in SP; [subst; exact VB|];
        destruct (cp_eq_dec _ bottom) in SP; [subst; exact VB|];
        eapply Mem.set_perm_list_valid_block_1; eauto end.
  Qed.

  (* Helper: all step-produced memory operations preserve block_compartment for
     blocks valid in the pre-step memory *)
  Lemma step_block_compartment_valid ge0 cpm0 st t st':
    step1 cpm0 ge0 st t st' ->
    forall b, Mem.valid_block (memory_of st) b ->
      Mem.block_compartment (memory_of st') b = Mem.block_compartment (memory_of st) b.
  Proof.
    intros STEP b VB.
    inv STEP; simpl in *; try reflexivity;
      try (eapply free_list_block_compartment'; eauto; fail);
      try (eapply external_call_block_compartment; eauto; fail).
    - (* step_assign *)
      match goal with AL: assign_loc _ _ _ _ _ _ _ _ _ |- _ =>
        symmetry; exact (assign_loc_block_compartment AL) end.
    - (* step_call/returnstate: set_perm *)
      match goal with SP: (if cp_eq_dec ?a ?b then _ else _) |- _ =>
        destruct (cp_eq_dec a b) in SP; [subst; reflexivity|];
        destruct (cp_eq_dec _ bottom) in SP; [subst; reflexivity|];
        eapply (Mem.set_perm_list_block_compartment _ _ _ _ _ SP) end.
    - (* step_internal_function *)
      match goal with FE: function_entry1 _ _ _ _ _ _ _ |- _ => inv FE end.
      match goal with
        BP: bind_parameters _ _ _ ?m0 _ _ _, AV: alloc_variables _ _ _ _ _ _ ?m0 |- _ =>
        etransitivity;
        [ symmetry; exact (bind_parameters_block_compartment _ _ _ _ _ _ _ _ BP)
        | eapply alloc_variables_block_compartment_old; eauto]
      end.
    - (* step_call/returnstate: set_perm *)
      match goal with SP: (if cp_eq_dec ?a ?b then _ else _) |- _ =>
        destruct (cp_eq_dec a b) in SP; [subst; reflexivity|];
        destruct (cp_eq_dec _ bottom) in SP; [subst; reflexivity|];
        eapply (Mem.set_perm_list_block_compartment _ _ _ _ _ SP) end.
  Qed.

  Lemma state_inv_step ge0 cpm0 st t st':
    step1 cpm0 ge0 st t st' ->
    state_inv ge0 st ->
    state_inv ge0 st'.
  Proof.
    intros STEP [GNP [BLKS [CONT [ENV [CEC ECOMP]]]]].
    split; [| split; [| split; [| split; [| split]]]].
    - eapply gfun_no_perm_step; eauto. eapply state_inv_env_above.
      split; [exact GNP | split; [exact BLKS | split; [exact CONT | split; [exact ENV | exact (conj CEC ECOMP)]]]].
    - eapply same_blocks_step; eauto.
    - (* cont_env_above preserved *)
      inv STEP; simpl in *; eauto;
        try (split; [exact ENV | exact CONT]);
        try (eapply cont_env_above_call_cont; eauto);
        try (destruct CONT as [? ?]; auto).
      eapply find_label_cont_env_above; eauto.
      eapply cont_env_above_call_cont; eauto.
    - (* env_blocks_above for current state *)
      inv STEP; simpl in *; eauto.
      + eapply function_entry1_env_above; eauto.
      + destruct CONT as [? _]; auto.
    - (* cont_env_comp preserved *)
      assert (CEC': cont_env_comp ge0 (memory_of st) (cont_of st')).
      { inv STEP; simpl in *; eauto;
          try (split; [exact ECOMP | exact CEC]);
          try (eapply cont_env_comp_call_cont; eauto);
          try (destruct CEC as [? ?]; auto).
        eapply find_label_cont_env_comp; eauto.
        eapply cont_env_comp_call_cont; eauto. }
      eapply cont_env_comp_mem_eq; eauto.
      + eapply step_block_compartment_valid; eauto.
      + eapply step_valid_block; eauto.
    - (* env_blocks_comp for current state *)
      assert (BC_VB: forall b0, Mem.valid_block (memory_of st) b0 ->
        Mem.block_compartment (memory_of st') b0 = Mem.block_compartment (memory_of st) b0 /\
        Mem.valid_block (memory_of st') b0).
      { intros b0 VB0; split; [eapply step_block_compartment_valid | eapply step_valid_block]; eauto. }
      inv STEP; simpl in *; try exact ECOMP; try exact I.
      all: try (intros b0 lo hi IN; destruct (ECOMP _ _ _ IN) as [BC VB];
                destruct (BC_VB _ VB) as [BC' VB']; split; [congruence | exact VB']; fail).
      + (* step_internal_function *)
        eapply function_entry1_env_comp; eauto.
      + (* step_returnstate *)
        destruct CEC as [BC_CALLER CEC_REST].
        intros b0 lo hi IN. destruct (BC_CALLER _ _ _ IN) as [BC VB].
        destruct (BC_VB _ VB) as [BC' VB']. split; [congruence | exact VB'].
  Qed.

  Lemma initial_state_inv: forall (pr: program) st,
    initial_state pr st ->
    state_inv (globalenv pr) st.
  Proof.
    intros pr st INI. inv INI.
    split; [| split; [| split; [| split; [| split]]]].
    - (* gfun_no_perm *)
      simpl. intros b0 fd DEF ofs k0 perm PERM.
      assert (FP: Genv.find_funct_ptr (Genv.globalenv pr) b0 = Some fd).
      { unfold Genv.find_funct_ptr.
        assert (Genv.find_def (Genv.globalenv pr) b0 = Some (Gfun fd)) as -> by exact DEF.
        reflexivity. }
      eapply Genv.init_mem_characterization_2; eassumption.
    - (* same_blocks *)
      apply init_mem_same_blocks. exact H.
    - (* cont_env_above Kstop *)
      simpl. exact I.
    - (* Callstate => True *)
      exact I.
    - (* cont_env_comp Kstop *)
      simpl. exact I.
    - (* Callstate => True *)
      exact I.
  Qed.

  Lemma state_inv_star (pr: program) s1 t s2:
    Star (semantics1 pr) s1 t s2 ->
    state_inv (globalenv pr) s1 ->
    state_inv (globalenv pr) s2.
  Proof.
    induction 1; eauto.
    intros SI. apply IHstar. eapply state_inv_step. exact H. exact SI.
  Qed.

  (* Extract env_blocks_info shape needed by parallel_abstract_2 *)
  Lemma state_inv_env_blocks_info ge0 st:
    state_inv ge0 st ->
    (match st with
     | State f _ _ e0 _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge0 e0) ->
           Mem.block_compartment (memory_of st) b = comp_of f /\
           Genv.find_def ge0 b = None
     | Returnstate _ (Kcall _ f e0 _ _) _ _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge0 e0) ->
           Mem.block_compartment (memory_of st) b = comp_of f /\
           Genv.find_def ge0 b = None
     | _ => True
     end).
  Proof.
    intros [_ [_ [CONT [ENV [CEC ECOMP]]]]].
    destruct st; simpl in *; auto.
    - intros b lo hi IN.
      destruct (ECOMP _ _ _ IN) as [BC VB].
      split; [exact BC | eapply find_def_above_genv_next; exact (ENV _ _ _ IN)].
    - destruct k; simpl in *; auto.
      destruct CONT as [KENV _].
      destruct CEC as [KCEC _].
      intros b lo hi IN.
      destruct (KCEC _ _ _ IN) as [BC VB].
      split; [exact BC | eapply find_def_above_genv_next; exact (KENV _ _ _ IN)].
  Qed.

  Lemma public_symbol_preserved:
    forall id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id.
  Proof.
    intros id.
    pose proof (Genv.senv_match match_W1_W2) as SM.
    exact (proj1 (proj2 SM) id).
  Qed.

  Lemma allowed_addrof_translated:
    forall cp id,
      s cp = Right ->
      Genv.allowed_addrof ge1 cp id ->
      Genv.allowed_addrof ge2 cp id.
  Proof.
    intros cp0 id0 RIGHT.
    unfold Genv.allowed_addrof, Genv.allowed_addrof_b.
    assert (FS: Genv.find_symbol ge2 id0 = Genv.find_symbol ge1 id0).
    { exact (proj1 (Genv.senv_match match_W1_W2) id0). }
    rewrite FS.
    destruct (Genv.find_symbol ge1 id0) as [b|]; [|auto].
    assert (FD: forall b0,
      option_rel (match_globdef (match_fundef s) match_varinfo tt)
        (Genv.find_def ge1 b0) (Genv.find_def ge2 b0)).
    { intro. exact (Genv.find_def_match_2 match_W1_W2 b0). }
    specialize (FD b).
    destruct (Genv.find_def ge1 b) as [gd1|] eqn:D1;
      destruct (Genv.find_def ge2 b) as [gd2|] eqn:D2;
      inv FD; auto.
    intro H. inv H1.
    - auto.
    - inv H0. auto.
  Qed.

  Lemma genv_cenv_preserved : ge2 = ge1 :> composite_env.
  Proof. symmetry. exact same_cenv. Qed.

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
  intros j0 ge1' ge2' m1 m2 b1 b2 lo hi cp0 m1' RMEMINJ FREE JB.
  destruct RMEMINJ as [DOM MI DZ JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
  exploit Mem.free_parallel_inject; eauto.
  intros (m2' & FREE2 & MI').
  rewrite Z.add_0_r, Z.add_0_r in FREE2.
  exists m2'. split; [exact FREE2 |].
  constructor.
  - eapply same_domain_right_free; eauto.
  - exact MI'.
  - exact DZ.
  - exact JINJ.
  - exact SYMB.
  - exact JPSYMB.
  - eapply same_blocks_free; eauto.
  - eapply same_blocks_free; eauto.
  - intros b1' b2' delta' JB'. rewrite <- (Mem.free_preserves_comp _ _ _ _ _ _ FREE2 b2').
    eauto.
  - exact TGR.
Qed.

Lemma right_mem_injection_free_list_right: forall {j m1 m2 e1 e2 cp m1'},
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

Lemma right_mem_injection_free_list_left:
  forall {j m1 m2 blks cp m1'}
         (RMEMINJ : right_mem_injection s j ge1 ge2 m1 m2)
         (FREE1 : Mem.free_list m1 blks cp = Some m1'),
    right_mem_injection s j ge1 ge2 m1' m2.
Proof.
  intros.
  destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
  split; trivial.
  - eauto using same_domain_right_free_list.
  - eauto using Mem.free_list_left_inject.
  - eauto using same_blocks_free_list.
Qed.

Lemma right_mem_injection_free_list_left':
  forall {j m1 m2 blks cp m2'}
         (RMEMINJ : right_mem_injection s j ge1 ge2 m1 m2)
         (LEFT : s cp = Left)
         (FREE2 : Mem.free_list m2 blks cp = Some m2')
         (BLK_COMP: forall b lo hi, In (b, lo, hi) blks ->
                      Mem.block_compartment m2 b = cp)
         (BLK_NOT_GLOBAL: forall b lo hi, In (b, lo, hi) blks ->
                            Genv.find_def ge2 b = None),
    right_mem_injection s j ge1 ge2 m1 m2'.
Proof.
  intros j m1 m2 blks cp m2' RMEMINJ LEFT FREE2 BLK_COMP BLK_NOT_GLOBAL.
  revert m2 m2' RMEMINJ FREE2 BLK_COMP.
  induction blks as [| [[b lo] hi] blks IH]; intros m2 m2' RMEMINJ FREE2 BLK_COMP.
  - simpl in FREE2. congruence.
  - simpl in FREE2.
    destruct (Mem.free m2 b lo hi cp) as [m2''|] eqn:FREE; [| discriminate].
    assert (BC: Mem.block_compartment m2 b = cp).
    { eapply BLK_COMP. left. reflexivity. }
    assert (OUTSIDE: forall b1 delta ofs k p,
              j b1 = Some (b, delta) ->
              Mem.perm m1 b1 ofs k p ->
              lo <= ofs + delta < hi -> False).
    { intros b1 delta ofs k p jb1 PERM RANGE.
      pose proof (right_side_image _ _ _ _ _ _ RMEMINJ _ _ _ jb1) as RSI.
      rewrite BC in RSI.
      assert (NG: Genv.find_def ge2 b = None).
      { eapply BLK_NOT_GLOBAL. left. reflexivity. }
      destruct RSI as [RSI | RSI]; congruence. }
    assert (RMEMINJ'': right_mem_injection s j ge1 ge2 m1 m2'').
    { destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
      split; trivial.
      - eauto using Mem.free_right_inject.
      - eauto using same_blocks_free.
      - intros b1 b2 delta jb1.
        rewrite <- (free_block_compartment FREE).
        eauto. }
    eapply IH; eauto.
    + intros b0 lo0 hi0 IN.
      eapply BLK_NOT_GLOBAL. right. exact IN.
    + intros b0 lo0 hi0 IN.
      rewrite <- (free_block_compartment FREE).
      eapply BLK_COMP. right. exact IN.
Qed.

  Lemma right_mem_injection_set_perm:
    forall {j m1 m2 b1 b2 p m1' m2'},
    right_mem_injection s j ge1 ge2 m1 m2 ->
    j b1 = Some (b2, 0) ->
    (forall b, j b = Some (b2, 0) -> b = b1) ->
    Mem.set_perm m1 b1 p = Some m1' ->
    Mem.set_perm m2 b2 p = Some m2' ->
    right_mem_injection s j ge1 ge2 m1' m2'.
  Proof.
    intros j m1 m2 b1 b2 p m1' m2' RMEMINJ JB NOALIAS SP1 SP2.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
    constructor.
    - intros b. unfold same_domain_right, in_side in *. simpl in *.
      rewrite (Mem.set_perm_block_compartment' _ _ _ _ _ SP1). exact (DOM b).
    - (* inject j m1' m2' *)
      eapply Mem.inject_perm_change; eauto.
      + exact (Mem.nextblock_set _ _ _ _ SP1).
      + exact (Mem.nextblock_set _ _ _ _ SP2).
      + exact (Mem.set_perm_contents_eq _ _ _ _ SP1).
      + exact (Mem.set_perm_contents_eq _ _ _ _ SP2).
      + intro b0. exact (Mem.set_perm_block_compartment' _ _ _ _ b0 SP1).
      + intro b0. exact (Mem.set_perm_block_compartment' _ _ _ _ b0 SP2).
      + (* Max Nonempty backward on m1' *)
        intros b0 ofs PERM.
        destruct (eq_block b0 b1) as [-> | NEQ].
        * pose proof (Mem.perm_set_same_inv _ _ _ _ SP1 _ _ _ PERM) as [RD _].
          eapply Mem.perm_cur_max in RD. eapply Mem.perm_implies; eauto. constructor.
        * eapply (Mem.perm_set_2' _ _ _ _ SP1); eauto.
      + (* Cur Readable backward on m1' *)
        intros b0 ofs PERM.
        destruct (eq_block b0 b1) as [-> | NEQ].
        * exact (proj1 (Mem.perm_set_same_inv _ _ _ _ SP1 _ _ _ PERM)).
        * eapply (Mem.perm_set_2' _ _ _ _ SP1); eauto.
      + (* FWD: perm m1' b1' → perm m2' b2' *)
        intros b1' b2' delta MAP ofs k q PERM.
        assert (D: delta = 0) by (eapply D0; eauto). subst delta.
        rewrite Z.add_0_r in *.
        destruct (eq_block b1' b1) as [-> | NEQ].
        * rewrite JB in MAP. inv MAP.
          pose proof (Mem.perm_set_same_inv _ _ _ _ SP1 _ _ _ PERM) as [RD PO].
          assert (RD2: Mem.perm m2 b2' (ofs + 0) Cur Readable)
            by (eapply Mem.perm_inject; eauto).
          rewrite Z.add_0_r in RD2.
          eapply Mem.perm_implies.
          { eapply (Mem.perm_set_1 _ _ _ _ SP2); eauto. constructor. }
          exact PO.
        * assert (NEQ2: b2' <> b2).
          { intro E. subst b2'. apply NEQ. apply NOALIAS. exact MAP. }
          eapply (Mem.perm_set_2 _ _ _ _ SP2); eauto.
          assert (PERM1: Mem.perm m1 b1' ofs k q)
            by (eapply (Mem.perm_set_2' _ _ _ _ SP1); eauto).
          assert (H: Mem.perm m2 b2' (ofs + 0) k q)
            by (eapply Mem.perm_inject; eauto).
          rewrite Z.add_0_r in H. exact H.
      + (* BWD: perm m2' b2' → perm m1' b1' ∨ ¬perm m1' Max Nonempty *)
        intros b1' b2' delta MAP ofs k q PERM.
        assert (D: delta = 0) by (eapply D0; eauto). subst delta.
        rewrite Z.add_0_r in *.
        destruct (eq_block b1' b1) as [-> | NEQ].
        * rewrite JB in MAP. inv MAP.
          pose proof (Mem.perm_set_same_inv _ _ _ _ SP2 _ _ _ PERM) as [RD2 PO].
          assert (RD2_0: Mem.perm m2 b2' (ofs + 0) Cur Readable)
            by (rewrite Z.add_0_r; exact RD2).
          destruct (Mem.perm_inject_inv _ _ _ _ _ _ _ _ _ MI JB RD2_0) as [L | R].
          { left. eapply Mem.perm_implies.
            - eapply (Mem.perm_set_1 _ _ _ _ SP1); eauto. constructor.
            - exact PO. }
          { right. intro PERM1'.
            pose proof (Mem.perm_set_same_inv _ _ _ _ SP1 _ _ _ PERM1') as [RD1 _].
            apply R. eapply Mem.perm_cur_max.
            eapply Mem.perm_implies; [exact RD1 | constructor]. }
        * assert (NEQ2: b2' <> b2).
          { intro E. subst b2'. apply NEQ. apply NOALIAS. exact MAP. }
          assert (PERM2: Mem.perm m2 b2' (ofs + 0) k q).
          { rewrite Z.add_0_r. eapply (Mem.perm_set_2' _ _ _ _ SP2); eauto. }
          destruct (Mem.perm_inject_inv _ _ _ _ _ _ _ _ _ MI MAP PERM2) as [L | R].
          { left. eapply (Mem.perm_set_2 _ _ _ _ SP1); eauto. }
          { right. intro PERM1'.
            apply R. eapply (Mem.perm_set_2' _ _ _ _ SP1); eauto. }
    - exact D0.
    - exact JINJ.
    - exact SYMB.
    - exact JPSYMB.
    - constructor.
      + intros b0 gd FIND.
        rewrite (Mem.set_perm_block_compartment' _ _ _ _ b0 SP1).
        eapply same_blocks_comp; eauto.
      + rewrite (Mem.nextblock_set _ _ _ _ SP1).
        exact (same_blocks_next _ _ BLKS1).
    - constructor.
      + intros b0 gd FIND.
        rewrite (Mem.set_perm_block_compartment' _ _ _ _ b0 SP2).
        eapply same_blocks_comp; eauto.
      + rewrite (Mem.nextblock_set _ _ _ _ SP2).
        exact (same_blocks_next _ _ BLKS2).
    - intros b1' b2' delta' JB'.
      rewrite (Mem.set_perm_block_compartment' _ _ _ _ b2' SP2). eauto.
    - exact TGR.
  Qed.

  Lemma right_mem_injection_set_perm_list_right: forall {j m1 m2 e1 e2 p m1'},
    right_mem_injection s j ge1 ge2 m1 m2 ->
    right_env_injection j e1 e2 ->
    (forall b1 b1' b2, j b1 = Some (b2, 0) -> j b1' = Some (b2, 0) -> b1 = b1') ->
    Mem.set_perm_list m1 (blocks_of_env ge1 e1) p = Some m1' ->
    exists m2',
      Mem.set_perm_list m2 (blocks_of_env ge2 e2) p = Some m2' /\
      right_mem_injection s j ge1 ge2 m1' m2'.
  Proof.
    intros j m1 m2 e1 e2 p m1' RMEMINJ ENVINJ JINJ SPL1.
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
    clear ENVINJ ENVINJ'. revert ENVINJ'' m1 m2 RMEMINJ SPL1.
    generalize (PTree.elements e1) (PTree.elements e2). clear e1 e2.
    intros e1 e2 EI.
    induction EI as [|(id & b1 & ty) e1 (id' & b2 & ty') e2 (? & j_b1 & ?) _ IH].
    { intros. simpl in *. exists m2; split; congruence. }
    intros m1 m2 RMEMINJ SPL1. simpl in *. subst id' ty'.
    destruct (Mem.set_perm m1 b1 p) as [m1''|] eqn:SP1; try discriminate.
    (* set_perm succeeds on m2 for b2 because b2 is valid *)
    assert (VB2: Mem.valid_block m2 b2).
    { eapply Mem.valid_block_inject_2; eauto.
      exact (partial_mem_inject _ _ _ _ _ _ RMEMINJ). }
    assert (exists m2'', Mem.set_perm m2 b2 p = Some m2'') as [m2'' SP2].
    { unfold Mem.set_perm. destruct (plt b2 (Mem.nextblock m2)); [eexists; eauto | contradiction]. }
    assert (RMEMINJ'': right_mem_injection s j ge1 ge2 m1'' m2'').
    { eapply right_mem_injection_set_perm; eauto. }
    destruct (IH _ _ RMEMINJ'' SPL1) as (m2' & SPL2 & RMEMINJ').
    exists m2'. rewrite SP2. split; assumption.
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

   *)
  Lemma eval_expr_lvalue_injection:
    forall s j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall (CP_RIGHT: s cp = Right),
    forall (CP_NOT_TOP: cp <> top),
    (forall a v,
      eval_expr ge1 e1 cp le1 m1 a v ->
      (* forall loc ofs (EQv: v = Vptr loc ofs), *)
      exists v', Val.inject j v v' /\
                   eval_expr ge2 e2 cp le2 m2 a v')
    /\
    (forall a loc ofs bf,
      eval_lvalue ge1 e1 cp le1 m1 a loc ofs bf ->
      exists loc' ofs',
        j loc = Some (loc', ofs') /\
        eval_lvalue ge2 e2 cp le2 m2 a loc' (Ptrofs.add ofs (Ptrofs.repr ofs')) bf).
  Proof.
    intros s0 j0 m1 m2 e1 e2 le1 le2 cp0 inj env_inj lenv_inj CP_RIGHT CP_NOT_TOP.
    apply eval_expr_lvalue_ind.
    (* eval_expr cases *)
    - (* Econst_int *)
      intros. exists (Vint i). split; [constructor | constructor].
    - (* Econst_float *)
      intros. exists (Vfloat f). split; [constructor | constructor].
    - (* Econst_single *)
      intros. exists (Vsingle f). split; [constructor | constructor].
    - (* Econst_long *)
      intros. exists (Vlong i). split; [constructor | constructor].
    - (* Etempvar *)
      intros id ty v LE_ID.
      exploit lenv_inj; eauto. intros [v' [VINJ LE2]].
      exists v'. split; auto. constructor; auto.
    - (* Eaddrof *)
      intros a ty loc ofs EVAL IH.
      destruct IH as [loc' [ofs' [JB LV2]]].
      exists (Vptr loc' (Ptrofs.add ofs (Ptrofs.repr ofs'))).
      split; [econstructor; eauto | econstructor; eauto].
    - (* Eunop *)
      intros op a ty v1 v EVAL IH SEM.
      destruct IH as [tv1 [INJ1 EV1]].
      exploit sem_unary_operation_inject; eauto.
      { exact (partial_mem_inject _ _ _ _ _ _ inj). }
      intros [tv [SEM2 INJ2]].
      exists tv. split; auto. econstructor; eauto.
    - (* Ebinop *)
      intros op a1 a2 ty v1 v2 v EVAL1 IH1 EVAL2 IH2 SEM.
      destruct IH1 as [tv1 [INJ1 EV1]].
      destruct IH2 as [tv2 [INJ2 EV2]].
      exploit sem_binary_operation_inject; eauto.
      { exact (partial_mem_inject _ _ _ _ _ _ inj). }
      intros [tv [SEM2 INJ3]].
      exists tv. split; auto. econstructor; eauto.
      congruence.
    - (* Ecast *)
      intros a ty v1 v EVAL IH SEM.
      destruct IH as [tv1 [INJ1 EV1]].
      exploit sem_cast_inject; eauto.
      { exact (partial_mem_inject _ _ _ _ _ _ inj). }
      intros [tv [SEM2 INJ2]].
      exists tv. split; auto. econstructor; eauto.
    - (* Esizeof *)
      intros ty1 ty.
      exists (Vptrofs (Ptrofs.repr (sizeof ge1 ty1))).
      split.
      + unfold Vptrofs; destruct Archi.ptr64; constructor.
      + replace (sizeof ge1 ty1) with (sizeof ge2 ty1) by congruence. constructor.
    - (* Ealignof *)
      intros ty1 ty.
      exists (Vptrofs (Ptrofs.repr (alignof ge1 ty1))).
      split.
      + unfold Vptrofs; destruct Archi.ptr64; constructor.
      + replace (alignof ge1 ty1) with (alignof ge2 ty1) by congruence. constructor.
    - (* Elvalue — rval from lvalue *)
      intros a loc ofs bf v EVAL_LV IH DEREF.
      destruct IH as [loc' [delta [JB LV2]]].
      assert (VINJ: Val.inject j0 (Vptr loc ofs) (Vptr loc' (Ptrofs.add ofs (Ptrofs.repr delta)))).
      { econstructor; eauto. }
      inv DEREF.
      + (* deref_loc_value *)
        exploit Mem.loadv_inject; eauto.
        { exact (partial_mem_inject _ _ _ _ _ _ inj). }
        intros [tv [LOAD2 VINJ2]].
        exists tv. split; auto. eapply eval_Elvalue; eauto.
        eapply deref_loc_value; eauto.
      + (* deref_loc_reference *)
        exists (Vptr loc' (Ptrofs.add ofs (Ptrofs.repr delta))).
        split; auto. eapply eval_Elvalue; eauto.
        eapply deref_loc_reference; eauto.
      + (* deref_loc_copy *)
        exists (Vptr loc' (Ptrofs.add ofs (Ptrofs.repr delta))).
        split; auto. eapply eval_Elvalue; eauto.
        eapply deref_loc_copy; eauto.
      + (* deref_loc_bitfield *)
        inv H.
        exploit Mem.loadv_inject; eauto.
        { exact (partial_mem_inject _ _ _ _ _ _ inj). }
        intros [tc [LOAD2 BINJ]]. inv BINJ.
        econstructor. split.
        { constructor. }
        eapply eval_Elvalue; eauto.
        eapply deref_loc_bitfield. rewrite <- H0. econstructor; eauto.
    (* eval_lvalue cases *)
    - (* Evar_local *)
      intros id l ty ENV.
      destruct env_inj as [SOME_INJ NONE_INJ].
      exploit SOME_INJ; eauto. intros [b' [JB E2]].
      exists b', 0%Z. split; auto.
      rewrite Ptrofs.add_zero. constructor; auto.
    - (* Evar_global *)
      intros id l ty ENV SYM AADDR.
      destruct env_inj as [_ NONE_INJ].
      assert (ENV2: e2 ! id = None) by (apply NONE_INJ; auto).
      (* l has a def, so j maps it *)
      assert (J_L: j0 l <> None).
      { apply (same_dom _ _ _ _ _ _ inj).
        assert (SYM' : Genv.find_symbol (Genv.globalenv W1) id = Some l) by exact SYM.
        pose proof (Genv.find_symbol_find_def_inversion _ _ SYM') as [gd DEF].
        destruct gd as [fd | v].
        - right. exists fd. exact DEF.
        - (* Gvar: allowed_addrof ensures comp_of v flows to cp0.
             Since comp_of v <> bottom and cp0 <> top, flowsto gives comp_of v = cp0.
             Since s cp0 = Right, the variable block is Right-side. *)
          left. simpl.
          assert (DEF': Genv.find_def ge1 l = Some (Gvar v)) by exact DEF.
          rewrite (same_blocks_comp _ _ (same_blks1 _ _ _ _ _ _ inj) _ _ DEF').
          simpl.
          (* AADDR gives flowsto (comp_of v) cp0 after unfolding *)
          unfold Genv.allowed_addrof, Genv.allowed_addrof_b in AADDR.
          rewrite SYM in AADDR. rewrite DEF' in AADDR.
          destruct (flowsto_dec (comp_of (Gvar v)) cp0) as [FLOW|]; [| discriminate].
          simpl in FLOW.
          assert (comp_of v = cp0).
          { apply flowsto_no_bottom_no_top; trivial.
            eapply no_bottom_var_W1; exact DEF'. }
          congruence. }
      destruct (j0 l) as [[l' delta]|] eqn:JB; [|congruence].
      assert (DELTA: delta = 0) by (eapply (j_delta_zero _ _ _ _ _ _ inj); eauto).
      subst delta.
      (* Get find_symbol ge2 *)
      assert (SYM2: Genv.find_symbol ge2 id = Some l').
      { exact (proj2 (j_preserves_symbols _ _ _ _ _ _ inj _ _ _ _ JB SYM)). }
      (* allowed_addrof preserved *)
      assert (AADDR2: Genv.allowed_addrof ge2 cp0 id).
      { apply (Genv.match_genvs_allowed_addrof match_W1_W2). exact AADDR. }
      exists l', 0%Z. split; auto.
      rewrite Ptrofs.add_zero. eapply eval_Evar_global; eauto.
    - (* Ederef *)
      intros a ty l ofs EVAL IH.
      destruct IH as [tv [VINJ EV2]]. inv VINJ.
      exists b2, delta. split; auto.
      constructor. exact EV2.
    - (* Efield_struct *)
      intros a i ty l ofs id0 co att delta0 bf EVAL IH TYPEOF CENV FOFF.
      destruct IH as [tv [VINJ EV2]]. inv VINJ.
      exists b2, delta. split; auto.
      replace (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr delta0)) (Ptrofs.repr delta))
        with (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr delta)) (Ptrofs.repr delta0))
        by (rewrite !Ptrofs.add_assoc; f_equal; apply Ptrofs.add_commut).
      eapply eval_Efield_struct; eauto.
      + exact (eq_ind _ (fun ce => ce ! id0 = Some co) CENV _ same_cenv).
      + exact (eq_ind _ (fun ce => field_offset ce i (co_members co) = OK (delta0, bf)) FOFF _ same_cenv).
    - (* Efield_union *)
      intros a i ty l ofs id0 co att delta0 bf EVAL IH TYPEOF CENV UOFF.
      destruct IH as [tv [VINJ EV2]]. inv VINJ.
      exists b2, delta. split; auto.
      replace (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr delta0)) (Ptrofs.repr delta))
        with (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr delta)) (Ptrofs.repr delta0))
        by (rewrite !Ptrofs.add_assoc; f_equal; apply Ptrofs.add_commut).
      eapply eval_Efield_union; eauto.
      + exact (eq_ind _ (fun ce => ce ! id0 = Some co) CENV _ same_cenv).
      + exact (eq_ind _ (fun ce => union_field_offset ce i (co_members co) = OK (delta0, bf)) UOFF _ same_cenv).
  Qed.

  Lemma eval_expr_injection:
    forall s j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall (CP_RIGHT: s cp = Right) (CP_NOT_TOP: cp <> top),
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
    forall s j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall (CP_RIGHT: s cp = Right) (CP_NOT_TOP: cp <> top),
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
    forall s j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall (CP_RIGHT: s cp = Right) (CP_NOT_TOP: cp <> top),
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
        destruct H as [same_dom mem_inject delta_zero ? same_symb j_psymb blks1 blks2 rsi tgr]
    end.

  Lemma find_funct_preserved j0 fd v v' cp :
    s (comp_of fd) = Right ->
    Val.inject j0 v v' ->
    symbols_inject j0 ge1 ge2 cp ->
    Genv.find_funct ge1 v = Some fd ->
    Genv.find_funct ge2 v' = Some fd.
  Proof.
    unfold Genv.find_funct. intros s_cp v_inj symbs_inj.
    case v_inj; try congruence. clear v_inj.
    intros b ofs b' _ delta j_b ->.
    destruct Ptrofs.eq_dec as [?|_]; try congruence. subst ofs.
    intros ge1_b.
    apply Genv.find_funct_ptr_iff in ge1_b.
    assert (exists id, Genv.find_symbol ge1 id = Some b) as [id ge1_id].
    { eapply Genv.find_def_find_symbol_inversion; eauto.
      exact W1_norepet. }
    assert (delta = 0 /\ Genv.find_symbol ge2 id = Some b') as [? ge2_id].
    { destruct symbs_inj as (_ & inj & _); eapply inj; eauto. }
    subst delta.
    rewrite Ptrofs.add_zero_l. unfold Ptrofs.zero.
    destruct Ptrofs.eq_dec as [_|?]; try congruence.
    (* Now we know find_def ge1 b = Some (Gfun fd) and find_symbol ge2 id = Some b' *)
    (* Use find_def_match_2 to relate ge1 and ge2 definitions *)
    pose proof (Genv.find_def_match_2 match_W1_W2 b) as REL.
    assert (REL': option_rel (match_globdef (match_fundef s) match_varinfo tt)
      (Genv.find_def ge1 b) (Genv.find_def ge2 b)) by exact REL.
    clear REL. rename REL' into REL.
    (* find_symbol ge2 id = Some b' and find_symbol ge1 id = Some b *)
    (* From senv_match, find_symbol ge2 = find_symbol ge1, so b' = b *)
    assert (FS: Genv.find_symbol ge2 id = Genv.find_symbol ge1 id).
    { exact (proj1 (Genv.senv_match match_W1_W2) id). }
    assert (b' = b) by congruence. subst b'.
    (* From find_def_match_2, find_def ge2 b matches find_def ge1 b *)
    assert (Genv.find_def ge2 b = Some (Gfun fd)).
    { rewrite ge1_b in REL.
      destruct (Genv.find_def ge2 b) as [gd2|] eqn:D2; inv REL.
      repeat match goal with
      | H: match_globdef _ _ _ _ _ |- _ => inv H
      end.
      f_equal. inv H2; try reflexivity.
      simpl in s_cp. congruence. }
    unfold Genv.find_funct_ptr. rewrite H. reflexivity.
  Qed.

  Lemma find_funct_preserved_bottom j0 fd v v' cp :
    comp_of fd = bottom ->
    Val.inject j0 v v' ->
    symbols_inject j0 ge1 ge2 cp ->
    Genv.find_funct ge1 v = Some fd ->
    Genv.find_funct ge2 v' = Some fd.
  Proof.
    unfold Genv.find_funct. intros BOTTOM v_inj symbs_inj.
    case v_inj; try congruence. clear v_inj.
    intros b ofs b' _ delta j_b ->.
    destruct Ptrofs.eq_dec as [?|_]; try congruence. subst ofs.
    intros ge1_b.
    apply Genv.find_funct_ptr_iff in ge1_b.
    assert (exists id, Genv.find_symbol ge1 id = Some b) as [id ge1_id].
    { eapply Genv.find_def_find_symbol_inversion; eauto.
      exact W1_norepet. }
    assert (delta = 0 /\ Genv.find_symbol ge2 id = Some b') as [? ge2_id].
    { destruct symbs_inj as (_ & inj & _); eapply inj; eauto. }
    subst delta.
    rewrite Ptrofs.add_zero_l. unfold Ptrofs.zero.
    destruct Ptrofs.eq_dec as [_|?]; try congruence.
    pose proof (Genv.find_def_match_2 match_W1_W2 b) as REL.
    assert (REL': option_rel (match_globdef (match_fundef s) match_varinfo tt)
      (Genv.find_def ge1 b) (Genv.find_def ge2 b)) by exact REL.
    clear REL. rename REL' into REL.
    assert (FS: Genv.find_symbol ge2 id = Genv.find_symbol ge1 id).
    { exact (proj1 (Genv.senv_match match_W1_W2) id). }
    assert (b' = b) by congruence. subst b'.
    assert (Genv.find_def ge2 b = Some (Gfun fd)).
    { rewrite ge1_b in REL.
      destruct (Genv.find_def ge2 b) as [gd2|] eqn:D2; inv REL.
      repeat match goal with
      | H: match_globdef _ _ _ _ _ |- _ => inv H
      end.
      f_equal. inv H2; try reflexivity.
      (* match_function_left: fd = Internal f with comp_of f = bottom *)
      (* But no_bottom_W1 says Internal functions can't have comp bottom *)
      exfalso.
      eapply no_bottom_W1; [exact ge1_b | simpl; exact BOTTOM]. }
    unfold Genv.find_funct_ptr. rewrite H. reflexivity.
  Qed.

  Lemma find_comp_of_block_preserved j m1 m2 b1 b2 delta id cp :
    right_mem_injection s j ge1 ge2 m1 m2 ->
    j b1 = Some (b2, delta) ->
    Genv.find_comp_of_block ge1 b1 = cp ->
    Genv.find_symbol ge1 id = Some b1 ->
    Genv.find_symbol ge2 id = Some b2 ->
    Genv.find_comp_of_block ge2 b2 = cp.
  Proof.
    intros RMEMINJ JB COMP SYM1 SYM2.
    assert (FS: Genv.find_symbol ge2 id = Genv.find_symbol ge1 id).
    { exact (proj1 (Genv.senv_match match_W1_W2) id). }
    assert (b2 = b1) as -> by congruence.
    assert (FC: Genv.find_comp_of_ident ge2 id = Genv.find_comp_of_ident ge1 id).
    { exact (Genv.find_comp_match match_W1_W2 id). }
    unfold Genv.find_comp_of_ident in FC.
    rewrite SYM1 in FC. rewrite SYM2 in FC.
    congruence.
  Qed.

  Lemma allowed_call_preserved : forall j cp m1 m2 b ofs vf2,
      right_mem_injection s j ge1 ge2 m1 m2 ->
      (forall b, j b <> None -> exists id, Genv.invert_symbol ge1 b = Some id) ->
      Val.inject j (Vptr b ofs) vf2 ->
      Genv.allowed_call ge1 cp (Vptr b ofs) ->
      Genv.allowed_call ge2 cp vf2.
  Proof.
    intros j cp m1 m2 b ofs vf2 RMEMINJ JHAS_SYM VINJ CALL1.
    inv VINJ.
    rename H1 into JB.
    pose proof (j_delta_zero _ _ _ _ _ _ RMEMINJ _ _ _ JB) as DELTA. subst delta.
    assert (b = b2).
    { assert (JB' : j b <> None) by congruence.
      destruct (JHAS_SYM b JB') as [id INV].
      apply Genv.invert_find_symbol in INV.
      pose proof (j_preserves_symbols _ _ _ _ _ _ RMEMINJ _ _ _ _ JB INV) as [_ SYM2].
      assert (FS: Genv.find_symbol ge2 id = Genv.find_symbol ge1 id).
      { exact (proj1 (Genv.senv_match match_W1_W2) id). }
      congruence. }
    subst b2. rewrite Ptrofs.add_zero.
    eapply (Genv.match_genvs_allowed_calls match_W1_W2). exact CALL1.
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
    intros j0 m1 m2 id0 b1 b2 delta RMEMINJ SYM1 JB.
    destruct RMEMINJ as [_ _ _ _ _ JPSYMB _ _ _].
    exact (proj2 (JPSYMB _ _ _ _ JB SYM1)).
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
    unfold Mem.valid_block.
    eapply Plt_Ple_trans; [| exact (same_blocks_next _ _ BLKS)].
    eapply Genv.genv_symb_range; eauto.
  Qed.

  Lemma block_is_volatile_valid_block p m b :
    same_blocks (globalenv p) m ->
    Genv.block_is_volatile (globalenv p) b = true ->
    Mem.valid_block m b.
  Proof.
    intros BLKS VOL.
    unfold Mem.valid_block.
    eapply Plt_Ple_trans; [| exact (same_blocks_next _ _ BLKS)].
    eapply Genv.block_is_volatile_below; eauto.
  Qed.

  (* FIXME: This name is wrong: it is too specific to the case of allocating a
     new parameter *)
  Lemma right_mem_injection_alloc_right {j cp m1 m2 e1 e2 le1 le2 m1' b1 ty} id
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (RENVINJ: right_env_injection j e1 e2)
    (RTENVINJ: right_tenv_injection j le1 le2)
    (RIGHT: s cp = Right)
    (ALLOC: Mem.alloc m1 cp 0 (sizeof ge1 ty) = (m1', b1)):
    exists j' m2' b2,
      Mem.alloc m2 cp 0 (sizeof ge2 ty) = (m2', b2) /\
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
    rewrite sizeof_preserved.
    split; [exact ALLOC2' | split; [| split; [| split]]].
    - destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
      constructor.
      + (* same_domain_right *)
        intros b. specialize (DOM b).
        simpl in *.
        rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC).
        destruct eq_block as [<-|b_b1].
        { rewrite ZERO. split; [intros _; left; exact RIGHT | congruence]. }
        now rewrite EXT; trivial.
      + (* inject *) exact INJ.
      + (* delta_zero *)
        intros b1' b2' delta j'_b1.
        destruct (peq b1' b1) as [-> | NEQ].
        * rewrite ZERO in j'_b1. injection j'_b1 as <- <-. reflexivity.
        * rewrite EXT in j'_b1; [| assumption]. eauto.
      + (* j_injective *)
        intros b1a b1b b2a j'_b1a j'_b1b.
        destruct (peq b1a b1) as [->|NEQa]; destruct (peq b1b b1) as [->|NEQb].
        * reflexivity.
        * rewrite ZERO in j'_b1a. injection j'_b1a as <-.
          rewrite EXT in j'_b1b; [| assumption].
          exfalso. eapply Mem.fresh_block_alloc; [exact ALLOC2'|].
          eapply Mem.mi_mappedblocks; eauto.
        * rewrite ZERO in j'_b1b. injection j'_b1b as <-.
          rewrite EXT in j'_b1a; [| assumption].
          exfalso. eapply Mem.fresh_block_alloc; [exact ALLOC2'|].
          eapply Mem.mi_mappedblocks; eauto.
        * rewrite EXT in j'_b1a, j'_b1b; [| assumption | assumption].
          eauto.
      + (* symbols_inject *)
        intros cp0 RIGHT_CP. specialize (SYMB cp0 RIGHT_CP).
        destruct SYMB as (S1 & S2 & S3 & S4 & S5).
        split; [|split; [|split; [|split]]]; auto.
        * intros id0 b1' b2' delta j'_b1' SYM.
          destruct (peq b1' b1) as [->|NEQ].
          { exfalso. eapply Mem.fresh_block_alloc; [exact ALLOC|].
            eapply find_symbol_valid_block; [exact BLKS1|]. exact SYM. }
          rewrite EXT in j'_b1'; [|assumption]. eauto.
        * intros id0 b1' PUB SYM COMP.
          destruct (S3 id0 b1' PUB SYM COMP) as (b2' & j_b1' & SYM2).
          exists b2'. split; [|assumption]. apply INCR. assumption.
        * intros b1' b2' delta j'_b1'.
          destruct (peq b1' b1) as [->|NEQ].
          { rewrite ZERO in j'_b1'. injection j'_b1' as <- <-.
            assert (~ Mem.valid_block m1 b1) by (eapply Mem.fresh_block_alloc; eauto).
            assert (~ Mem.valid_block m2 b2) by (eapply Mem.fresh_block_alloc; eauto).
            assert (Senv.block_is_volatile ge1 b1 = false) as ->.
            { destruct Senv.block_is_volatile eqn:V; trivial.
              exfalso. apply H. eapply block_is_volatile_valid_block; eauto. }
            assert (Senv.block_is_volatile ge2 b2 = false) as ->.
            { destruct Senv.block_is_volatile eqn:V; trivial.
              exfalso. apply H0. eapply block_is_volatile_valid_block; eauto. }
            reflexivity. }
          rewrite EXT in j'_b1'; [|assumption]. eauto.
      + (* j_preserves_symbols *)
        intros id0 b1' b2' delta j'_b1' SYM.
        destruct (peq b1' b1) as [->|NEQ].
        { exfalso. eapply Mem.fresh_block_alloc; [exact ALLOC|].
          eapply find_symbol_valid_block; [exact BLKS1|]. exact SYM. }
        rewrite EXT in j'_b1'; [|assumption]. eauto.
      + eapply same_blocks_alloc; eauto.
      + eapply same_blocks_alloc; eauto.
      + (* right_side_image *)
        intros b1' b2' delta j'_b1.
        destruct (peq b1' b1) as [-> | NEQ].
        * rewrite ZERO in j'_b1. injection j'_b1 as <- <-.
          rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC2').
          destruct eq_block; [left; exact RIGHT | contradiction].
        * rewrite EXT in j'_b1; [| assumption].
          rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC2').
          destruct eq_block as [->|].
          { exfalso. eapply Mem.fresh_block_alloc; [exact ALLOC2'|].
            eapply Mem.mi_mappedblocks; eauto. }
          eauto.
      + (* target_gvar_right *)
        intros b1' b2' delta gv j'_b1 FDEF2.
        destruct (peq b1' b1) as [->|NEQ].
        * rewrite ZERO in j'_b1. injection j'_b1 as <- <-.
          exfalso. eapply Mem.fresh_block_alloc; [exact ALLOC2'|].
          eapply Pos.lt_le_trans.
          { eapply Genv.genv_defs_range. unfold Genv.find_def in FDEF2. exact FDEF2. }
          exact (same_blocks_next _ _ BLKS2).
        * rewrite EXT in j'_b1; [| assumption]. eapply TGR; eauto.
    - exact INCR.
    - (* right_env_injection *)
      destruct RENVINJ as [ENVSOME ENVNONE]. split.
      + intros id' b ty' GET.
        destruct (peq id' id) as [-> | NEQ].
        * rewrite PTree.gss. rewrite PTree.gss in GET.
          injection GET as <- <-.
          eauto.
        * rewrite PTree.gso; [| assumption].
          rewrite PTree.gso in GET; [| assumption].
          destruct (ENVSOME id' b ty' GET) as (b' & b_b' & id'_b').
          eauto.
      + intros id' GET.
        destruct (peq id' id) as [-> | NEQ].
        * rewrite PTree.gss in GET. discriminate.
        * rewrite PTree.gso; [| assumption].
          rewrite PTree.gso in GET; [| assumption].
          eauto.
    - (* right_tenv_injection *)
      intros id' v GET. specialize (RTENVINJ id' v GET) as (v' & INJ' & GET').
      exists v'. split; [| assumption].
      eapply val_inject_incr; eauto.
  Qed.

  Lemma same_domain_right_alloc_left :
    forall j ge m cp lo hi m' b,
      same_domain_right s j ge m ->
      Mem.alloc m cp lo hi = (m', b) ->
      s cp = Left ->
      (forall b0, ~Mem.valid_block m b0 -> j b0 = None) ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      same_domain_right s j ge m'.
  Proof.
    intros j0 ge m cp lo hi m' b SDR ALLOC LEFT FREEBLOCKS GE_NEXT b'.
    specialize (SDR b'). simpl in *.
    rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC).
    destruct eq_block as [->|?].
    - (* b' = b: fresh block *)
      rewrite LEFT. split.
      + intros Hne.
        assert (j0 b = None) by (apply FREEBLOCKS; eapply Mem.fresh_block_alloc; eauto).
        congruence.
      + intros [|[fd FD]]; [discriminate|].
        exfalso.
        apply Genv.genv_defs_range in FD.
        assert (b = Mem.nextblock m) by (eapply Mem.alloc_result; eauto).
        subst b. unfold Plt, Ple in *. lia.
    - exact SDR.
  Qed.

  Lemma right_mem_injection_alloc_left {j cp m1 m2 m1' b1 lo hi}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (LEFT: s cp = Left)
    (ALLOC: Mem.alloc m1 cp lo hi = (m1', b1)):
    right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
    split; trivial.
    - eapply same_domain_right_alloc_left; eauto.
      + eapply Mem.mi_freeblocks; eauto.
      + exact (same_blocks_next _ _ BLKS1).
    - eauto using Mem.alloc_left_unmapped_inject_strong.
    - eauto using same_blocks_alloc.
  Qed.

  Lemma right_mem_injection_alloc_left' {j cp m1 m2 m2' b2 lo hi}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (LEFT: s cp = Left)
    (ALLOC: Mem.alloc m2 cp lo hi = (m2', b2)):
    right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
    split; trivial.
    - eauto using Mem.alloc_right_inject.
    - eauto using same_blocks_alloc.
    - intros b1' b2' delta' JB'.
      assert (b2' <> b2).
      { intro; subst. exploit Mem.mi_mappedblocks; eauto. intro VB.
        exploit Mem.alloc_result; eauto. intro; subst.
        eapply Mem.fresh_block_alloc; eauto. }
      rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC).
      destruct eq_block; [congruence | eauto].
  Qed.

  Lemma right_mem_injection_alloc_variables_right
    {j f m1 m1' m2 e1 e1' e2 le1 le2 vars}
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
    - destruct (right_mem_injection_alloc_right id RMEMINJ RENVINJ RTENVINJ RIGHT H)
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

  Lemma right_mem_injection_alloc_variables_left
    {j cp m1 m1' m2 e1 e1' vars}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (LEFT: s cp = Left)
    (ALLOC: alloc_variables ge1 cp e1 m1 vars e1' m1'):
    right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    induction ALLOC as [
        e1 m1
      | e1 m1 id ty vars m1' b1 m1'' e1' ALLOC _ IH]; trivial.
    eauto using right_mem_injection_alloc_left.
  Qed.

  Lemma right_mem_injection_alloc_variables_left'
    {j cp m1 m2 m2' e2 e2' vars}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (LEFT: s cp = Left)
    (ALLOC: alloc_variables ge2 cp e2 m2 vars e2' m2'):
    right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    induction ALLOC as [
        e2 m2
      | e2 m2 id ty vars m2' b1 m2'' e2' ALLOC _ IH]; trivial.
    eauto using right_mem_injection_alloc_left'.
  Qed.

  Lemma right_mem_injection_store_mapped {j chunk m1 m2 b1 b2 ofs v1 v2 cp m1'} :
    forall (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (LOCINJ: j b1 = Some (b2, 0))
           (VALINJ: Val.inject j v1 v2)
           (STORE1: Mem.store chunk m1 b1 ofs v1 cp = Some m1'),
    exists m2',
      Mem.store chunk m2 b2 ofs v2 cp = Some m2' /\
      right_mem_injection s j ge1 ge2 m1' m2'.
  Proof.
    intros.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
    exploit Mem.store_mapped_inject; eauto.
    rewrite Z.add_0_r. intros (m2' & STORE2 & INJ').
    exists m2'; split; trivial. constructor; trivial;
    try solve [eauto using same_domain_right_store, same_blocks_store].
    intros b1' b2' delta' JB'.
    rewrite (Mem.store_block_compartment _ _ _ _ _ _ _ STORE2 b2'). eauto.
  Qed.

  Lemma right_mem_injection_store_unmapped :
    forall {j chunk m1 m2 b1 ofs v1 cp m1'}
           (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (LOCINJ: j b1 = None)
           (STORE1: Mem.store chunk m1 b1 ofs v1 cp = Some m1'),
      right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    intros.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
    exploit Mem.store_unmapped_inject; eauto.
    intros MI'.
    constructor; trivial;
    eauto using same_domain_right_store, same_blocks_store.
  Qed.

  Lemma right_mem_injection_store_outside :
    forall {j m1 chunk m2 b2 ofs v2 cp m2'}
           (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (LOCINJ: forall b delta, j b <> Some (b2, delta))
           (STORE2: Mem.store chunk m2 b2 ofs v2 cp = Some m2'),
      right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    intros.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
    exploit Mem.store_outside_inject; eauto.
    { intros ??? INJ. destruct (LOCINJ _ _ INJ). }
    intros MI'.
    constructor; trivial; try solve [eauto using same_blocks_store].
    intros b1' b2' delta' JB'.
    rewrite (Mem.store_block_compartment _ _ _ _ _ _ _ STORE2 b2'). eauto.
  Qed.

  Lemma right_mem_injection_storebytes_mapped
    {j m1 m2 b1 b2 ofs bytes1 bytes2 cp m1'} :
    forall (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (LOCINJ: j b1 = Some (b2, 0))
           (BYTESINJ: list_forall2 (memval_inject j) bytes1 bytes2)
           (STORE1: Mem.storebytes m1 b1 ofs bytes1 cp = Some m1'),
    exists m2',
      Mem.storebytes m2 b2 ofs bytes2 cp = Some m2' /\
      right_mem_injection s j ge1 ge2 m1' m2'.
  Proof.
    intros [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR] b1_b2 BYTESINJ STORE1.
    exploit Mem.storebytes_mapped_inject; eauto.
    rewrite Z.add_0_r. intros (m2' & STORE2 & MI').
    exists m2'. split; trivial.
    constructor;
    try solve [eauto using same_domain_right_storebytes, same_blocks_storebytes].
    intros b1' b2' delta' JB'.
    rewrite (Mem.storebytes_block_compartment _ _ _ _ _ _ STORE2 b2'). eauto.
  Qed.

  Lemma right_mem_injection_storebytes_unmapped
    {j m1 m2 b1 ofs bytes1 cp m1'} :
    forall (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (LOCINJ: j b1 = None)
           (STORE1: Mem.storebytes m1 b1 ofs bytes1 cp = Some m1'),
      right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    intros [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR] LOCINJ STORE1.
    exploit Mem.storebytes_unmapped_inject; eauto. intros MI'.
    constructor;
    eauto using same_domain_right_storebytes, same_blocks_storebytes.
  Qed.

  Lemma right_mem_injection_storebytes_outside
    {j m1 m2 b2 ofs bytes2 cp m2'} :
    forall (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (LOCINJ: forall b delta, j b <> Some (b2, delta))
           (STORE1: Mem.storebytes m2 b2 ofs bytes2 cp = Some m2'),
      right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    intros [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR] LOCINJ STORE2.
    exploit Mem.storebytes_outside_inject; eauto.
    { intros. eapply LOCINJ. eauto. }
    constructor;
    try solve [eauto using same_domain_right_storebytes, same_blocks_storebytes].
    intros b1' b2' delta' JB'.
    rewrite (Mem.storebytes_block_compartment _ _ _ _ _ _ STORE2 b2'). eauto.
  Qed.

Lemma same_domain_right_assign_loc
        ge0 ge j cp ty m b ofs bf v m' :
  assign_loc ge cp ty m b ofs bf v m' ->
  same_domain_right s j ge0 m ->
  same_domain_right s j ge0 m'.
Proof.
  intros ASSIGN DOM.
  destruct ASSIGN as [
      v chunk m' ACCESS STORE
    | b' ofs' bytes m' ACCESS H1 H2 H3 LOAD STORE
    | v sz sg pos width m' v' STORE ].
  - eapply same_domain_right_store in STORE; eauto.
  - eapply same_domain_right_storebytes in STORE; eauto.
  - remember (Vptr b ofs) as addr1 eqn:Eaddr1.
    destruct STORE as
      [ sz sg1 attr sg pos width m addr c' n m' cp
          pos_0 width_bounds pos_width sg_eq LOAD STORE
      ]; subst addr.
    eapply same_domain_right_store in STORE; eauto.
Qed.

  Lemma right_mem_injection_assign_loc_mapped
    {j m1 m1' m2 ofs bf v1 v2 ty b1 b2 cp}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (LOCINJ: j b1 = Some (b2, 0))
    (VALINJ: Val.inject j v1 v2)
    (ASSIGN1: assign_loc ge1 cp ty m1 b1 ofs bf v1 m1'):
    exists m2',
      assign_loc ge2 cp ty m2 b2 ofs bf v2 m2' /\
      right_mem_injection s j ge1 ge2 m1' m2'.
  Proof.
    assert (Val.inject j (Vptr b1 ofs) (Vptr b2 ofs)) as LOCINJ'.
    { econstructor; eauto. now rewrite Ptrofs.add_zero. }
    exploit assign_loc_inject; eauto using partial_mem_inject.
    intros (m2' & ASSIGN2 & MEMINJ & LOAD).
    rewrite genv_cenv_preserved. exists m2'; split; trivial.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYMB BLKS1 BLKS2 RSI TGR].
    constructor; try solve [eauto using same_domain_right_assign_loc, same_blocks_assign_loc].
    intros b1' b2' delta' JB'.
    rewrite <- (assign_loc_block_compartment ASSIGN2). eauto.
  Qed.

  Lemma right_mem_injection_assign_loc_unmapped
    {j m1 m1' m2 ofs bf v1 ty b1 cp}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (LOCINJ: j b1 = None)
    (ASSIGN: assign_loc ge1 cp ty m1 b1 ofs bf v1 m1'):
    right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    destruct ASSIGN as [
        v1 chunk m1' ACCESS1 STORE1
      | b1' ofs' bytes1 m1' ACCESS H11 H12 H13 LOAD1 STORE1
      | v1 sz sg pos width m1' v1' STORE1 ].
    - simpl in *. eauto using right_mem_injection_store_unmapped.
    - eauto using right_mem_injection_storebytes_unmapped.
    - remember (Vptr b1 ofs) as addr1 eqn:Eaddr1.
      destruct STORE1 as
        [ sz sg1 attr sg pos width m1 addr1 c1 n1 m1' cp
          pos_0 width_bounds pos_width sg1_eq LOAD1 STORE1
        ]; subst addr1.
      simpl in *. eauto using right_mem_injection_store_unmapped.
  Qed.

  Lemma right_mem_injection_assign_loc_outside
    {j m1 m2 m2' ofs bf v2 ty b2 cp}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (LOCINJ: forall b delta, j b <> Some (b2, delta))
    (ASSIGN: assign_loc ge2 cp ty m2 b2 ofs bf v2 m2'):
    right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    destruct ASSIGN as [
        v2 chunk m2' ACCESS2 STORE2
      | b2' ofs' bytes2 m2' ACCESS H21 H22 H23 LOAD2 STORE2
      | v2 sz sg pos width m2' v2' STORE2 ].
    - simpl in *. eauto using right_mem_injection_store_outside.
    - eauto using right_mem_injection_storebytes_outside.
    - remember (Vptr b2 ofs) as addr2 eqn:Eaddr2.
      destruct STORE2 as
        [ sz sg2 attr sg pos width m2 addr2 c2 n2 m2' cp
          pos_0 width_bounds pos_width sg1_eq LOAD2 STORE2
        ]; subst addr2.
      simpl in *. eauto using right_mem_injection_store_outside.
  Qed.

  Lemma right_mem_injection_bind_parameters_right
    {j m1 m1' m2 e1 e2 vargs1 vargs2 params cp}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (RENVINJ: right_env_injection j e1 e2)
    (VALINJ: Val.inject_list j vargs1 vargs2)
    (BIND: bind_parameters ge1 cp e1 m1 params vargs1 m1'):
    exists m2',
      bind_parameters ge2 cp e2 m2 params vargs2 m2' /\
      right_mem_injection s j ge1 ge2 m1' m2'.
  Proof.
    revert m2 vargs2 RMEMINJ VALINJ.
    induction BIND as [
      | m1 id ty params v1 vl1 b1 m1' m1'' e1_id ASSIGN1 _ IH]; intros.
    - exists m2. split.
      + inv VALINJ. constructor.
      + assumption.
    - assert (exists v2 vl2, vargs2 = v2 :: vl2 /\ Val.inject j v1 v2 /\
                Val.inject_list j vl1 vl2)
        as (v2 & vl2 & -> & v1_v2 & vl1_vl2).
      { inv VALINJ; eauto. }
      clear VALINJ.
      assert (exists b2, j b1 = Some (b2, 0) /\ e2 ! id = Some (b2, ty))
        as (b2 & b1_b2 & e2_id).
      { destruct RENVINJ as [H _]. now apply H. }
      exploit @right_mem_injection_assign_loc_mapped; eauto.
      clear RMEMINJ v1_v2. intros (m2' & ASSIGN2 & RMEMINJ).
      exploit IH; eauto. clear RMEMINJ. intros (m2'' & BIND & RMEMINJ).
      exists m2''. split; trivial.
      econstructor; eauto.
  Qed.

  Lemma right_mem_injection_bind_parameters_left
    {j m1 m1' m2 e1 vargs1 params cp}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (BIND: bind_parameters ge1 cp e1 m1 params vargs1 m1')
    (LEFT: s cp = Left)
    (ENV_COMP: forall id b ty, e1 ! id = Some (b, ty) ->
                 Mem.block_compartment m1 b = cp)
    (ENV_NOT_GLOBAL: forall id b ty, e1 ! id = Some (b, ty) ->
                       Genv.find_def ge1 b = None):
    right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    induction BIND as [
      | m1 id ty params v1 vl1 b1 m1' m1'' e1_id ASSIGN1 _ IH]; trivial.
    assert (BC: Mem.block_compartment m1 b1 = cp) by (eapply ENV_COMP; eauto).
    assert (NG: Genv.find_def ge1 b1 = None) by (eapply ENV_NOT_GLOBAL; eauto).
    assert (j b1 = None) as UNMAPPED.
    { destruct (j b1) eqn:j_b1; trivial.
      destruct p.
      assert (j b1 <> None) as contra by congruence.
      pose proof (same_dom _ _ _ _ _ _ RMEMINJ b1) as [SD _].
      apply SD in contra.
      destruct contra as [contra | [fd contra]].
      - simpl in contra. rewrite BC in contra. congruence.
      - congruence. }
    exploit @right_mem_injection_assign_loc_unmapped; eauto.
    intros RMEMINJ'.
    apply IH; trivial.
    intros id0 b0 ty0 Hid0.
    rewrite <- (assign_loc_block_compartment ASSIGN1).
    eapply ENV_COMP; eauto.
  Qed.

  Lemma right_mem_injection_bind_parameters_left'
    {j m1 m2 m2' e2 vargs2 params cp}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (BIND: bind_parameters ge2 cp e2 m2 params vargs2 m2')
    (LEFT: s cp = Left)
    (ENV_COMP: forall id b ty, e2 ! id = Some (b, ty) ->
                 Mem.block_compartment m2 b = cp)
    (ENV_NOT_GLOBAL: forall id b ty, e2 ! id = Some (b, ty) ->
                       Genv.find_def ge2 b = None):
    right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    induction BIND as [
      | m2 id ty params v2 vl2 b2 m2' m2'' e2_id ASSIGN2 _ IH]; trivial.
    assert (BC: Mem.block_compartment m2 b2 = cp) by (eapply ENV_COMP; eauto).
    assert (NG: Genv.find_def ge2 b2 = None) by (eapply ENV_NOT_GLOBAL; eauto).
    assert (OUTSIDE: forall b delta, j b <> Some (b2, delta)).
    { intros b delta contra.
      pose proof (right_side_image _ _ _ _ _ _ RMEMINJ _ _ _ contra) as RSI.
      rewrite BC in RSI.
      destruct RSI as [RSI | RSI]; [congruence | congruence]. }
    exploit @right_mem_injection_assign_loc_outside; eauto.
    intros RMEMINJ'.
    apply IH; trivial.
    intros id0 b0 ty0 Hid0.
    rewrite <- (assign_loc_block_compartment ASSIGN2).
    eapply ENV_COMP; eauto.
  Qed.

  Lemma right_mem_injection_function_entry1_right: forall
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
    destruct (right_mem_injection_alloc_variables_right
                RMEMINJ RENVINJ0 RTENVINJ0 RIGHT H0)
      as (j' & e2 & m2' & ALLOC2 & RMEMINJ' & INCR & RENVINJ' & RTENVINJ').
    assert (VALINJ': Val.inject_list j' vargs1 vargs2). {
      clear -VALINJ INCR.
      induction VALINJ; [constructor |].
      constructor; [| assumption].
      inv H; try constructor.
      eapply Val.inject_ptr; [| reflexivity].
      auto. }
    exploit @right_mem_injection_bind_parameters_right; eauto.
    intros (m2'' & BIND2 & MEMINJ'').
    exists j', e2, (create_undef_temps (fn_temps f)), m2''.
    split; [| split; [| split; [| split]]]; auto.
    econstructor; eauto.
  Qed.

  Lemma right_mem_injection_function_entry1_left: forall
    {j f m1 m2 vargs1 e1 le1 m1'},
    right_mem_injection s j ge1 ge2 m1 m2 ->
    s (comp_of f) = Left ->
    function_entry1 ge1 f vargs1 m1 e1 le1 m1' ->
    right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    intros until m1'; intros RMEMINJ LEFT ENTRY.
    destruct ENTRY as [m1'' NOREPET ALLOC FIND E].
    simpl in *.
    exploit @right_mem_injection_alloc_variables_left; eauto.
    intros RMEMINJ'.
    eapply right_mem_injection_bind_parameters_left; eauto.
    - eapply alloc_variables_env_block_compartment; eauto.
      intros id0 b0 ty0. rewrite PTree.gempty. congruence.
    - eapply alloc_variables_env_not_global; eauto.
      + exact (same_blks1 _ _ _ _ _ _ RMEMINJ).
      + intros id0 b0 ty0. rewrite PTree.gempty. congruence.
  Qed.

  Lemma right_mem_injection_function_entry1_left': forall
    {j f m1 m2 vargs2 e2 le2 m2'},
    right_mem_injection s j ge1 ge2 m1 m2 ->
    s (comp_of f) = Left ->
    function_entry1 ge2 f vargs2 m2 e2 le2 m2' ->
    right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    intros until m2'; intros RMEMINJ LEFT ENTRY.
    destruct ENTRY as [m2'' NOREPET ALLOC FIND E].
    simpl in *.
    exploit @right_mem_injection_alloc_variables_left'; eauto.
    intros RMEMINJ'.
    eapply right_mem_injection_bind_parameters_left'; eauto.
    - eapply alloc_variables_env_block_compartment; eauto.
      intros id0 b0 ty0. rewrite PTree.gempty. congruence.
    - eapply alloc_variables_env_not_global; eauto.
      + exact (same_blks2 _ _ _ _ _ _ RMEMINJ).
      + intros id0 b0 ty0. rewrite PTree.gempty. congruence.
  Qed.

  (* FIXME: Move to Genv. *)
  Lemma invert_symbol_find_comp_of_block p b id :
    Genv.invert_symbol (globalenv p) b = Some id ->
    True (* find_comp_of_block always returns *).
  Proof. auto. Qed.

  Lemma same_blocks_extcall :
    forall wf_sc sem cp sg (ge: genv) vargs m t v m',
      extcall_properties wf_sc sem cp sg ->
      sem ge cp vargs m t v m' ->
      same_blocks ge m ->
      same_blocks ge m'.
  Proof.
    intros wf_sc0 sem cp sg ge0 vargs m t v m' EXT EC BLKS.
    constructor.
    - intros b gd FIND.
      assert (VB: Mem.valid_block m b).
      { unfold Mem.valid_block.
        eapply Plt_Ple_trans; [| exact (same_blocks_next _ _ BLKS)].
        eapply Genv.genv_defs_range; eauto. }
      erewrite <- ec_preserves_comp; eauto.
      eapply same_blocks_comp; eauto.
    - eapply Ple_trans; [exact (same_blocks_next _ _ BLKS) |].
      destruct (Pos.lt_total (Mem.nextblock m) (Mem.nextblock m')) as [LT | [EQ | GT]].
      + unfold Ple. lia.
      + unfold Ple. lia.
      + exfalso. apply (Plt_strict (Mem.nextblock m')).
        eapply ec_valid_block; eauto.
  Qed.

  Lemma symbols_inject_incr : forall cp j j' m1 m2,
      symbols_inject j ge1 ge2 cp ->
      same_blocks ge1 m1 ->
      same_blocks ge2 m2 ->
      inject_incr j j' ->
      inject_separated j j' m1 m2 ->
      symbols_inject j' ge1 ge2 cp.
  Proof.
    intros cp j j' m1 m2 SYMB BLKS1 BLKS2 INCR SEP.
    destruct SYMB as (S1 & S2 & S3 & S4 & S5).
    split; [|split; [|split; [|split]]]; auto.
    - (* find_symbol preservation *)
      intros id b1 b2 delta j'_b1 ge1_id.
      destruct (j b1) as [[b2' delta']|] eqn:j_b1.
      + exploit INCR; eauto. rewrite j'_b1. intros EQ; inv EQ. eauto.
      + exfalso. exploit SEP; eauto. intros [INV _].
        apply INV. red.
        eapply Plt_Ple_trans; [| exact (same_blocks_next _ _ BLKS1)].
        eapply Genv.genv_symb_range. exact ge1_id.
    - (* public symbol coverage *)
      intros id b1 pub_id ge1_id comp_id.
      exploit S3; eauto. intros [b2 [j_b1 ge2_id]].
      exists b2. split; [| exact ge2_id]. eauto.
    - (* block_is_volatile *)
      intros b1 b2 delta j'_b1.
      destruct (j b1) as [[b2' delta']|] eqn:j_b1.
      + exploit INCR; eauto. rewrite j'_b1. intros EQ; inv EQ. eauto.
      + exploit SEP; eauto. intros [INV1 INV2].
        assert (Ple (Genv.genv_next ge1) b1) as GE1.
        { eapply Ple_trans; [exact (same_blocks_next _ _ BLKS1) |].
          red. unfold Plt, Mem.valid_block in INV1. extlia. }
        assert (Ple (Genv.genv_next ge2) b2) as GE2.
        { eapply Ple_trans; [exact (same_blocks_next _ _ BLKS2) |].
          red. unfold Plt, Mem.valid_block in INV2. extlia. }
        assert (Senv.block_is_volatile ge1 b1 = false) as ->.
        { destruct (Senv.block_is_volatile ge1 b1) eqn:V1; trivial.
          exfalso. apply (Plt_strict b1).
          eapply Plt_Ple_trans; [| exact GE1].
          change (Plt b1 (Genv.genv_next ge1)).
          eapply Genv.block_is_volatile_below. exact V1. }
        assert (Senv.block_is_volatile ge2 b2 = false) as ->.
        { destruct (Senv.block_is_volatile ge2 b2) eqn:V2; trivial.
          exfalso. apply (Plt_strict b2).
          eapply Plt_Ple_trans; [| exact GE2].
          change (Plt b2 (Genv.genv_next ge2)).
          eapply Genv.block_is_volatile_below. exact V2. }
        reflexivity.
  Qed.
    (* intros cp j j' m1 m2 SYMB BLKS1 BLKS2 incr j_j'_sep. *)
    (* destruct SYMB as (SYMB1 & SYMB2 & SYMB3 & SYMB4). *)
    (* split; [|split; [|split]]; eauto. *)
    (* - intros id b1 b2 delta j'_b1 ge1_id. *)
    (*   destruct (j b1) as [[b2' delta']|] eqn:j_b1. *)
    (*   { exploit incr; eauto. rewrite j'_b1. *)
    (*     intros I. injection I as <- <-. *)
    (*     eauto. } *)
    (*   exploit j_j'_sep; eauto. intros (invalid_b1 & invalid_b2). *)
    (*   pose proof (Genv.find_invert_symbol _ _ ge1_id) as ge1_b1. *)
    (*   apply invert_symbol_find_comp_of_block in ge1_b1. *)
    (*   destruct ge1_b1 as [cp ge1_b1]. *)
    (*   exploit BLKS1; eauto. intros m1_b1. *)
    (*   apply Mem.block_compartment_valid_block in invalid_b1. *)
    (*   congruence. *)
    (* - intros id b1 public_id id_b1. *)
    (*   exploit SYMB3; eauto. intros (b2 & j_b1 & id_b2). *)
    (*   eauto. *)
    (* - intros b1 b2 delta j'_b1. *)
    (*   destruct (j b1) as [[b2' delta']|] eqn:j_b1. *)
    (*   { exploit incr; eauto. rewrite j'_b1. *)
    (*     intros I. injection I as <- <-. *)
    (*     eauto. } *)
    (*   exploit j_j'_sep; eauto. intros (invalid_b1 & invalid_b2). *)
    (*   simpl. *)
    (*   destruct (Genv.block_is_volatile _ b2) eqn:volatile_b2. *)
    (*   { exfalso. apply invalid_b2. *)
    (*     eauto using block_is_volatile_valid_block. } *)
    (*   destruct (Genv.block_is_volatile _ b1) eqn:volatile_b1; trivial. *)
    (*   exfalso. apply invalid_b2. *)
    (*   eauto using block_is_volatile_valid_block. *)

  Lemma right_mem_injection_external_call_right {cp j ef vargs1 vargs2 vres1 t m1 m1' m2}
    (RMEMINJ : right_mem_injection s j ge1 ge2 m1 m2)
    (EXTCALL: external_call ef ge1 cp vargs1 m1 t vres1 m1')
    (ARGINJ: Val.inject_list j vargs1 vargs2)
    (RIGHT: s cp = Right):
    exists j' m2' vres2,
      external_call ef ge2 cp vargs2 m2 t vres2 m2' /\
      right_mem_injection s j' ge1 ge2 m1' m2' /\
      inject_incr j j' /\
      Val.inject j' vres1 vres2.
  Proof.
    pose proof (external_call_spec ef cp) as ECSPEC.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYM BLKS1 BLKS2 RSIMG TGR].
    edestruct (ec_mem_inject ECSPEC) as (j' & vres2 & m2' & EXTCALL2 & RESINJ & MI' & UNCH1 & UNCH2 &
              INCR & SEP & NEWBLKS & NEWBLKS_INJ).
    { eapply SYMB; eauto. }
    { exact EXTCALL. }
    { exact MI. }
    { exact ARGINJ. }
    exists j', m2', vres2.
    split; [exact EXTCALL2 | split; [| split; [exact INCR | exact RESINJ]]].
    (* Preservation lemmas for block_compartment *)
    assert (PCOMP1: forall b, Mem.valid_block m1 b ->
      Mem.block_compartment m1' b = Mem.block_compartment m1 b).
    { intros b VB. symmetry. eapply (ec_preserves_comp ECSPEC); eauto. }
    assert (PCOMP2: forall b, Mem.valid_block m2 b ->
      Mem.block_compartment m2' b = Mem.block_compartment m2 b).
    { intros b VB. symmetry. eapply (ec_preserves_comp (external_call_spec ef cp)); eauto. }
    constructor.
    - (* same_domain_right *)
      intros b0. split.
      + (* j' b0 <> None -> Right \/ Gfun *)
        intros J'NE.
        destruct (plt b0 (Mem.nextblock m1)) as [VB|NVB].
        * (* b0 valid in m1 *)
          simpl. rewrite PCOMP1; [| exact VB].
          assert (j b0 <> None) as JNE.
          { destruct (j b0) as [[b2 d]|] eqn:JB; [congruence|].
            destruct (j' b0) as [[b2' d']|] eqn:J'B; [|congruence].
            exfalso. exploit SEP; eauto. intros [NVB' _]. contradiction. }
          apply (DOM b0). exact JNE.
        * (* b0 not valid in m1 *)
          destruct (plt b0 (Mem.nextblock m1')) as [VB'|NVB'].
          -- (* new block: comp = cp, s cp = Right *)
             left. simpl.
             erewrite ec_new_blocks_comp; eauto.
          -- (* not valid in m1' either: j' b0 = None, contradiction *)
             exfalso. apply J'NE. eapply Mem.mi_freeblocks; eauto.
      + (* Right \/ Gfun -> j' b0 <> None *)
        intros [SIDE | [fd FDEF]].
        * (* s (block_compartment m1' b0) = Right *)
          simpl in SIDE.
          destruct (plt b0 (Mem.nextblock m1)) as [VB|NVB].
          -- (* b0 valid in m1 *)
             rewrite PCOMP1 in SIDE; [|exact VB].
             assert (JNE: j b0 <> None) by (apply (DOM b0); left; exact SIDE).
             destruct (j b0) as [[b2 d]|] eqn:JB; [|congruence].
             rewrite (INCR _ _ _ JB). congruence.
          -- destruct (plt b0 (Mem.nextblock m1')) as [VB'|NVB'].
             ++ (* new block *)
                exploit NEWBLKS; eauto. intros [b' J'B]. congruence.
             ++ (* not valid in m1': block_compartment = top, s top = Left *)
                exfalso. rewrite Mem.block_compartment_valid_block in SIDE; [|exact NVB'].
                rewrite s_top_left in SIDE. discriminate.
        * (* exists fd, find_def ge1 b0 = Some (Gfun fd) *)
          assert (VB: Mem.valid_block m1 b0).
          { eapply Pos.lt_le_trans; [|exact (same_blocks_next _ _ BLKS1)].
            eapply Genv.genv_defs_range. unfold Genv.find_def in FDEF. exact FDEF. }
          assert (JNE: j b0 <> None) by (apply DOM; right; eauto).
          destruct (j b0) as [[b2 d]|] eqn:JB; [|congruence].
          rewrite (INCR _ _ _ JB). congruence.
    - (* partial_mem_inject *)
      exact MI'.
    - (* j_delta_zero *)
      intros b0 b' d J'B.
      destruct (j b0) as [[b2' d']|] eqn:JB.
      + (* old mapping *)
        rewrite (INCR _ _ _ JB) in J'B. injection J'B as <- <-.
        eapply D0; eauto.
      + (* new mapping: delta = 0 *)
        assert (NVB: ~Mem.valid_block m1 b0).
        { exploit SEP; eauto. intros [? _]; exact H. }
        assert (VB': Mem.valid_block m1' b0).
        { destruct (plt b0 (Mem.nextblock m1')); [assumption|].
          exfalso. assert (j' b0 = None) by (eapply Mem.mi_freeblocks; eauto).
          congruence. }
        exploit NEWBLKS; eauto. intros [b'' J'B'].
        rewrite J'B in J'B'. injection J'B' as <- <-. reflexivity.
    - (* j_injective *)
      intros b1a b1b b2a j'_b1a j'_b1b.
      destruct (j b1a) as [[ba da]|] eqn:JBa;
        destruct (j b1b) as [[bb db]|] eqn:JBb.
      + (* both old *)
        rewrite (INCR _ _ _ JBa) in j'_b1a. inv j'_b1a.
        rewrite (INCR _ _ _ JBb) in j'_b1b. inv j'_b1b.
        eapply JINJ; eauto.
      + (* a old, b new *)
        exfalso.
        rewrite (INCR _ _ _ JBa) in j'_b1a. inv j'_b1a.
        exploit SEP; eauto. intros [_ NVB2].
        apply NVB2. eapply Mem.mi_mappedblocks; eauto.
      + (* a new, b old *)
        exfalso.
        rewrite (INCR _ _ _ JBb) in j'_b1b. inv j'_b1b.
        exploit SEP; eauto. intros [_ NVB2].
        apply NVB2. eapply Mem.mi_mappedblocks; eauto.
      + (* both new *)
        destruct (peq b1a b1b) as [|NEQ]; [assumption|].
        exfalso. apply (NEWBLKS_INJ _ _ _ _ _ _ NEQ JBa JBb j'_b1a j'_b1b). reflexivity.
    - (* same_symb *)
      intros cp0 CP0R.
      eapply symbols_inject_incr; eauto.
    - (* j_preserves_symbols *)
      intros id b1 b2 delta J'B FSYM.
      assert (VB: Mem.valid_block m1 b1).
      { eapply Pos.lt_le_trans; [|exact (same_blocks_next _ _ BLKS1)].
        eapply Genv.genv_symb_range. exact FSYM. }
      destruct (j b1) as [[b2' d']|] eqn:JB.
      + rewrite (INCR _ _ _ JB) in J'B. injection J'B as <- <-.
        eapply JPSYM; eauto.
      + (* j b1 = None, j' b1 = Some: inject_separated gives ~valid m1 b1 *)
        exfalso. exploit SEP; eauto. intros [NVB _]. contradiction.
    - (* same_blks1 *)
      eapply (same_blocks_extcall _ _ _ _ _ _ _ _ _ _ ECSPEC); eauto.
    - (* same_blks2 *)
      eapply (same_blocks_extcall _ _ _ _ _ _ _ _ _ _ (external_call_spec ef cp)); eauto.
    - (* right_side_image *)
      intros b1 b2 delta J'B.
      destruct (j b1) as [[b2' d']|] eqn:JB.
      + (* old mapping *)
        rewrite (INCR _ _ _ JB) in J'B. injection J'B as <- <-.
        destruct (RSIMG _ _ _ JB) as [RIMG | FDEF].
        * left.
          assert (VB2: Mem.valid_block m2 b2').
          { eapply Mem.valid_block_inject_2; eauto. }
          rewrite PCOMP2; [exact RIMG | exact VB2].
        * right. exact FDEF.
      + (* new mapping: target block is new, comp = cp, s cp = Right *)
        left.
        assert (NVB2: ~Mem.valid_block m2 b2).
        { exploit SEP; eauto. intros [_ ?]; exact H. }
        assert (VB2': Mem.valid_block m2' b2).
        { eapply Mem.valid_block_inject_2; eauto. }
        erewrite ec_new_blocks_comp; eauto.
    - (* target_gvar_right *)
      intros b1 b2 delta gv J'B FDEF2.
      destruct (j b1) as [[b2' d']|] eqn:JB.
      + rewrite (INCR _ _ _ JB) in J'B. injection J'B as <- <-.
        eapply TGR; eauto.
      + (* new mapping: target above nextblock m2, no find_def *)
        exfalso.
        assert (NVB2: ~Mem.valid_block m2 b2).
        { exploit SEP; eauto. intros [_ ?]; exact H. }
        assert (Plt b2 (Genv.genv_next ge2)).
        { eapply Genv.genv_defs_range. unfold Genv.find_def in FDEF2. exact FDEF2. }
        apply NVB2. eapply Pos.lt_le_trans; [eassumption | exact (same_blocks_next _ _ BLKS2)].
  Qed.

  (* Left-side Gfun blocks in the injection domain have no permissions.
     True invariantly: Gfun blocks are size-0 and never gain permissions. *)
  Lemma right_mem_injection_external_call_left :
    forall cp j ef vargs1 vres1 t m1 m1' m2
           (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (EXTCALL: external_call ef ge1 cp vargs1 m1 t vres1 m1')
           (CP_LEFT: s cp = Left)
           (CP_NB: cp <> bottom)
           (CP_NT: cp <> top)
           (GFUN_NO_PERM: forall b fd ofs k p,
              j b <> None ->
              Genv.find_def ge1 b = Some (Gfun fd) ->
              s (comp_of fd) = Left ->
              ~ Mem.perm m1 b ofs k p),
      right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    intros.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYM BLKS1 BLKS2 RSIMG TGR].
    pose proof (external_call_spec ef cp) as ECSPEC.
    pose proof (ec_outside_comp ECSPEC ge1 vargs1 m1 t vres1 m1' EXTCALL)
      as UNCH.
    assert (PCOMP: forall b, Mem.valid_block m1 b ->
      Mem.block_compartment m1' b = Mem.block_compartment m1 b).
    { intros b VB. symmetry. eapply (ec_preserves_comp ECSPEC); eauto. }
    assert (MAXP: forall b ofs p, Mem.valid_block m1 b ->
      Mem.perm m1' b ofs Max p -> Mem.perm m1 b ofs Max p).
    { intros b ofs p VB PERM'. eapply (ec_max_perm ECSPEC); eauto. }
    assert (NEXTB: Ple (Mem.nextblock m1) (Mem.nextblock m1')).
    { eapply Mem.unchanged_on_nextblock. exact UNCH. }
    constructor.
    - (* same_domain_right *)
      intros b0. specialize (DOM b0). simpl in *.
      destruct (plt b0 (Mem.nextblock m1)) as [VB|NVB].
      + rewrite PCOMP; [exact DOM | exact VB].
      + (* b0 not valid in m1 — not mapped by j *)
        assert (JN: j b0 = None) by (eapply Mem.mi_freeblocks; eauto).
        split; [congruence |].
        intros [SIDE | [fd FDEF]].
        * (* New block with Right-side compartment? Contradiction. *)
          exfalso.
          destruct (plt b0 (Mem.nextblock m1')) as [VB'|NVB'].
          -- (* b0 valid in m1' but not m1: new block with comp cp *)
             assert (BC: Mem.block_compartment m1' b0 = cp).
             { eapply ec_new_blocks_comp; eauto. }
             rewrite BC in SIDE. rewrite CP_LEFT in SIDE. discriminate.
          -- (* b0 not valid in m1' either: block_compartment is top *)
             rewrite Mem.block_compartment_valid_block in SIDE; [|exact NVB'].
             rewrite s_top_left in SIDE. discriminate.
        * (* Gfun block: must be valid in m1 *)
          exfalso. apply NVB.
          assert (Plt b0 (Genv.genv_next ge1)).
          { eapply Genv.genv_defs_range. unfold Genv.find_def in FDEF. exact FDEF. }
          eapply Pos.lt_le_trans; [eassumption | exact (same_blocks_next _ _ BLKS1)].
    - (* partial_mem_inject *)
      (* Key fact: for each mapped block b, either:
         (A) ¬ can_access_block m1 b cp — protected by unchanged_on
         (B) can_access_block m1 b cp — must be a Left-side Gfun block,
             which has no permissions (GFUN_NO_PERM), and ec_max_perm
             ensures it still has no permissions in m1'. *)
      assert (MAPPED_PROT: forall b0,
        j b0 <> None ->
        ~ Mem.can_access_block m1 b0 cp \/
        (Mem.can_access_block m1 b0 cp /\
         exists fd, Genv.find_def ge1 b0 = Some (Gfun fd) /\ s (comp_of fd) = Left)).
      { intros b0 JB.
        destruct (flowsto_dec (Mem.block_compartment m1 b0) cp) as [ACC|NACC].
        - (* accessible: must be Left-side Gfun *)
          right. split; [exact ACC|].
          apply DOM in JB. simpl in JB.
          destruct JB as [SIDE | [fd FDEF]].
          + (* Right-side block: contradiction with accessibility *)
            exfalso.
            assert (Mem.block_compartment m1 b0 <> bottom).
            { intro E. rewrite E in SIDE. rewrite s_bottom_left in SIDE. discriminate. }
            assert (HEQ := flowsto_no_bottom_no_top _ _ ACC H CP_NT). subst.
            rewrite CP_LEFT in SIDE. discriminate.
          + exists fd. split; [exact FDEF|].
            assert (BC: Mem.block_compartment m1 b0 = comp_of (Gfun fd : globdef fundef type)).
            { eapply same_blocks_comp; eauto. }
            simpl in BC. rewrite BC in ACC.
            destruct fd as [fi|ef0].
            * (* Internal: comp_of fi <> bottom, so comp_of fi = cp = Left *)
              assert (comp_of fi <> bottom) by (eapply no_bottom_W1; exact FDEF).
              assert (comp_of fi = cp) by (eapply flowsto_no_bottom_no_top; eauto).
              subst. exact CP_LEFT.
            * (* External: comp_of = bottom, s bottom = Left *)
              simpl. exact s_bottom_left.
        - left. exact NACC. }
      (* Now prove inject *)
      destruct MI as [INJ FB MB NOV REP PINV].
      destruct INJ as [MIPERM MIOWN MIALIGN MIMEMVAL].
      constructor.
      + (* mi_inj *)
        constructor.
        * (* mi_perm *)
          intros b1 b2 delta ofs k p0 JB PERM'.
          destruct (flowsto_dec (Mem.block_compartment m1 b1) cp) as [ACC|NACC].
          -- (* accessible: Left-side Gfun, no perm in m1 *)
             exfalso.
             assert (JB' : j b1 <> None) by congruence.
             destruct (MAPPED_PROT b1 JB') as [NACC'|[_ [fd [FDEF FLEFT]]]].
             ++ contradiction.
             ++ assert (VB1: Mem.valid_block m1 b1).
                { destruct (plt b1 (Mem.nextblock m1)); [assumption|].
                  exfalso. apply n. eapply Pos.lt_le_trans; [|exact (same_blocks_next _ _ BLKS1)].
                  eapply Genv.genv_defs_range. unfold Genv.find_def in FDEF. exact FDEF. }
                assert (NPM: ~ Mem.perm m1' b1 ofs Max Nonempty).
                { intro PM'. apply (GFUN_NO_PERM b1 fd ofs Max Nonempty JB' FDEF FLEFT).
                  eapply MAXP; eauto. }
                apply NPM. eapply Mem.perm_max. eapply Mem.perm_implies; eauto. constructor.
          -- (* not accessible: protected by unchanged_on *)
             assert (VB1: Mem.valid_block m1 b1).
             { destruct (plt b1 (Mem.nextblock m1)); [assumption|].
               exfalso. assert (j b1 = None) by (eapply FB; eauto). congruence. }
             assert (PERM: Mem.perm m1 b1 ofs k p0).
             { eapply (Mem.unchanged_on_perm _ _ _ UNCH); eauto. }
             eapply MIPERM; eauto.
        * (* mi_access *)
          intros b1 b2 delta ofs p0 k JB PERM'.
          assert (VB1: Mem.valid_block m1 b1).
          { destruct (plt b1 (Mem.nextblock m1)); [assumption|].
            exfalso. assert (j b1 = None) by (eapply FB; eauto). congruence. }
          rewrite PCOMP; [|exact VB1].
          destruct (flowsto_dec (Mem.block_compartment m1 b1) cp) as [ACC|NACC].
          -- (* accessible: Left-side Gfun, no perm in m1' — contradiction *)
             exfalso.
             assert (JB' : j b1 <> None) by congruence.
             destruct (MAPPED_PROT b1 JB') as [NACC'|[_ [fd [FDEF FLEFT]]]].
             ++ contradiction.
             ++ apply (GFUN_NO_PERM b1 fd ofs Max Nonempty JB' FDEF FLEFT).
                eapply MAXP; eauto.
                eapply Mem.perm_max. eapply Mem.perm_implies; eauto. constructor.
          -- (* not accessible: use unchanged_on to get m1 perm *)
             eapply MIOWN; eauto.
             eapply (Mem.unchanged_on_perm _ _ _ UNCH); eauto.
        * (* mi_align *)
          intros b1 b2 delta chunk ofs p0 JB RANGE.
          eapply MIALIGN; eauto.
          intros ofs' RANGE'. eapply MAXP.
          -- destruct (plt b1 (Mem.nextblock m1)); [assumption|].
             exfalso. assert (j b1 = None) by (eapply FB; eauto). congruence.
          -- eapply RANGE. exact RANGE'.
        * (* mi_memval *)
          intros b1 ofs b2 delta JB PERM'.
          destruct (flowsto_dec (Mem.block_compartment m1 b1) cp) as [ACC|NACC].
          -- (* accessible: Left-side Gfun, no perm — contradiction *)
             exfalso.
             assert (JB' : j b1 <> None) by congruence.
             destruct (MAPPED_PROT b1 JB') as [NACC'|[_ [fd [FDEF FLEFT]]]].
             ++ contradiction.
             ++ assert (VB1: Mem.valid_block m1 b1).
                { destruct (plt b1 (Mem.nextblock m1)); [assumption|].
                  exfalso. apply n. eapply Pos.lt_le_trans; [|exact (same_blocks_next _ _ BLKS1)].
                  eapply Genv.genv_defs_range. unfold Genv.find_def in FDEF. exact FDEF. }
                assert (NPM: ~ Mem.perm m1' b1 ofs Max Nonempty).
                { intro PM'. apply (GFUN_NO_PERM b1 fd ofs Max Nonempty JB' FDEF FLEFT).
                  eapply MAXP; eauto. }
                apply NPM. eapply Mem.perm_max. eapply Mem.perm_implies; eauto. constructor.
          -- (* not accessible: protected *)
             assert (VB1: Mem.valid_block m1 b1).
             { destruct (plt b1 (Mem.nextblock m1)); [assumption|].
               exfalso. assert (j b1 = None) by (eapply FB; eauto). congruence. }
             assert (PERM: Mem.perm m1 b1 ofs Cur Readable).
             { eapply (Mem.unchanged_on_perm _ _ _ UNCH); eauto. }
             assert (CONTENTS: ZMap.get ofs (PMap.get b1 (Mem.mem_contents m1')) =
                     ZMap.get ofs (PMap.get b1 (Mem.mem_contents m1))).
             { eapply (Mem.unchanged_on_contents _ _ _ UNCH); eauto. }
             rewrite CONTENTS. eapply MIMEMVAL; eauto.
      + (* mi_freeblocks *)
        intros b0 NVB'. eapply FB.
        intro VB. apply NVB'. eapply Pos.lt_le_trans; eauto.
      + (* mi_mappedblocks *)
        exact MB.
      + (* mi_no_overlap *)
        intros b1 b1' d1 b2 b2' d2 ofs1 ofs2 NEQ JB1 JB2 P1 P2.
        eapply NOV; eauto; eapply MAXP; eauto.
        * destruct (plt b1 (Mem.nextblock m1)); [assumption|].
          exfalso. assert (j b1 = None) by (eapply FB; eauto). congruence.
        * destruct (plt b2 (Mem.nextblock m1)); [assumption|].
          exfalso. assert (j b2 = None) by (eapply FB; eauto). congruence.
      + (* mi_representable *)
        intros b0 b' delta ofs JB0 [P1|P1]; eapply REP; eauto;
        (assert (VB: Mem.valid_block m1 b0) by
          (destruct (plt b0 (Mem.nextblock m1)); [assumption|];
           exfalso; assert (j b0 = None) by (eapply FB; eauto); congruence));
        [left | right]; eapply MAXP; eauto.
      + (* mi_perm_inv *)
        intros b1 ofs b2 delta k p0 JB PM2.
        destruct (PINV b1 ofs b2 delta k p0 JB PM2) as [PM1|NPM1].
        * (* perm m1 b1 ofs k p0 *)
          destruct (flowsto_dec (Mem.block_compartment m1 b1) cp) as [ACC|NACC].
          -- (* accessible: Left-side Gfun, no perm — contradiction *)
             right. intro PM'.
             assert (JB' : j b1 <> None) by congruence.
             destruct (MAPPED_PROT b1 JB') as [NACC'|[_ [fd [FDEF FLEFT]]]].
             ++ contradiction.
             ++ apply (GFUN_NO_PERM b1 fd ofs Max Nonempty JB' FDEF FLEFT).
                eapply MAXP.
                { destruct (plt b1 (Mem.nextblock m1)); [assumption|].
                  exfalso. assert (j b1 = None) by (eapply FB; eauto). congruence. }
                eapply Mem.perm_max. eapply Mem.perm_implies; eauto. constructor.
          -- (* not accessible: unchanged_on preserves perm *)
             left.
             assert (VB1: Mem.valid_block m1 b1).
             { destruct (plt b1 (Mem.nextblock m1)); [assumption|].
               exfalso. assert (j b1 = None) by (eapply FB; eauto). congruence. }
             eapply (Mem.unchanged_on_perm _ _ _ UNCH); eauto.
        * (* ¬ perm m1 b1 ofs Max Nonempty *)
          right. intro PM'.
          apply NPM1. eapply MAXP; eauto.
          destruct (plt b1 (Mem.nextblock m1)); [assumption|].
          exfalso. assert (j b1 = None) by (eapply FB; eauto). congruence.
    - (* j_delta_zero *) exact D0.
    - (* j_injective *) exact JINJ.
    - (* same_symb *) exact SYMB.
    - (* j_preserves_symbols *) exact JPSYM.
    - (* same_blks1 *)
      constructor.
      + intros b0 gd FIND.
        assert (VB: Mem.valid_block m1 b0).
        { eapply Pos.lt_le_trans; [| exact (same_blocks_next _ _ BLKS1)].
          eapply Genv.genv_defs_range. unfold Genv.find_def in FIND. exact FIND. }
        rewrite PCOMP; [| exact VB]. eapply same_blocks_comp; eauto.
      + apply Pos.le_trans with (Mem.nextblock m1).
        * exact (same_blocks_next _ _ BLKS1).
        * apply NEXTB.
    - (* same_blks2 *) exact BLKS2.
    - (* right_side_image *) exact RSIMG.
    - (* target_gvar_right *) exact TGR.
  Qed.

  (* Target-side external call preserves right_mem_injection when the
     call is Left-side. Uses ec_outside_comp for non-accessible blocks
     and ec_max_perm for accessible-but-no-perm blocks (Gfun targets). *)
  (* Helper: if j maps b1 to b2 and find_def ge2 b2 is a Gvar, then its compartment is Right.
     Now uses the target_gvar_right field of right_mem_injection directly. *)
  Lemma gvar_injection_target_right :
    forall j0 m10 m20 b1 b2 delta gv
           (RMEMINJ0: right_mem_injection s j0 ge1 ge2 m10 m20)
           (JB: j0 b1 = Some (b2, delta))
           (FDEF2: Genv.find_def ge2 b2 = Some (Gvar gv)),
      s (comp_of gv) = Right.
  Proof.
    intros. eapply target_gvar_right; eauto.
  Qed.

  (* Helper: Right-side block_compartment implies not accessible by Left cp *)
  Lemma right_not_accessible_left m b2 cp0
    (RIMG: s (Mem.block_compartment m b2) = Right)
    (CP_LEFT: s cp0 = Left)
    (CP_NT: cp0 <> top):
    ~ Mem.can_access_block m b2 cp0.
  Proof.
    intro ACC. unfold Mem.can_access_block in ACC. simpl in ACC.
    assert (BNB: Mem.block_compartment m b2 <> bottom).
    { intro EQ. rewrite EQ in RIMG. rewrite s_bottom_left in RIMG. discriminate. }
    apply flowsto_no_bottom_no_top in ACC; [| exact BNB | exact CP_NT].
    rewrite ACC in RIMG. congruence.
  Qed.

  Lemma right_mem_injection_external_call_left' :
    forall cp j ef vargs2 vres2 t m1 m2 m2'
           (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (EXTCALL: external_call ef ge2 cp vargs2 m2 t vres2 m2')
           (CP_LEFT: s cp = Left)
           (CP_NT: cp <> top)
           (GFUN_NO_PERM2: forall b fd,
              Genv.find_def ge2 b = Some (Gfun fd) ->
              forall ofs k p, ~ Mem.perm m2 b ofs k p),
      right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    intros cp j ef vargs2 vres2 t m1 m2 m2' RMEMINJ EXTCALL CP_LEFT CP_NT GFUN_NO_PERM2.
    pose proof RMEMINJ as [DOM MI D0 JINJ SYMB JPSYM BLKS1 BLKS2 RSIMG TGR].
    pose proof (ec_outside_comp (external_call_spec ef cp) ge2 vargs2 m2 t vres2 m2' EXTCALL) as UNCH.
    (* Key fact: all injection targets are either not accessible by cp or have no permissions *)
    assert (INJ_TARGET_PROT: forall b1 b2 delta, j b1 = Some (b2, delta) ->
      ~ Mem.can_access_block m2 b2 cp \/ (forall ofs k p, ~ Mem.perm m2 b2 ofs k p)).
    { intros b1 b2 delta JB.
      pose proof (RSIMG _ _ _ JB) as [RIMG | FDEF].
      - (* Right-side target: not accessible by Left cp *)
        left. eapply right_not_accessible_left; eauto.
      - (* find_def target *)
        destruct (Genv.find_def ge2 b2) as [gd|] eqn:FDEF2; [| contradiction].
        destruct gd as [fd | gv].
        + (* Gfun: no permissions *)
          right. intros ofs k p PM. exact (GFUN_NO_PERM2 _ _ FDEF2 ofs k p PM).
        + (* Gvar: Right-side by injection structure, hence not accessible *)
          left.
          assert (GVRIGHT: s (comp_of gv) = Right).
          { eapply gvar_injection_target_right; eauto. }
          pose proof (same_blocks_comp _ _ BLKS2 _ _ FDEF2) as BCC.
          change (comp_of (Gvar gv)) with (comp_of gv) in BCC.
          rewrite <- BCC in GVRIGHT.
          eapply right_not_accessible_left; eauto. }
    (* Build unchanged_on for all injection targets *)
    assert (TARGET_UNCH: Mem.unchanged_on
      (fun b2 ofs => exists b1 delta, j b1 = Some (b2, delta)) m2 m2').
    { constructor.
      - exact (Mem.unchanged_on_nextblock _ _ _ UNCH).
      - (* permissions *)
        intros b ofs k p [b1 [delta JB]] VB.
        destruct (INJ_TARGET_PROT _ _ _ JB) as [NACC | NOPERM].
        + eapply (Mem.unchanged_on_perm _ _ _ UNCH); eauto.
        + split; intro PM.
          * exfalso. exact (NOPERM ofs k p PM).
          * exfalso. eapply NOPERM.
            eapply (ec_max_perm (external_call_spec ef cp)); eauto.
            eapply Mem.perm_max. exact PM.
      - (* contents *)
        intros b ofs [b1 [delta JB]] PERM.
        destruct (INJ_TARGET_PROT _ _ _ JB) as [NACC | NOPERM].
        + eapply (Mem.unchanged_on_contents _ _ _ UNCH); eauto.
        + exfalso. exact (NOPERM ofs Cur Readable PERM).
      - (* own *)
        intros b VB.
        symmetry. eapply (ec_preserves_comp (external_call_spec ef cp)); eauto. }
    assert (MI': Mem.inject j m1 m2').
    { eapply Mem.unchanged_on_inject' with
        (P := fun b2 _ => exists b1 delta, j b1 = Some (b2, delta)); eauto. }
    constructor.
    - (* same_domain_right *) exact DOM.
    - (* partial_mem_inject *) exact MI'.
    - (* j_delta_zero *) exact D0.
    - (* j_injective *) exact JINJ.
    - (* same_symb *) exact SYMB.
    - (* j_preserves_symbols *) exact JPSYM.
    - (* same_blks1 *) exact BLKS1.
    - (* same_blks2 *)
      eapply (same_blocks_extcall _ _ _ _ _ _ _ _ _ _ (external_call_spec ef cp)); eauto.
    - (* right_side_image *)
      intros b1 b2 delta JB.
      pose proof (RSIMG _ _ _ JB) as [RIMG | FDEF].
      + left.
        assert (VB: Mem.valid_block m2 b2).
        { eapply Mem.valid_block_inject_2; eauto. }
        pose proof (external_call_spec ef cp) as ECSPEC.
        assert (BCC: Mem.block_compartment m2 b2 = Mem.block_compartment m2' b2).
        { eapply (ec_preserves_comp ECSPEC); eauto. }
        rewrite <- BCC. exact RIMG.
      + right. exact FDEF.
    - (* target_gvar_right *) exact TGR.
  Qed.

  (* Target-side assign_loc preserves right_mem_injection when cp is Left. *)
  Lemma right_mem_injection_assign_loc_left' j0 m1 m2 m2' b ofs bf v cp ty ce:
    right_mem_injection s j0 ge1 ge2 m1 m2 ->
    assign_loc ce cp ty m2 b ofs bf v m2' ->
    s cp = Left -> cp <> top ->
    (forall b0 fd, Genv.find_def ge2 b0 = Some (Gfun fd) ->
       forall ofs0 k p, ~ Mem.perm m2 b0 ofs0 k p) ->
    right_mem_injection s j0 ge1 ge2 m1 m2'.
  Proof.
    intros RMEMINJ ASSIGN CP_LEFT CP_NT GFUN_NO_PERM2.
    destruct ASSIGN as [v0 chunk m2' AMODE STOREV
                       | b' ofs' bytes m2' AMODE ALIGN1 ALIGN2 OVERLAP LOAD STORE
                       | v0 sz sg pos width m2' v' BITFIELD].
    - (* assign_loc_value: store *)
      simpl in STOREV.
      eapply right_mem_injection_store_outside; eauto.
      { intros b1 delta JB.
        pose proof RMEMINJ as [DOM MI D0 JINJ SYMB JPSYM BLKS1 BLKS2 RSIMG TGR].
        pose proof (RSIMG _ _ _ JB) as [RIMG | FDEF].
        - apply (right_not_accessible_left _ _ _ RIMG CP_LEFT CP_NT).
          exact (proj1 (proj2 (Mem.store_valid_access_3 _ _ _ _ _ _ _ STOREV))).
        - destruct (Genv.find_def ge2 b) as [[fd|gv]|] eqn:FDEF2; try contradiction.
          + eapply GFUN_NO_PERM2; eauto.
            eapply Mem.valid_access_perm. eapply Mem.store_valid_access_3; eauto.
          + assert (GVRIGHT: s (comp_of gv) = Right)
              by (eapply gvar_injection_target_right; eauto).
            pose proof (same_blocks_comp _ _ BLKS2 _ _ FDEF2) as BCC.
            change (comp_of (Gvar gv)) with (comp_of gv) in BCC.
            rewrite <- BCC in GVRIGHT.
            apply (right_not_accessible_left _ _ _ GVRIGHT CP_LEFT CP_NT).
            exact (proj1 (proj2 (Mem.store_valid_access_3 _ _ _ _ _ _ _ STOREV))). }
    - (* assign_loc_copy: storebytes *)
      destruct (Nat.eq_dec (length bytes) 0) as [EMPTY|NOTEMPTY].
      + (* 0-byte: memory effectively unchanged *)
        destruct bytes as [|byte bytes']; [| simpl in EMPTY; lia].
        destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYM BLKS1 BLKS2 RSIMG TGR].
        constructor; eauto.
        * eapply Mem.unchanged_on_inject' with (P := fun _ _ => True); eauto.
          eapply Mem.storebytes_unchanged_on; eauto. simpl. intros. lia.
        * eapply same_blocks_storebytes; eauto.
        * intros b1 b2 delta JB.
          rewrite (Mem.storebytes_block_compartment _ _ _ _ _ _ STORE b2). eauto.
      + (* non-empty: b has perm *)
        eapply right_mem_injection_storebytes_outside; eauto.
        { intros b1 delta JB.
          pose proof RMEMINJ as [DOM MI D0 JINJ SYMB JPSYM BLKS1 BLKS2 RSIMG TGR].
          pose proof (RSIMG _ _ _ JB) as [RIMG | FDEF].
          - pose proof (Mem.storebytes_can_access_block_1 _ _ _ _ _ _ STORE) as [ACC | LEN].
            + apply (right_not_accessible_left _ _ _ RIMG CP_LEFT CP_NT). exact ACC.
            + exfalso. exact (NOTEMPTY LEN).
          - destruct (Genv.find_def ge2 b) as [[fd|gv]|] eqn:FDEF2; try contradiction.
            + assert (PM: Mem.perm m2 b (Ptrofs.unsigned ofs) Cur Writable).
              { eapply Mem.perm_cur.
                eapply Mem.storebytes_range_perm; eauto.
                destruct bytes as [|byte bytes']; [simpl in NOTEMPTY; lia|]. simpl. lia. }
              exact (GFUN_NO_PERM2 _ _ FDEF2 _ _ _ PM).
            + assert (GVRIGHT: s (comp_of gv) = Right)
                by (eapply gvar_injection_target_right; eauto).
              pose proof (same_blocks_comp _ _ BLKS2 _ _ FDEF2) as BCC.
              change (comp_of (Gvar gv)) with (comp_of gv) in BCC.
              rewrite <- BCC in GVRIGHT.
              pose proof (Mem.storebytes_can_access_block_1 _ _ _ _ _ _ STORE) as [ACC | LEN].
              * apply (right_not_accessible_left _ _ _ GVRIGHT CP_LEFT CP_NT). exact ACC.
              * exfalso. exact (NOTEMPTY LEN). }
    - (* assign_loc_bitfield: store *)
      remember (Vptr b ofs) as addr eqn:Eaddr.
      destruct BITFIELD as
        [sz0 sg0 attr sg0' pos0 width0 m2_0 addr0 c0 n0 m2'0 cp0
         _ _ _ _ _ STORE]; subst addr0.
      simpl in STORE.
      eapply right_mem_injection_store_outside; eauto.
      { intros b1 delta JB.
        pose proof RMEMINJ as [DOM MI D0 JINJ SYMB JPSYM BLKS1 BLKS2 RSIMG TGR].
        pose proof (RSIMG _ _ _ JB) as [RIMG | FDEF].
        - apply (right_not_accessible_left _ _ _ RIMG CP_LEFT CP_NT).
          exact (proj1 (proj2 (Mem.store_valid_access_3 _ _ _ _ _ _ _ STORE))).
        - destruct (Genv.find_def ge2 b) as [[fd|gv]|] eqn:FDEF2; try contradiction.
          + eapply GFUN_NO_PERM2; eauto.
            eapply Mem.valid_access_perm. eapply Mem.store_valid_access_3; eauto.
          + assert (GVRIGHT: s (comp_of gv) = Right)
              by (eapply gvar_injection_target_right; eauto).
            pose proof (same_blocks_comp _ _ BLKS2 _ _ FDEF2) as BCC.
            change (comp_of (Gvar gv)) with (comp_of gv) in BCC.
            rewrite <- BCC in GVRIGHT.
            apply (right_not_accessible_left _ _ _ GVRIGHT CP_LEFT CP_NT).
            exact (proj1 (proj2 (Mem.store_valid_access_3 _ _ _ _ _ _ _ STORE))). }
  Unshelve. all: exact Cur.
  Qed.

  Lemma find_funct_ptr_right id fd1 fd2 b1 b2
    (RIGHT: s (comp_of fd1) = Right)
    (SYM1: Genv.invert_symbol (Genv.globalenv W1) b1 = Some id)
    (SYM2: Genv.invert_symbol (Genv.globalenv W2) b2 = Some id)
    (FUN1: Genv.find_funct_ptr (Genv.globalenv W1) b1 = Some fd1)
    (FUN2: Genv.find_funct_ptr (Genv.globalenv W2) b2 = Some fd2):
    fd1 = fd2.
  Proof.
    apply Genv.invert_find_symbol in SYM1.
    apply Genv.invert_find_symbol in SYM2.
    (* From senv_match: find_symbol ge1 id = find_symbol ge2 id, so b1 = b2 *)
    assert (FS: Senv.find_symbol ge2 id = Senv.find_symbol ge1 id).
    { exact (proj1 (Genv.senv_match match_W1_W2) id). }
    assert (b1 = b2).
    { change (Genv.find_symbol (Genv.globalenv W1) id) with (Senv.find_symbol ge1 id) in SYM1.
      change (Genv.find_symbol (Genv.globalenv W2) id) with (Senv.find_symbol ge2 id) in SYM2.
      congruence. }
    subst b2.
    (* Use find_funct_ptr_match to get matched definition directly *)
    apply Genv.find_funct_ptr_iff in FUN1.
    apply Genv.find_funct_ptr_iff in FUN2.
    edestruct (Genv.find_def_match match_W1_W2) as [tg [TG MG]]; [exact FUN1 |].
    (* Bridge coercion gap between TG and FUN2 via the goal *)
    assert (H_eq: Some tg = Some (Gfun fd2)).
    { rewrite <- TG. exact FUN2. }
    inv H_eq.
    inv MG. inv H2.
    - (* match_function_left *) simpl in RIGHT. congruence.
    - (* match_external_left *) reflexivity.
    - (* match_right *) reflexivity.
  Qed.

  (** Sub-invariant lemmas, mostly on injections *)

  (* Helper: Left-side access to a mapped block leads to contradiction.
     If a Left-side compartment (cp <> top, cp <> bottom) can access a block,
     and the block has permissions, then the block is not mapped by j. *)
  Lemma left_access_unmapped j0 cp m1 m2 b
    (RMEMINJ: right_mem_injection s j0 ge1 ge2 m1 m2)
    (LEFT: s cp = Left) (NB: cp <> bottom) (NT: cp <> top)
    (ACC: flowsto (Mem.block_compartment m1 b) cp)
    (FNP: forall b0 fd, Genv.find_def ge1 b0 = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm m1 b0 ofs k p)
    (HAS_PERM: exists ofs k p, Mem.perm m1 b ofs k p):
    j0 b = None.
  Proof.
    destruct (j0 b) as [[b2 delta]|] eqn:JB; [|reflexivity].
    exfalso.
    assert (JB' : j0 b <> None) by congruence.
    destruct RMEMINJ as [DOM _ _ _ _ _ _ _ _].
    apply DOM in JB'. simpl in JB'.
    destruct JB' as [RSIDE | [fd FDEF]].
    - (* Right-side block: contradiction with Left access *)
      unfold in_side in RSIDE. simpl in RSIDE.
      assert (Mem.block_compartment m1 b <> bottom).
      { intro EQ. rewrite EQ in RSIDE. rewrite s_bottom_left in RSIDE. discriminate. }
      assert (Mem.block_compartment m1 b = cp) by (eapply flowsto_no_bottom_no_top; eauto).
      congruence.
    - (* Gfun block: contradiction with perm *)
      destruct HAS_PERM as [ofs' [k' [p' PERM']]].
      exact (FNP b fd FDEF ofs' k' p' PERM').
  Qed.

  (* assign_loc on Left side preserves right_mem_injection.
     For sizeof=0 copy: storebytes with nil bytes doesn't change memory content,
     so injection is preserved even without proving j b = None.
     For all other cases: block is unmapped because Left-side can't access Right-side blocks. *)
  Lemma right_mem_injection_assign_loc_left j0 m1 m1' m2 b ofs bf v cp ty ce:
    right_mem_injection s j0 ge1 ge2 m1 m2 ->
    assign_loc ce cp ty m1 b ofs bf v m1' ->
    s cp = Left -> cp <> bottom -> cp <> top ->
    (forall b0 fd, Genv.find_def ge1 b0 = Some (Gfun fd) ->
       forall ofs' k p, ~ Mem.perm m1 b0 ofs' k p) ->
    right_mem_injection s j0 ge1 ge2 m1' m2.
  Proof.
    intros RMEMINJ ASSIGN LEFT NB NT FNP.
    destruct ASSIGN as [v0 chunk m1' AMODE STOREV
                       | b' ofs' bytes m1' AMODE ALIGN1 ALIGN2 OVERLAP LOAD STORE
                       | v0 sz sg pos width m1' v' BITFIELD].
    - (* assign_loc_value: store *)
      simpl in STOREV.
      eapply right_mem_injection_store_unmapped; eauto.
      eapply left_access_unmapped; eauto.
      + exact (proj1 (proj2 (Mem.store_valid_access_3 _ _ _ _ _ _ _ STOREV))).
      + exists (Ptrofs.unsigned ofs), Cur, Writable.
        eapply Mem.valid_access_perm.
        exact (Mem.store_valid_access_3 _ _ _ _ _ _ _ STOREV).
    - (* assign_loc_copy: storebytes *)
      destruct (Nat.eq_dec (length bytes) 0) as [EMPTY|NOTEMPTY].
      + (* sizeof = 0: storebytes with nil bytes, memory effectively unchanged *)
        destruct bytes as [|byte bytes']; [| simpl in EMPTY; lia].
        destruct RMEMINJ.
        constructor; eauto.
        * eapply same_domain_right_storebytes; eauto.
        * eapply Mem.unchanged_on_inject with (P := fun _ _ => True); eauto.
          eapply Mem.storebytes_unchanged_on; eauto. simpl. intros. lia.
        * eapply same_blocks_storebytes; eauto.
      + (* sizeof > 0: non-empty bytes, block is unmapped *)
        eapply right_mem_injection_storebytes_unmapped; eauto.
        eapply left_access_unmapped; eauto.
        * exploit Mem.storebytes_can_access_block_1; [exact STORE|].
          intros [ACC|LEN]; [exact ACC|]. exfalso. exact (NOTEMPTY LEN).
        * destruct bytes as [|byte bytes']; [simpl in NOTEMPTY; lia|].
          exists (Ptrofs.unsigned ofs), Cur, Writable.
          apply Mem.perm_cur.
          eapply Mem.storebytes_range_perm; eauto. simpl. lia.
    - (* assign_loc_bitfield: store *)
      remember (Vptr b ofs) as addr eqn:Eaddr.
      destruct BITFIELD as
        [sz0 sg0 attr sg0' pos0 width0 m1_0 addr0 c0 n0 m1'0 cp0
         POS0 WIDTH0 POSWIDTH SG0 LOAD0 STORE0]; subst addr0.
      simpl in STORE0.
      eapply right_mem_injection_store_unmapped; eauto.
      eapply left_access_unmapped; eauto.
      + exact (proj1 (proj2 (Mem.store_valid_access_3 _ _ _ _ _ _ _ STORE0))).
      + exists (Ptrofs.unsigned ofs), Cur, Writable.
        eapply Mem.valid_access_perm.
        exact (Mem.store_valid_access_3 _ _ _ _ _ _ _ STORE0).
  Qed.

  (* set_perm_list on unmapped source blocks preserves right_mem_injection *)
  Lemma right_mem_injection_set_perm_list_left j0 m1 m1' m2 l p0:
    right_mem_injection s j0 ge1 ge2 m1 m2 ->
    Mem.set_perm_list m1 l p0 = Some m1' ->
    (forall b, (exists lo hi, In (b, lo, hi) l) -> j0 b = None) ->
    right_mem_injection s j0 ge1 ge2 m1' m2.
  Proof.
    intros RMEMINJ SPL UNMAPPED.
    destruct RMEMINJ.
    constructor; eauto.
    - (* same_dom *)
      intro b. unfold same_domain_right, in_side in *; simpl in *.
      rewrite (Mem.set_perm_list_block_compartment _ _ _ _ _ SPL).
      exact (same_dom0 b).
    - (* partial_mem_inject *)
      eapply Mem.unchanged_on_inject with (P := fun b _ => j0 b <> None); eauto.
      assert (NIN: forall b, j0 b <> None -> forall x, In x l -> fst (fst x) <> b).
      { intros b JB [[bx lox] hix] Hx. simpl. intro EQ; subst bx.
        apply JB. apply UNMAPPED. eauto. }
      constructor.
      + rewrite (Mem.nextblock_set_perm_list _ _ _ _ SPL). apply Ple_refl.
      + intros b ofs k pp JB VB. split.
        * eapply Mem.set_perm_list_perm_not_in_fwd; eauto.
        * eapply Mem.set_perm_list_perm_not_in; eauto.
      + intros b ofs JB PERM.
        rewrite (Mem.set_perm_list_contents _ _ _ _ SPL). reflexivity.
      + intros b VB.
        rewrite (Mem.set_perm_list_block_compartment _ _ _ _ _ SPL). reflexivity.
    - (* same_blks1 *)
      eapply same_blocks_set_perm_list; eauto.
  Qed.

  Lemma right_mem_injection_set_perm_list_left' j0 m1 m2 m2' l p0:
    right_mem_injection s j0 ge1 ge2 m1 m2 ->
    Mem.set_perm_list m2 l p0 = Some m2' ->
    (forall b, (exists lo hi, In (b, lo, hi) l) ->
       s (Mem.block_compartment m2 b) = Left /\ Genv.find_def ge2 b = None) ->
    right_mem_injection s j0 ge1 ge2 m1 m2'.
  Proof.
    intros RMEMINJ SPL BLK_LEFT.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYM BLKS1 BLKS2 RSIMG TGR].
    constructor; eauto.
    - (* partial_mem_inject *)
      eapply Mem.unchanged_on_inject' with
        (P := fun b2 _ => exists b1 delta, j0 b1 = Some (b2, delta)); eauto.
      + constructor.
        * rewrite (Mem.nextblock_set_perm_list _ _ _ _ SPL). apply Ple_refl.
        * intros b ofs k pp [b1 [delta JB]] VB.
          assert (NIN: forall x, In x l -> fst (fst x) <> b).
          { intros [[bx lox] hix] Hx. simpl. intro EQ; subst bx.
            pose proof (RSIMG _ _ _ JB) as [RIMG | FDEF].
            - pose proof (BLK_LEFT b (ex_intro _ lox (ex_intro _ hix Hx))) as [BL _].
              congruence.
            - pose proof (BLK_LEFT b (ex_intro _ lox (ex_intro _ hix Hx))) as [_ NG].
              destruct (Genv.find_def ge2 b); congruence. }
          split.
          -- eapply Mem.set_perm_list_perm_not_in_fwd; eauto.
          -- eapply Mem.set_perm_list_perm_not_in; eauto.
        * intros b ofs [b1 [delta JB]] PERM.
          rewrite (Mem.set_perm_list_contents _ _ _ _ SPL). reflexivity.
        * intros b VB.
          rewrite (Mem.set_perm_list_block_compartment _ _ _ _ _ SPL). reflexivity.
    - (* same_blks2 *)
      eapply same_blocks_set_perm_list; eauto.
    - (* right_side_image *)
      intros b1 b2 delta JB.
      pose proof (RSIMG _ _ _ JB) as [RIMG | FDEF].
      + left. rewrite (Mem.set_perm_list_block_compartment _ _ _ _ _ SPL). exact RIMG.
      + right. exact FDEF.
  Qed.

  (* Parallel set_perm_list on both memories (for Right-side env blocks on return) *)
  Lemma right_mem_injection_set_perm_list_both j0 m1 m1' m2 m2' l1 l2 p0:
    right_mem_injection s j0 ge1 ge2 m1 m2 ->
    Mem.set_perm_list m1 l1 p0 = Some m1' ->
    Mem.set_perm_list m2 l2 p0 = Some m2' ->
    perm_order p0 Readable ->
    (forall b1 b2 delta, j0 b1 = Some (b2, delta) ->
      (exists lo hi, In (b1, lo, hi) l1) <-> (exists lo' hi', In (b2, lo', hi') l2)) ->
    right_mem_injection s j0 ge1 ge2 m1' m2'.
  Proof.
    intros RMEMINJ SPL1 SPL2 PO CORR.
    destruct RMEMINJ as [DOM MI D0 JINJ SYMB JPSYM BLKS1 BLKS2 RSIMG TGR].
    constructor; eauto.
    - (* same_dom *)
      intro b. unfold same_domain_right, in_side in *; simpl in *.
      rewrite (Mem.set_perm_list_block_compartment _ _ _ _ _ SPL1).
      exact (DOM b).
    - (* partial_mem_inject *)
      eapply Mem.set_perm_list_parallel_inject; eauto.
    - (* same_blks1 *)
      eapply same_blocks_set_perm_list; eauto.
    - (* same_blks2 *)
      eapply same_blocks_set_perm_list; eauto.
    - (* right_side_image *)
      intros b1 b2 delta JB.
      pose proof (RSIMG _ _ _ JB) as [RIMG | FDEF].
      + left. rewrite (Mem.set_perm_list_block_compartment _ _ _ _ _ SPL2). exact RIMG.
      + right. exact FDEF.
  Qed.

  Lemma right_mem_injection_left_step_1: forall j s1 t s2 s1',
    right_mem_injection s j ge1 ge2 (memory_of s1) (memory_of s2) ->
    s |= s1 ∈ Left ->
    state_wf s1 ->
    step1 cpm1 ge1 s1 t s1' ->
    (forall b fd, Genv.find_def ge1 b = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm (memory_of s1) b ofs k p) ->
    (match s1 with
     | State _ _ _ e0 _ _ =>
         forall b, (exists lo hi, In (b, lo, hi) (blocks_of_env ge1 e0)) -> j b = None
     | Returnstate _ (Kcall _ _ e0 _ _) _ _ _ =>
         forall b, (exists lo hi, In (b, lo, hi) (blocks_of_env ge1 e0)) -> j b = None
     | _ => True
     end) ->
    right_mem_injection s j ge1 ge2 (memory_of s1') (memory_of s2).
  Proof.
    intros j s1 t s2 s1' RMEMINJ LEFT WF STEP FUN_NO_PERM ENV_UNMAPPED.
    inv STEP; simpl in *; try assumption.
    - (* step_assign *)
      destruct WF as (NB & NT & KP).
      eapply right_mem_injection_assign_loc_left; eauto.
    - (* step_call: set_perm case *)
      destruct (cp_eq_dec (comp_of f) (comp_of fd)); [subst; assumption|].
      destruct (cp_eq_dec (comp_of fd) bottom); [subst; assumption|].
      eapply right_mem_injection_set_perm_list_left; eauto.
    - (* step_builtin *)
      destruct WF as (NB & NT & KP).
      eapply right_mem_injection_external_call_left; eauto.
    - (* step_return_0 *)
      eapply right_mem_injection_free_list_left; eauto.
    - (* step_return_1 *)
      eapply right_mem_injection_free_list_left; eauto.
    - (* step_skip_call *)
      eapply right_mem_injection_free_list_left; eauto.
    - (* step_internal_function *)
      eapply right_mem_injection_function_entry1_left; eauto.
    - (* step_external_function *)
      destruct WF as [_ KP].
      eapply right_mem_injection_external_call_left; eauto.
      + eapply call_comp_left; eauto.
      + eapply cont_proper_call_comp_not_bottom; eauto.
      + eapply cont_proper_call_comp_not_top; eauto.
    - (* step_returnstate: set_perm case *)
      destruct (cp_eq_dec (comp_of f) cp); [subst; assumption|].
      destruct (cp_eq_dec cp bottom); [subst; assumption|].
      eapply right_mem_injection_set_perm_list_left; eauto.
  Qed.

  Lemma right_mem_injection_left_step_2: forall j s1 s2 t s2',
    right_mem_injection s j ge1 ge2 (memory_of s1) (memory_of s2) ->
    s |= s2 ∈ Left ->
    s |= s2' ∈ Left ->
    state_wf s2 ->
    step1 cpm2 ge2 s2 t s2' ->
    (forall b fd, Genv.find_def ge2 b = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm (memory_of s2) b ofs k p) ->
    (match s2 with
     | State f _ _ e0 _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge2 e0) ->
           Mem.block_compartment (memory_of s2) b = comp_of f /\
           Genv.find_def ge2 b = None
     | Returnstate _ (Kcall _ f e0 _ _) _ _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge2 e0) ->
           Mem.block_compartment (memory_of s2) b = comp_of f /\
           Genv.find_def ge2 b = None
     | _ => True
     end) ->
    right_mem_injection s j ge1 ge2 (memory_of s1) (memory_of s2').
  Proof.
    intros j s1 s2 t s2' RMEMINJ LEFT LEFT' WF STEP GFUN_NO_PERM2 ENV_BLOCKS.
    inv STEP; simpl in *; try assumption.
    - (* step_assign *)
      destruct WF as (NB & NT & KP).
      eapply right_mem_injection_assign_loc_left'; eauto.
    - (* step_call: set_perm case *)
      destruct (cp_eq_dec (comp_of f) (comp_of fd)); [subst; assumption|].
      destruct (cp_eq_dec (comp_of fd) bottom); [subst; assumption|].
      eapply right_mem_injection_set_perm_list_left'; eauto.
      intros b0 (lo & hi & IN).
      destruct (ENV_BLOCKS b0 lo hi IN) as [BC NG].
      split; [| exact NG]. rewrite BC, LEFT. reflexivity.
    - (* step_builtin *)
      destruct WF as (NB & NT & KP).
      eapply right_mem_injection_external_call_left'; eauto.
    - (* step_return_0 *)
      clear LEFT'.
      eapply right_mem_injection_free_list_left'; eauto.
      + intros b0 lo hi IN. exact (proj1 (ENV_BLOCKS b0 lo hi IN)).
      + intros b0 lo hi IN. exact (proj2 (ENV_BLOCKS b0 lo hi IN)).
    - (* step_return_1 *)
      clear LEFT'.
      eapply right_mem_injection_free_list_left'; eauto.
      + intros b0 lo hi IN. exact (proj1 (ENV_BLOCKS b0 lo hi IN)).
      + intros b0 lo hi IN. exact (proj2 (ENV_BLOCKS b0 lo hi IN)).
    - (* step_skip_call *)
      clear LEFT'.
      eapply right_mem_injection_free_list_left'; eauto.
      + intros b0 lo hi IN. exact (proj1 (ENV_BLOCKS b0 lo hi IN)).
      + intros b0 lo hi IN. exact (proj2 (ENV_BLOCKS b0 lo hi IN)).
    - (* step_internal_function *)
      eapply right_mem_injection_function_entry1_left'; eauto.
    - (* step_external_function *)
      destruct WF as [_ KP].
      eapply right_mem_injection_external_call_left'; eauto.
      + eapply call_comp_left_2; eauto.
      + eapply cont_proper_call_comp_not_top_2; eauto.
    - (* step_returnstate: set_perm case *)
      destruct (cp_eq_dec (comp_of f) cp); [subst; assumption|].
      destruct (cp_eq_dec cp bottom); [subst; assumption|].
      eapply right_mem_injection_set_perm_list_left'; eauto.
      intros b0 (lo & hi & IN).
      destruct (ENV_BLOCKS b0 lo hi IN) as [BC NG].
      split; [| exact NG]. rewrite BC. exact LEFT'.
  Qed.

Scheme statement_ind2 := Induction for statement Sort Prop
  with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme statement_labeled_statements_ind from statement_ind2, labeled_statements_ind2.

Inductive right_cont_injection_find_label_spec j:
  option (statement * cont) -> option (statement * cont) -> Prop :=
| rcifls_Some: forall stmt k1 k2,
    right_cont_injection s j k1 k2 ->
    right_cont_injection_find_label_spec j (Some (stmt, k1)) (Some (stmt, k2))
| rcifls_None:
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

Lemma remove_until_right_call_cont k:
  remove_until_right s k = remove_until_right s (call_cont k).
Proof.
  induction k; auto.
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

(* We can drop [call_cont] and prove a more general helper more
   easily. *)
Lemma find_label_remove_until_right:
  (forall stmt lbl k,
     ((forall stmt' k'
              (LABEL : find_label lbl stmt k = Some (stmt', k')),
         remove_until_right s k = remove_until_right s k')
  ))
  /\
  (forall sl lbl k,
     ((forall stmt' k'
              (LABEL_LS : find_label_ls lbl sl k = Some (stmt', k')),
         remove_until_right s k = remove_until_right s k')
  )).
Proof.
  apply statement_labeled_statements_ind;
    try easy;
    simpl; intros.
  - destruct find_label eqn:FIND.
    + injection LABEL as ->.
      exact (H _ _ _ _ FIND).
    + eapply H0; eauto.
  - destruct find_label eqn:FIND.
    + injection LABEL as ->.
      exact (H _ _ _ _ FIND).
    + eapply H0; eauto.
  - destruct find_label eqn:FIND.
    + injection LABEL as ->.
      exact (H _ _ _ _ FIND).
    + exact (H0 _ _ _ _ LABEL).
  - exact (H _ _ _ _ LABEL).
  - destruct (ident_eq lbl l) as [<- | NEQ].
    + injection LABEL as -> ->.
      reflexivity.
    + exact (H _ _ _ _ LABEL).
  - destruct find_label eqn:FIND.
    + injection LABEL_LS as ->.
      exact (H _ _ _ _ FIND).
    + eapply H0; eauto.
Qed.

Lemma remove_until_right_step: forall cpm ge s1 t s1',
  s |= s1 ∈ Left ->
  s |= s1' ∈ Left ->
  step1 cpm ge s1 t s1' ->
  remove_until_right s (cont_of s1') = remove_until_right s (cont_of s1).
Proof.
  intros cpm ge s1 t s1' LEFT LEFT' STEP. inv STEP; auto; simpl.
  - rewrite LEFT. reflexivity.
  - symmetry. rewrite remove_until_right_call_cont. reflexivity.
  - symmetry. rewrite remove_until_right_call_cont. reflexivity.
  - rewrite <- (proj1 find_label_remove_until_right _ _ _ _ _ H).
    symmetry. rewrite remove_until_right_call_cont. reflexivity.
  - inv EV. unfold Genv.type_of_call in H.
    destruct (cp_eq_dec (comp_of f) cp) as [<- | NEQ].
    + unfold in_side in LEFT; simpl in LEFT.
      destruct (cp_eq_dec (comp_of f) bottom); rewrite LEFT; reflexivity.
    + unfold in_side in LEFT'; simpl in LEFT'. rewrite LEFT'. reflexivity.
    + unfold in_side in LEFT'; simpl in LEFT'. now rewrite LEFT'.
Qed.

Lemma right_cont_injection_left_step_left_1: forall j s1 t s2 s1',
  right_cont_injection s j (remove_until_right s (cont_of s1)) (remove_until_right s (cont_of s2)) ->
  step1 cpm1 ge1 s1 t s1' ->
  s |= s1 ∈ Left ->
  s |= s1' ∈ Left ->
  right_cont_injection s j (remove_until_right s (cont_of s1')) (remove_until_right s (cont_of s2)).
Proof.
  intros j s1 t s2 s1' RCONTINJ STEP LEFT LEFT'.
  now rewrite (remove_until_right_step _ _ _ _ _ LEFT LEFT' STEP).
Qed.

Lemma right_cont_injection_left_step_left_2: forall j s1 s2 t s2',
  right_cont_injection s j (remove_until_right s (cont_of s1)) (remove_until_right s (cont_of s2)) ->
  step1 cpm2 ge2 s2 t s2' ->
  s |= s2 ∈ Left ->
  s |= s2' ∈ Left ->
  right_cont_injection s j (remove_until_right s (cont_of s1)) (remove_until_right s (cont_of s2')).
Proof.
  intros j s1 s2 t s2' RCONTINJ STEP LEFT LEFT'.
  now rewrite (remove_until_right_step _ _ _ _ _ LEFT LEFT' STEP).
Qed.

  (* WIP *)
  (* FIXME: Is this needed? *)
  Definition abstract_step_inj (j: meminj): meminj :=
    j.

  (** Step diagram lemmas *)

  Lemma parallel_concrete: forall j s1 s2 s1' t,
      right_state_injection s j ge1 ge2 s1 s2 ->
      s |= s1 ∈ Right ->
      state_inv ge1 s1 ->
      state_inv ge2 s2 ->
      Clight.step1 cpm1 ge1 s1 t s1' ->
      exists j' s2',
        Clight.step1 cpm2 ge2 s2 t s2' /\
          right_state_injection s j' ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' t rs_inj is_r1 SI1 SI2 step1.
    destruct rs_inj as [| _ is_r2 right_exec_inj].
    { (* contradiction *)
      destruct s1; simpl in *; congruence. }
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
      rename H2 into ASSIGN1.
      assert (f_right : s (comp_of f) = Right) by exact is_r2.
      assert (CP_NT: comp_of f <> top)
        by (intro E; rewrite E, s_top_left in f_right; discriminate).
      exploit eval_lvalue_injection; eauto.
      exploit eval_expr_injection; eauto.
      intros [v2 [v1_v2 eval_rhs2]] [loc2 [loc1_ofs [j_loc1 eval_lhs2]]].
      exploit sem_cast_inject; eauto using partial_mem_inject.
      intros [v2' [cast_v2 v1'_v2']].
      exploit j_delta_zero; eauto. intros ->.
      rewrite Ptrofs.add_zero in *.
      exploit @right_mem_injection_assign_loc_mapped; eauto.
      intros (m2' & ASSIGN2 & RMEMINJ').
      exists j; eexists; split.
      { econstructor; eauto. }
      apply RightControl; eauto.
      constructor; eauto.
    + (* step_set *)
      simpl in is_r2.
      assert (CP_NT: comp_of f <> top)
        by (intro E; rewrite E, s_top_left in is_r2; discriminate).
      exploit eval_expr_injection; eauto.
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
      simpl in is_r2.
      assert (CP_NT: comp_of f <> top)
        by (intro E; rewrite E, s_top_left in is_r2; discriminate).
      exploit eval_expr_injection; eauto; eauto.
      intros [vf2 [vf1_vf2 eval_a2]].
      exploit eval_exprlist_injection; eauto; eauto.
      intros [vargs2 [vargs1_vargs2 eval_vargs2]].
      destruct (s (comp_of fd1)) eqn:s_fd1.
      * (* Next function is on the left *)
        destruct (cp_eq_dec (comp_of fd1) bottom) as [BOTTOM_FD1|NOTBOTTOM_FD1].
        { (* comp_of fd1 = bottom — must be External function *)
          (* Eliminate Internal case by contradiction with no_bottom_W1 *)
          destruct fd1 as [fi|ef tys' ty' cc'].
          { exfalso.
            pose proof find_vf1 as FIND_COPY.
            apply Genv.find_funct_inv in FIND_COPY as [b_vf VF_EQ]. subst vf1.
            rewrite Genv.find_funct_find_funct_ptr in find_vf1.
            apply Genv.find_funct_ptr_iff in find_vf1.
            eapply no_bottom_W1; [exact find_vf1 | exact BOTTOM_FD1]. }
          (* fd1 = External ef tys' ty' cc' *)
          exploit find_funct_preserved_bottom; eauto.
          { eapply same_symb; eauto. }
          intros find_vf2.
          assert (Genv.allowed_call ge2 (comp_of f) vf2) as ALLOWED2.
          { left. erewrite Genv.find_funct_find_comp_in_genv; eauto.
            rewrite BOTTOM_FD1. constructor. }
          (* SET_PERM simplifies: comp_of (External ...) = bottom ≠ comp_of f (Right) *)
          assert (m' = m1) as -> by (destruct (cp_eq_dec _ _) in SET_PERM; exact SET_PERM).
          exists j.
          exists (Callstate (External ef tys' ty' cc') vargs2 (Kcall optid f e2 le2 k2) m2).
          split.
          { econstructor; eauto.
            - (* NO_CROSS_PTR: vacuous since type_of_call = InternalCall for bottom *)
              intro CROSS. exfalso. unfold Genv.type_of_call in CROSS. rewrite BOTTOM_FD1 in CROSS.
              destruct (flowsto_dec bottom (comp_of f)); [congruence | apply n; constructor].
            - (* call_trace: must be intra since comp_of fd = bottom *)
              inv EV1.
              + apply call_trace_intra. assumption.
              + exfalso. rewrite BOTTOM_FD1 in H. unfold Genv.type_of_call in H.
                destruct (flowsto_dec bottom (comp_of f)) as [|n0]; [discriminate | apply n0; constructor].
            - (* SET_PERM *)
              destruct (cp_eq_dec _ _); [reflexivity |].
              rewrite BOTTOM_FD1. destruct (cp_eq_dec bottom bottom); [reflexivity | congruence].
          }
          apply RightControl; simpl; trivial.
          constructor; simpl; trivial.
          now apply right_cont_injection_kcall_right. }
        (* comp_of fd1 <> bottom *)
        assert (CROSS1 : Genv.allowed_cross_call ge1 (comp_of f) vf1).
        { destruct ALLOWED1 as [CONTRA|CROSS1]; trivial.
          assert (COMP_VF1: Genv.find_comp_in_genv ge1 vf1 = comp_of fd1)
            by (eapply Genv.find_funct_find_comp_in_genv; eauto).
          rewrite COMP_VF1 in CONTRA.
          unfold Genv.type_of_call in CONTRA.
          destruct (flowsto_dec (comp_of fd1) (comp_of f)); try congruence.
          exfalso. apply flowsto_no_bottom_no_top in f0; [| exact NOTBOTTOM_FD1 | exact CP_NT].
          rewrite f0 in s_fd1. congruence. }
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
        exploit (Genv.find_def_match match_W1_W2); eauto.
        intros (def2 & ge2_b1 & match_fd').
        assert (exists fd2,
                   def2 = Gfun fd2 /\
                   match_fundef s tt fd1 fd2)
          as (fd2 & -> & match_fd'').
        { inv match_fd'. destruct ctx'. eauto. }
        assert (j b1 = Some (b1, 0)) as J_B1.
        { assert (j b1 <> None) as J_DEF.
          { apply (same_dom _ _ _ _ _ _ H11). right. eauto. }
          destruct (j b1) as [[b2' delta]|] eqn:EQ; [|congruence].
          assert (delta = 0) as -> by (eapply (j_delta_zero _ _ _ _ _ _ H11); eauto).
          destruct (j_preserves_symbols _ _ _ _ _ _ H11 _ _ _ _ EQ ge1_id) as [_ ge2_id'].
          assert (b2' = b1) as ->.
          { assert (Genv.find_symbol ge1 id = Some b2').
            { rewrite <- (Genv.find_symbol_match match_W1_W2). exact ge2_id'. }
            congruence. }
          reflexivity. }
        assert (vf2 = Vptr b1 Ptrofs.zero) as evf2.
        { inv vf1_vf2; try congruence.
          injection H1 as <- <-.
          rewrite J_B1 in H. inv H.
          rewrite Ptrofs.add_zero. reflexivity. }
        assert (Genv.find_funct ge2 vf2 = Some fd2) as find_vf2'.
        { assert (ge2_b1': Genv.find_def ge2 b1 = Some (Gfun fd2)).
          { replace (Genv.find_def ge2 b1) with (Genv.find_def (Genv.globalenv W2) b1) by reflexivity.
            exact ge2_b1. }
          unfold Genv.find_funct, Genv.find_funct_ptr. rewrite evf2.
          destruct Ptrofs.eq_dec as [_|?]; try congruence.
          rewrite ge2_b1'. reflexivity. }
        assert (type_of_fundef fd2 = Tfunction tyargs tyres cconv)
          as type_fd2.
        { inv match_fd''; eauto. }
        assert (COMP_fd1_fd2: comp_of fd1 = comp_of fd2)
              by (inv match_fd''; auto).
        assert (Genv.allowed_call ge2 (comp_of f) vf2) as ALLOWED2.
        { rewrite evf2. rewrite evf1 in ALLOWED1.
          exact (Genv.match_genvs_allowed_calls match_W1_W2 ALLOWED1). }
        (* Resolve SET_PERM: cross-comp non-bottom case *)
        assert (SP1: Mem.set_perm_list m1 (blocks_of_env ge1 e1) Readable = Some m').
        { destruct (cp_eq_dec (comp_of f) (comp_of fd1)) as [E|].
          - exfalso. rewrite E, s_fd1 in is_r2. discriminate.
          - destruct (cp_eq_dec (comp_of fd1) bottom); [congruence | exact SET_PERM]. }
        pose proof (j_injective _ _ _ _ _ _ H11) as JINJ.
        destruct (right_mem_injection_set_perm_list_right ltac:(eassumption) ltac:(eassumption) JINJ SP1)
          as (m2' & SP2 & RMEMINJ').
        exists j, (Callstate fd2 vargs2 (Kcall optid f e2 le2 k2) m2').
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
              * eapply right_mem_injection_list_match; eauto.
          - (* SET_PERM *)
            rewrite <- COMP_fd1_fd2.
            destruct (cp_eq_dec (comp_of f) (comp_of fd1)); [congruence |].
            destruct (cp_eq_dec (comp_of fd1) bottom); [congruence |].
            exact SP2. }
        { apply LeftControl.
          - simpl. destruct fd1; [exact s_fd1 | exfalso; apply NOTBOTTOM_FD1; reflexivity].
          - simpl. destruct fd2 as [fi2|ef2 tys2 ty2 cc2].
            + simpl in COMP_fd1_fd2. rewrite <- COMP_fd1_fd2. exact s_fd1.
            + exfalso. simpl in COMP_fd1_fd2. apply NOTBOTTOM_FD1. rewrite COMP_fd1_fd2. reflexivity.
          - simpl. exact RMEMINJ'.
          - simpl. destruct fd1; [| exfalso; apply NOTBOTTOM_FD1; reflexivity].
            rewrite is_r1. now apply right_cont_injection_kcall_right. }
      * rename fd1 into fd.
        rename type_fd1 into type_fd.
        exploit find_funct_preserved; eauto.
        { eapply same_symb; eauto. }
        intros find_vf2.
        assert (Genv.allowed_call ge2 (comp_of f) vf2) as ALLOWED2.
        { (* Show vf1 = vf2, then transfer allowed_call *)
          pose proof find_vf1 as FF.
          apply Genv.find_funct_inv in FF as [b_vf VF_EQ]. subst vf1.
          rewrite Genv.find_funct_find_funct_ptr in find_vf1.
          apply Genv.find_funct_ptr_iff in find_vf1.
          assert (exists id, Genv.find_symbol ge1 id = Some b_vf) as [id SYM1].
          { eapply Genv.find_def_find_symbol_inversion; eauto. exact W1_norepet. }
          inv vf1_vf2; try congruence.
          pose proof (j_delta_zero _ _ _ _ _ _ ltac:(eassumption) _ _ _ ltac:(eassumption)) as DELTA. subst delta.
          assert (b2 = b_vf).
          { pose proof (j_preserves_symbols _ _ _ _ _ _ ltac:(eassumption) _ _ _ _ ltac:(eassumption) SYM1) as [_ SYM2].
            assert (Genv.find_symbol ge2 id = Genv.find_symbol ge1 id)
              by exact (proj1 (Genv.senv_match match_W1_W2) id).
            congruence. }
          subst b2. rewrite Ptrofs.add_zero.
          exact (Genv.match_genvs_allowed_calls match_W1_W2 ALLOWED1). }
        (* Resolve SET_PERM *)
        assert (exists m2',
          (if cp_eq_dec (comp_of f) (comp_of fd) then m2' = m2
           else if cp_eq_dec (comp_of fd) bottom then m2' = m2
           else Mem.set_perm_list m2 (blocks_of_env ge2 e2) Readable = Some m2') /\
          right_mem_injection s j ge1 ge2 m' m2')
          as (m2' & SP2 & RMEMINJ').
        { destruct (cp_eq_dec (comp_of f) (comp_of fd)) as [E|NE].
          - exists m2. split; [reflexivity |].
            assert (m' = m1) as -> by exact SET_PERM. eassumption.
          - destruct (cp_eq_dec (comp_of fd) bottom) as [E|NE2].
            + exists m2. split; [reflexivity |].
              assert (m' = m1) as -> by exact SET_PERM. eassumption.
            + assert (SP1: Mem.set_perm_list m1 (blocks_of_env ge1 e1) Readable = Some m')
                by exact SET_PERM.
              pose proof (j_injective _ _ _ _ _ _ H11) as JINJ.
              destruct (right_mem_injection_set_perm_list_right ltac:(eassumption) ltac:(eassumption) JINJ SP1)
                as (m2'' & SP2 & RMEMINJ').
              exists m2''. split; [exact SP2 | exact RMEMINJ']. }
        exists j.
        exists (Callstate fd vargs2 (Kcall optid f e2 le2 k2) m2').
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
        { apply RightControl.
          - simpl. destruct fd; [exact s_fd1 | exact is_r2].
          - simpl. destruct fd; [exact s_fd1 | exact is_r2].
          - constructor; eauto.
            apply right_cont_injection_kcall_right; eassumption. }
    + (* step_builtin *)
      (* prefix *)
      simpl in is_r2.
      assert (CP_NT: comp_of f <> top)
        by (intro E; rewrite E, s_top_left in is_r2; discriminate).
      exploit eval_exprlist_injection; eauto.
      intros [vs' [? ?]].
      (* same as step_external_function *)
      destruct (right_mem_injection_external_call_right H8 H0 H1)
        as (j' & m2' & vres' & EXTCALL' & RMEMINJ' & INCR & RESINJ).
      { exact is_r2. }
      exists j'; eexists; split.
      { econstructor; eauto.
        exact (Genv.match_genvs_allowed_syscalls match_W1_W2 ALLOWED). }
      apply RightControl; eauto.
      constructor; eauto.
      * eapply right_cont_injection_inject_incr; eauto.
      * destruct H10 as [RENVINJ_SOME RENVINJ_NONE].
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
          { specialize (H11 _ _ H3) as [? [? ?]]. eexists; split; [|eauto]. eapply val_inject_incr; eauto. }
        - specialize (H11 _ _ H3) as [? [? ?]]. eexists; split; [|eauto]. eapply val_inject_incr; eauto.
    + (* step_seq*)
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto. constructor; auto.
    + (* step_skip_seq *)
      inv H7.
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_continue_seq *)
      inv H7.
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_break_seq *)
      inv H7.
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_ifthenelse *)
      simpl in is_r2.
      assert (CP_NT: comp_of f <> top)
        by (intro E; rewrite E, s_top_left in is_r2; discriminate).
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
      inv H8. exists j; eexists; split; [constructor | apply RightControl]; eauto.
      constructor; auto. constructor; auto.
    + (* step_break_loop1 *)
      inv H7. exists j; eexists; split; [apply step_break_loop1 | apply RightControl]; eauto.
      constructor; auto.
    + (* step_skip_loop2 *)
      inv H7. exists j; eexists; split; [apply step_skip_loop2 | apply RightControl]; eauto.
      constructor; auto.
    + (* step_break_loop2 *)
      inv H7. exists j; eexists; split; [apply step_break_loop2 | apply RightControl]; eauto.
      constructor; auto.
    + (* step_return_0 *)
      rename H7 into RMEMINJ. rename H8 into RCONTINJ. rename H9 into RENVINJ. rename H10 into RTENVINJ.
      destruct (right_mem_injection_free_list_right RMEMINJ RENVINJ H is_r1) as (m2' & FREE' & RMEMINJ').
      exists j; eexists; split.
      { apply step_return_0; eauto. }
      { apply RightControl.
        - simpl. destruct (cp_eq_dec (comp_of f) bottom) as [E|]; [| exact is_r2].
          exfalso. simpl in is_r2. rewrite E, s_bottom_left in is_r2. discriminate.
        - simpl. destruct (cp_eq_dec (comp_of f) bottom) as [E|]; [| exact is_r2].
          exfalso. simpl in is_r2. rewrite E, s_bottom_left in is_r2. discriminate.
        - constructor; auto.
          apply right_cont_injection_call_cont; auto. }
    + (* step_return_1 *)
      rename H9 into RMEMINJ. rename H10 into RCONTINJ. rename H11 into RENVINJ. rename H12 into RTENVINJ.
      destruct (right_mem_injection_free_list_right RMEMINJ RENVINJ H1 is_r1) as (m2' & FREE' & RMEMINJ').
      simpl in is_r2.
      assert (CP_NB: comp_of f <> bottom)
        by (intro E; rewrite E, s_bottom_left in is_r2; discriminate).
      assert (CP_NT: comp_of f <> top)
        by (intro E; rewrite E, s_top_left in is_r2; discriminate).
      exploit (eval_expr_injection s j m m2 e e2 le le2 (comp_of f) RMEMINJ RENVINJ RTENVINJ is_r1 CP_NT).
      { exact H. } intros (v2 & VINJ2 & EVAL2).
      exploit sem_cast_inject; eauto; [inv RMEMINJ; eauto |]. intros (v2' & CAST2' & VINJ2').
      exists j. eexists. split.
      { eapply step_return_1; eauto. }
      { apply RightControl.
        - simpl. destruct (cp_eq_dec (comp_of f) bottom); [congruence | exact is_r2].
        - simpl. destruct (cp_eq_dec (comp_of f) bottom); [congruence | exact is_r2].
        - constructor; auto.
          apply right_cont_injection_call_cont; auto. }
    + (* step_skip_call *)
      rename H8 into RMEMINJ. rename H9 into RCONTINJ. rename H10 into RENVINJ. rename H11 into RTENVINJ.
      destruct (right_mem_injection_free_list_right RMEMINJ RENVINJ H0 is_r1) as (m2' & FREE' & RMEMINJ').
      assert (CP_NB: comp_of f <> bottom).
      { simpl in is_r2. intro E; rewrite E, s_bottom_left in is_r2; discriminate. }
      exists j. eexists. split.
      { apply step_skip_call; eauto.
        destruct k; try contradiction H;
          inv RCONTINJ; reflexivity. }
      { apply RightControl.
        - simpl. destruct (cp_eq_dec (comp_of f) bottom); [congruence | simpl in is_r2; exact is_r2].
        - simpl. destruct (cp_eq_dec (comp_of f) bottom); [congruence | simpl in is_r2; exact is_r2].
        - constructor; auto. }
    + (* step_switch *)
      simpl in is_r2.
      assert (CP_NT: comp_of f <> top)
        by (intro E; rewrite E, s_top_left in is_r2; discriminate).
      exploit eval_expr_injection; simpl in is_r1; eauto.
      intros [v' [? ?]].
      assert (sem_switch_arg v (typeof a) = Some n -> sem_switch_arg v' (typeof a) = Some n).
      { intros. unfold sem_switch_arg in *.
        destruct (classify_switch (typeof a)); simpl in *; try easy; inv H1; try easy. }
      exists j; eexists; split; [econstructor | apply RightControl]; eauto.
      constructor; auto.
      constructor; auto.
    + (* step_break_switch *)
      inv H8. exists j; eexists; split; [constructor | apply RightControl]; eauto.
      constructor; auto.
    + (* step_continue_switch *)
      inv H7. exists j; eexists; split; [apply step_continue_switch | apply RightControl]; eauto.
      constructor; auto.
    + (* step_label *)
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_goto *)
      rename H7 into RMEMINJ. rename H8 into RCONTINJ. rename H9 into RENVINJ. rename H10 into RTENVINJ.
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
      rename H5 into RMEMINJ. rename H6 into RCONTINJ. rename H7 into ARGINJ.
      destruct (right_mem_injection_function_entry1_right RMEMINJ ARGINJ is_r1 H)
        as (j' & e2 & le2 & m2' & ENTRY' & INCR & RMEMINJ' & RENVINJ' & RTENVINJ').
      exists j'. eexists. split.
      { apply step_internal_function; eauto. }
      { apply RightControl; auto.
        constructor; auto.
        { eapply right_cont_injection_inject_incr; eauto. }
        inv H. inv ENTRY'. apply right_tenv_injection_create_undef_temps. }
    + (* step_external_function *)
      (* very similar to step_builtin *)
      rename H5 into RMEMINJ. rename H6 into RCONTINJ. rename H7 into ARGINJ.
      destruct (right_mem_injection_external_call_right RMEMINJ H ARGINJ)
        as (j' & m2' & vres' & EXTCALL' & RMEMINJ' & INCR & RESINJ).
      { unfold call_comp.
        destruct (call_cont_is_stop_or_kcall k) as [CC | (oid & f0 & e0 & le0 & k' & CC)];
          rewrite CC.
        - exfalso.
          assert (cont_caller_comp k = top).
          { clear -CC. induction k; simpl in *; try congruence; auto. }
          simpl in is_r1. rewrite H0 in is_r1. rewrite s_top_left in is_r1. discriminate.
        - simpl in is_r1. rewrite (call_cont_cont_caller_comp k _ _ _ _ _ CC) in is_r1. exact is_r1. }
      assert (CALL_COMP_EQ: call_comp cpm1 k = call_comp cpm2 k2).
      { apply right_cont_injection_call_comp with j.
        - exact RCONTINJ.
        - intro CC.
          assert (cont_caller_comp k = top).
          { clear -CC. induction k; simpl in *; try congruence; auto. }
          simpl in is_r1. rewrite H0 in is_r1. rewrite s_top_left in is_r1. discriminate. }
      exists j'; eexists; split.
      { eapply step_external_function.
        - rewrite CALL_COMP_EQ in EXTCALL'. exact EXTCALL'.
        - rewrite CALL_COMP_EQ in *.
          exact (Genv.match_genvs_allowed_syscalls match_W1_W2 ALLOWED). }
      { apply RightControl; simpl; try (destruct (cp_eq_dec bottom bottom); [| congruence]);
          simpl in *; eauto.
        constructor; eauto.
        eapply right_cont_injection_inject_incr; eauto. }
    + (* step_returnstate *)
      rename H5 into RMEMINJ. rename H6 into RCONTINJ. rename H7 into RVALINJ.
      inv RCONTINJ.
      * (* Pre-resolve SET_PERM for Left return *)
        assert (exists m2',
          (if cp_eq_dec (comp_of f2) cp then m2' = m2
           else if cp_eq_dec cp bottom then m2' = m2
           else Mem.set_perm_list m2 (blocks_of_env ge2 en2) Freeable = Some m2') /\
          right_mem_injection s j ge1 ge2 m' m2')
          as (m2' & SP2 & RMEMINJ').
        { destruct (cp_eq_dec (comp_of f) cp) as [ECP|NECP].
          - exists m2. split.
            + destruct (cp_eq_dec (comp_of f2) cp); [reflexivity | congruence].
            + destruct (cp_eq_dec (comp_of f) cp) in SET_PERM; [subst m'; exact RMEMINJ | congruence].
          - destruct (cp_eq_dec cp bottom) as [ECB|NECB].
            + exists m2. split.
              * destruct (cp_eq_dec (comp_of f2) cp); [congruence |].
                destruct (cp_eq_dec cp bottom); [reflexivity | congruence].
              * destruct (cp_eq_dec (comp_of f) cp) in SET_PERM; [congruence |].
                destruct (cp_eq_dec cp bottom) in SET_PERM; [subst m'; exact RMEMINJ | congruence].
            + assert (SET_PERM': Mem.set_perm_list m (blocks_of_env ge1 e) Freeable = Some m').
              { destruct (cp_eq_dec (comp_of f) cp) in SET_PERM; [congruence |].
                destruct (cp_eq_dec cp bottom) in SET_PERM; [congruence |].
                exact SET_PERM. }
              (* Get cont info from state_inv *)
              pose proof SI1 as [_ [_ [CONT_ABOVE1 [_ [CEC_SI1 _]]]]].
              simpl in CONT_ABOVE1, CEC_SI1.
              destruct CONT_ABOVE1 as [KENV1 _].
              destruct CEC_SI1 as [KCEC1 _].
              pose proof SI2 as [_ [_ [CONT_ABOVE2 [_ [CEC_SI2 _]]]]].
              simpl in CONT_ABOVE2, CEC_SI2.
              destruct CONT_ABOVE2 as [KENV2 _].
              destruct CEC_SI2 as [KCEC2 _].
              (* Target set_perm_list exists *)
              destruct (Mem.set_perm_list_exists (blocks_of_env ge2 en2) Freeable m2) as [m2'' SP2'].
              { intros b0 lo0 hi0 IN0. exact (proj2 (KCEC2 _ _ _ IN0)). }
              exists m2''. split.
              { destruct (cp_eq_dec (comp_of f2) cp); [congruence |].
                destruct (cp_eq_dec cp bottom); [congruence |].
                exact SP2'. }
              (* Source set_perm_list preserves injection *)
              assert (RMEMINJ1: right_mem_injection s j ge1 ge2 m' m2).
              { eapply right_mem_injection_set_perm_list_left; eauto.
                intros b0 (lo0 & hi0 & IN0).
                destruct (j b0) eqn:JB0; [exfalso | reflexivity].
                assert (JNE: j b0 <> None) by congruence.
                apply (same_dom _ _ _ _ _ _ RMEMINJ) in JNE.
                destruct JNE as [RSIDE | [fd0 DEF0]].
                - unfold in_side in RSIDE. simpl in RSIDE.
                  destruct (KCEC1 _ _ _ IN0) as [BC0 _].
                  rewrite BC0 in RSIDE.
                  unfold in_side in H5. simpl in H5. congruence.
                - assert (Genv.find_def ge1 b0 = None).
                  { eapply find_def_above_genv_next. exact (KENV1 _ _ _ IN0). }
                  congruence. }
              (* Target set_perm_list preserves injection *)
              eapply right_mem_injection_set_perm_list_left'; eauto.
              intros b0 (lo0 & hi0 & IN0). split.
              { destruct (KCEC2 _ _ _ IN0) as [BC0 _].
                rewrite BC0. unfold in_side in H5. simpl in H5. rewrite <- H6.
                exact H5. }
              { eapply find_def_above_genv_next. exact (KENV2 _ _ _ IN0). } }
        exists j. eexists. split.
        { apply step_returnstate.
          - rewrite <- H6.
            intros CALLTYPE. specialize (NO_CROSS_PTR CALLTYPE).
            destruct v; try contradiction; inv RVALINJ; reflexivity.
          - rewrite <- H6.
            inv EV.
            + apply return_trace_intra; auto.
            + apply return_trace_cross; auto.
              specialize (NO_CROSS_PTR H).
              destruct v; try contradiction; inv RVALINJ; inv H0; constructor.
          - destruct (cp_eq_dec (comp_of f) cp) as [EQ|NEQ].
            + assert (comp_of f2 = cp) by congruence.
              destruct (cp_eq_dec (comp_of f2) cp); [exact SP2 | congruence].
            + assert (comp_of f2 <> cp) by congruence.
              destruct (cp_eq_dec (comp_of f2) cp); [congruence |].
              destruct (cp_eq_dec cp bottom); exact SP2.
        }
        { apply LeftControl; auto.
          simpl. congruence. }
      * (* Resolve SET_PERM *)
        assert (exists m2',
          (if cp_eq_dec (comp_of f) cp then m2' = m2
           else if cp_eq_dec cp bottom then m2' = m2
           else Mem.set_perm_list m2 (blocks_of_env ge2 en2) Freeable = Some m2') /\
          right_mem_injection s j ge1 ge2 m' m2')
          as (m2' & SP2 & RMEMINJ').
        { destruct (cp_eq_dec (comp_of f) cp) as [E|NE].
          - exists m2. split; [reflexivity |].
            assert (m' = m) as -> by exact SET_PERM. exact RMEMINJ.
          - destruct (cp_eq_dec cp bottom) as [E|NE2].
            + exists m2. split; [reflexivity |].
              assert (m' = m) as -> by exact SET_PERM. exact RMEMINJ.
            + pose proof (j_injective _ _ _ _ _ _ RMEMINJ) as JINJ.
              destruct (right_mem_injection_set_perm_list_right RMEMINJ ltac:(eassumption) JINJ SET_PERM)
                as (m2'' & SP2 & RMEMINJ').
              exists m2''. split; [exact SP2 | exact RMEMINJ']. }
        exists j. eexists. split.
        { apply step_returnstate.
          - intros CALLTYPE. specialize (NO_CROSS_PTR CALLTYPE).
            destruct v; try contradiction; inv RVALINJ; reflexivity.
          - inv EV.
            + apply return_trace_intra; auto.
            + apply return_trace_cross; auto.
              specialize (NO_CROSS_PTR H).
              destruct v; try contradiction; inv RVALINJ; inv H0; constructor.
          - exact SP2.
        }
        { apply RightControl; auto.
          constructor.
          - exact RMEMINJ'.
          - assumption.
          - assumption.
          - destruct optid as [id |];
              [| assumption].
            simpl. intros id' v'' GET.
            destruct (peq id' id) as [-> | NEQ].
            + rewrite PTree.gss.
              rewrite PTree.gss in GET. injection GET as <-.
              eauto.
            + rewrite PTree.gso; [| assumption].
              rewrite PTree.gso in GET; [| assumption].
              eauto.
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


  (* parallel_concrete_E0 = parallel_concrete_E0' (they were originally two versions) *)
  Lemma parallel_concrete_E0 : forall j s1 s2 s1' s2' t,
    right_state_injection s j ge1 ge2 s1 s2 ->
    s |= s1 ∈ Right ->
    state_inv ge1 s1 ->
    state_inv ge2 s2 ->
    step1 cpm2 ge2 s2 E0 s2' ->
    step1 cpm1 ge1 s1 t s1' ->
  exists j',
    t = E0 /\ right_state_injection s j' ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' s2' t INJ RIGHT SI1 SI2 STEP1 STEP2.
    exploit parallel_concrete; eauto.
    intros [j' [s2'' [STEP2' INJ']]].
    destruct t as [| e [| e' t]].
    - destruct (step1_E0_determ STEP1 STEP2'). eauto.
    - exfalso. eapply step1_E0_event_False; eassumption.
    - apply (sr_traces (semantics_receptive _)) in STEP2. inv STEP2. inv H0.
  Qed.

  Lemma parallel_concrete_E0': forall j s1 s2 s1' s2' t,
    right_state_injection s j ge1 ge2 s1 s2 ->
    s |= s1 ∈ Right -> (* in the context *)
    state_inv ge1 s1 ->
    state_inv ge2 s2 ->
    step1 cpm2 ge2 s2 E0 s2' ->
    step1 cpm1 ge1 s1 t s1' ->
  exists j',
    t = E0 /\ right_state_injection s j' ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' s2' t INJ RIGHT SI1 SI2 STEP1 STEP2.
    exploit parallel_concrete; eauto.
    intros [j' [s2'' [STEP2' INJ']]].
    destruct t as [| e [| e' t]].
    - destruct (step1_E0_determ STEP1 STEP2').
      eauto.
    - exfalso. eapply step1_E0_event_False; eassumption.
    - apply (sr_traces (semantics_receptive _)) in STEP2.
      inv STEP2. inv H0.
  Qed.

  Lemma parallel_abstract_1: forall j s1 t s2 s1',
    right_state_injection s j ge1 ge2 s1 s2 ->
    step1 cpm1 ge1 s1 t s1' ->
    s |= s1 ∈ Left ->
    s |= s1' ∈ Left ->
    state_wf s1 ->
    (forall b fd, Genv.find_def ge1 b = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm (memory_of s1) b ofs k p) ->
    (match s1 with
     | State _ _ _ e0 _ _ =>
         forall b, (exists lo hi, In (b, lo, hi) (blocks_of_env ge1 e0)) -> j b = None
     | Returnstate _ (Kcall _ _ e0 _ _) _ _ _ =>
         forall b, (exists lo hi, In (b, lo, hi) (blocks_of_env ge1 e0)) -> j b = None
     | _ => True
     end) ->
    right_state_injection s j ge1 ge2 s1' s2.
  Proof.
    intros j s1 t s2 s1' INJ LEFT LEFT' STEP WF FNP ENV.
    inversion INJ as [SIDE1 SIDE2 MEMINJ CONTINJ |]; subst; clear INJ;
    [| exfalso; eauto using state_split_contra].
    exploit right_mem_injection_left_step_1; eauto.
    intros MEMINJ'.
    exploit right_cont_injection_left_step_left_1; eauto.
    intros CONTINJ'.
    constructor; try assumption.
  Qed.

  Lemma parallel_abstract_2: forall j s1 s2 t s2',
    right_state_injection s j ge1 ge2 s1 s2 ->
    step1 cpm2 ge2 s2 t s2' ->
    s |= s1 ∈ Left ->
    s |= s2 ∈ Left ->
    s |= s2' ∈ Left ->
    state_wf s2 ->
    (forall b fd, Genv.find_def ge2 b = Some (Gfun fd) ->
       forall ofs k p, ~ Mem.perm (memory_of s2) b ofs k p) ->
    (match s2 with
     | State f _ _ e0 _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge2 e0) ->
           Mem.block_compartment (memory_of s2) b = comp_of f /\
           Genv.find_def ge2 b = None
     | Returnstate _ (Kcall _ f e0 _ _) _ _ _ =>
         forall b lo hi, In (b, lo, hi) (blocks_of_env ge2 e0) ->
           Mem.block_compartment (memory_of s2) b = comp_of f /\
           Genv.find_def ge2 b = None
     | _ => True
     end) ->
    right_state_injection s j ge1 ge2 s1 s2'.
  Proof.
    intros j s1 s2 t s2' INJ STEP LEFT LEFT2 LEFT' WF GFUN_NO_PERM2 ENV_BLOCKS.
    inversion INJ as [SIDE1 SIDE2 MEMINJ CONTINJ |]; subst; clear INJ;
      [| exfalso; eauto using state_split_contra].
    assert (MEMINJ': right_mem_injection s j ge1 ge2 (memory_of s1) (memory_of s2')).
    { eapply right_mem_injection_left_step_2; eauto. }
    exploit right_cont_injection_left_step_left_2; eauto.
    intros CONTINJ'.
    constructor; try assumption.
  Qed.

  Lemma eventval_match_inject_inv j v ty v1 v2 :
    eventval_match ge1 v ty v1 ->
    eventval_match ge2 v ty v2 ->
    not_ptr v1 ->
    not_ptr v2 ->
    Val.inject j v1 v2.
  Proof.
    intros match1 match2 not_ptr1 not_ptr2.
    inv match1; inv match2; simpl in *; solve [easy|constructor].
  Qed.

  Lemma eventval_list_match_inject_inv j vl tyargs vargs1 vargs2 :
    eventval_list_match ge1 vl tyargs vargs1 ->
    eventval_list_match ge2 vl tyargs vargs2 ->
    Forall not_ptr vargs1 ->
    Forall not_ptr vargs2 ->
    Val.inject_list j vargs1 vargs2.
  Proof.
    intros match1 match2 not_ptr1 not_ptr2.
    revert vargs2 match2 not_ptr2.
    induction match1; intros vargs2 match2 not_ptr2;
    inv match2;
    repeat match goal with
    | H : Forall _ nil |- _ => inv H
    | H : Forall _ (_ :: _) |- _ => inv H
    end;
    constructor;
    eauto using eventval_match_inject_inv.
  Qed.

  Definition event_next_compartment e :=
    match e with
    | Event_call _ cp _ _
    | Event_return cp _ _ => Some cp
    | _ => None
    end.

  Definition trace_next_compartment t :=
    match t with
    | e :: nil => event_next_compartment e
    | _ => None
    end.

  Definition step1_next_compartment_prop (s1 s1': Clight.state) (t: trace) : Prop :=
    match trace_next_compartment t with
    | Some cp => s |= s1' ∈ (s cp)
    | None => forall δ, s |= s1 ∈ δ -> s |= s1' ∈ δ
    end.

  Lemma step1_next_compartment: forall (ge0: genv) cpm0 s1 t s1',
    (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
      comp_of f <> bottom /\ comp_of f <> top) ->
    state_wf s1 ->
    step1 cpm0 ge0 s1 t s1' ->
    step1_next_compartment_prop s1 s1' t.
  Proof.
    intros ge0 cpm0 s1 t s1' PROPER WF STEP.
    unfold step1_next_compartment_prop.
    inv STEP; simpl; try tauto;
      try (destruct WF as [NB' _]; intros δ SIDE;
           destruct (cp_eq_dec (comp_of f) bottom); [congruence | exact SIDE]).
    - (* step_call *)
      inv EV.
      + (* call_trace_intra: t = E0 *)
        simpl. intros δ SIDE.
        unfold in_side in *. simpl in *.
        assert (FLOW: flowsto (comp_of fd) (comp_of f)).
        { unfold Genv.type_of_call in *.
          destruct (flowsto_dec (comp_of fd) (comp_of f)); [assumption | congruence]. }
        destruct fd as [fi | ef tya tyr cc'].
        * (* Internal fi *)
          simpl.
          assert (HFD: exists b, Genv.find_def ge0 b = Some (Gfun (Internal fi))).
          { eapply find_funct_find_def_clight; eauto. }
          destruct HFD as [b' FD].
          destruct (PROPER _ _ FD) as [NB NT].
          simpl in FLOW.
          destruct WF as [_ [WF_NT _]].
          assert (comp_of fi = comp_of f).
          { eapply flowsto_no_bottom_no_top; eassumption. }
          congruence.
        * (* External *)
          simpl. exact SIDE.
      + (* call_trace_cross: t = Event_call :: nil *)
        simpl.
        destruct fd as [fi | ef tya tyr cc'].
        * simpl. reflexivity.
        * (* External fd with CrossCompartmentCall — impossible *)
          exfalso.
          unfold Genv.type_of_call in *; simpl in *.
          destruct (flowsto_dec bottom (comp_of f));
            [congruence | elim n; apply bottom_flowsto].
    - (* step_builtin *)
      assert (HNC: trace_next_compartment t = None).
      { exploit ec_no_crossing; [eauto using external_call_spec | eauto |].
        now destruct t as [|[] [|??]]. }
      rewrite HNC. simpl. tauto.
    - (* step_external_function *)
      assert (HNC: trace_next_compartment t = None).
      { exploit ec_no_crossing; [eauto using external_call_spec | eauto |].
        now destruct t as [|[] [|??]]. }
      rewrite HNC. simpl.
      intros δ SIDE. exact SIDE.
    - (* step_returnstate *)
      inv EV.
      + (* return_trace_intra: t = E0 *)
        simpl. intros δ SIDE.
        unfold in_side in *. simpl in *.
        assert (FLOW: flowsto cp (comp_of f)).
        { unfold Genv.type_of_call in *.
          destruct (flowsto_dec cp (comp_of f)); [assumption | congruence]. }
        destruct (cp_eq_dec cp bottom) as [-> | NB].
        * exact SIDE.
        * destruct WF as [_ [WF_NT _]].
          assert (cp = comp_of f).
          { eapply flowsto_no_bottom_no_top; eassumption. }
          congruence.
      + (* return_trace_cross: t = Event_return :: nil *)
        simpl. reflexivity.
  Qed.

  Lemma ec_no_crossing' ef ge cp vargs m t vres m' :
    external_call ef ge cp vargs m t vres m' ->
    trace_next_compartment t = None.
  Proof.
    intros SEM.
    exploit ec_no_crossing; eauto.
    { eauto using external_call_spec. }
    now destruct t as [|[] [|??]].
  Qed.

  Lemma call_trace_cons_inv F V (ge: Genv.t F V) cp cp' vf vargs ty t :
    call_trace ge cp cp' vf vargs ty t ->
    t <> E0 ->
    exists b ofs id vl,
      t = Event_call cp cp' id vl :: nil /\
      vf = Vptr b ofs /\
      cp <> cp' /\
      Genv.invert_symbol ge b = Some id /\
      eventval_list_match ge vl ty vargs.
  Proof.
    intros ct; inv ct; try congruence; eauto.
    intros _.
    unfold Genv.type_of_call in *.
    destruct (flowsto_dec cp' cp); try congruence.
    destruct (cp_eq_dec cp cp') as [->|?].
    + destruct (flowsto_dec cp' cp'); [congruence | elim n; apply flowsto_refl].
    + eauto 10.
  Qed.

  Lemma return_trace_cons_inv F V (ge: Genv.t F V) cp cp' vret tyret t :
    return_trace ge cp cp' vret tyret t ->
    t <> E0 ->
    exists res,
      t = Event_return cp cp' res :: nil /\
      cp <> cp' /\
      eventval_match ge res (proj_xtype tyret) vret.
  Proof.
    intros rt; inv rt; try congruence; eauto.
    intros _.
    unfold Genv.type_of_call in *.
    destruct (flowsto_dec cp' cp); try congruence.
    destruct (cp_eq_dec cp cp') as [->|?].
    + destruct (flowsto_dec cp' cp'); [congruence | elim n; apply flowsto_refl].
    + eauto 10.
  Qed.

  Lemma call_trace_return_trace 
    cp cp' cp'' cp''' vf vargs ty t vret tyret :
    call_trace ge1 cp cp' vf vargs ty t ->
    return_trace ge2 cp'' cp''' vret tyret t ->
    t = E0.
  Proof.
    intros H1 H2. inv H1; trivial. inv H2; trivial.
  Qed.

  Lemma parallel_abstract_t: forall j s1 s2 s1' s2' t,
    right_state_injection s j ge1 ge2 s1 s2 ->
    s |= s1 ∈ Left ->
    state_wf s1 ->
    state_wf s2 ->
    state_inv ge1 s1 ->
    state_inv ge2 s2 ->
    step1 cpm1 ge1 s1 t s1' ->
    step1 cpm2 ge2 s2 t s2' ->
    right_state_injection s j ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' s2' t INJ LEFT1 WF1 WF2 SI1 SI2 STEP1 STEP2.
    assert (s |= s2 ∈ Left) as LEFT2.
    { eauto using right_state_injection_same_side_right. }
    assert (PROPER1: forall b f, Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
      comp_of f <> bottom /\ comp_of f <> top)
      by (intros; split; [eapply no_bottom_W1 | eapply no_top_W1]; eauto).
    assert (PROPER2: forall b f, Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
      comp_of f <> bottom /\ comp_of f <> top)
      by (intros; split; [eapply no_bottom_W2 | eapply no_top_W2]; eauto).
    pose proof (step1_next_compartment _ _ _ _ _ PROPER1 WF1 STEP1) as EV1.
    pose proof (step1_next_compartment _ _ _ _ _ PROPER2 WF2 STEP2) as EV2.
    (* If the next states remain on the left (which we can check by analyzing
       the value of trace_next_compartment), then the goal follows by a simple
       application of the previous parallel_abstract lemmas. *)
    (* Check if next states stay Left *)
    assert (STAYS_LEFT:
      (s |= s1' ∈ Left /\ s |= s2' ∈ Left) \/
      (exists cp, trace_next_compartment t = Some cp /\ s cp = Right)).
    { destruct (trace_next_compartment t) as [cp|] eqn:E.
      - unfold step1_next_compartment_prop in EV1. rewrite E in EV1.
        destruct (s cp) eqn:SCP; [left; split; [exact EV1 |] | right; eauto].
        unfold step1_next_compartment_prop in EV2. rewrite E in EV2.
        rewrite SCP in EV2. exact EV2.
      - left. unfold step1_next_compartment_prop in EV1, EV2. rewrite E in EV1, EV2.
        split; [apply EV1; exact LEFT1 | apply EV2; exact LEFT2]. }
    destruct STAYS_LEFT as [[LEFT1' LEFT2'] | [cp [TNC SCP]]].
    { (* Both stay Left: use parallel_abstract_1 + parallel_abstract_2 *)
      pose proof (right_state_injection_left_rmi INJ LEFT1) as RMI.
      pose proof (state_inv_env_above _ _ SI1) as ENV_ABOVE1.
      pose proof (state_inv_env_blocks_info _ _ SI1) as ENV_INFO1.
      assert (INJ1: right_state_injection s j ge1 ge2 s1' s2).
      { eapply parallel_abstract_1; eauto.
        - exact (state_inv_gfun_no_perm _ _ SI1).
        - destruct s1; simpl in *; auto.
          + intros b0 EX.
            eapply (env_blocks_unmapped_via_same_domain j ge1 _ _ b0 (comp_of f));
              [exact (same_dom _ _ _ _ _ _ RMI) | exact (same_blks1 _ _ _ _ _ _ RMI) | exact LEFT1 |
               intros b' lo' hi' IN'; split; [exact (ENV_ABOVE1 _ _ _ IN') | exact (proj1 (ENV_INFO1 _ _ _ IN'))] | exact EX].
          + destruct k; simpl in *; auto.
            intros b0 EX.
            assert (COMP_F_LEFT: s (comp_of f) = Left).
            { inv STEP1; simpl in LEFT1'; exact LEFT1'. }
            eapply (env_blocks_unmapped_via_same_domain j ge1 _ _ b0 (comp_of f));
              [exact (same_dom _ _ _ _ _ _ RMI) | exact (same_blks1 _ _ _ _ _ _ RMI) | exact COMP_F_LEFT |
               intros b' lo' hi' IN'; split; [exact (ENV_ABOVE1 _ _ _ IN') | exact (proj1 (ENV_INFO1 _ _ _ IN'))] | exact EX]. }
      eapply parallel_abstract_2; try exact INJ1; try exact STEP2;
        try exact LEFT1'; try exact LEFT2; try exact LEFT2';
        try exact WF2.
      - exact (state_inv_gfun_no_perm _ _ SI2).
      - exact (state_inv_env_blocks_info _ _ SI2). }
    (* Right case: Left→Right transition via cross-comp call/return *)
    unfold step1_next_compartment_prop in EV1, EV2. rewrite TNC in EV1, EV2.
    rewrite SCP in EV1, EV2.
    assert (RIGHT1': s |= s1' ∈ Right) by exact EV1.
    assert (RIGHT2': s |= s2' ∈ Right) by exact EV2.
    clear EV1 EV2.
    (* Extract RMI and RCINJ from INJ *)
    pose proof (right_state_injection_left_rmi INJ LEFT1) as RMI.
    pose proof (right_state_injection_left_rcinj INJ LEFT1) as RCINJ.
    (* Apply RightControl *)
    apply RightControl; [exact RIGHT1' | exact RIGHT2' |].
    (* Need: right_executing_injection ge1 ge2 s1' s2' *)
    (* Case-analyze STEP1 to find which step constructor produced the event *)
    inv STEP1; try (simpl in TNC; discriminate).
    + (* step_call: Left→Right cross-compartment call *)
      (* The call_trace must be cross-compartment (otherwise t=E0, contradicting TNC) *)
      inv EV; [simpl in TNC; discriminate |].
      (* Now t = [Event_call (comp_of f) (comp_of fd) i vl] *)
      simpl in TNC. inv TNC.
      (* cp = comp_of fd *)
      (* fd must be Internal (External would give state_comp = cont_caller_comp,
         which is Left since f is Left) *)
      assert (FD_INTERNAL: exists fd_f, fd = Internal fd_f).
      { destruct fd as [fd_f | ef targs tres cc].
        - eauto.
        - (* External: state_comp uses cont_caller_comp k, which is comp_of f = Left *)
          exfalso. simpl in RIGHT1'. unfold in_side in RIGHT1'. simpl in RIGHT1'.
          simpl in LEFT1. unfold in_side in LEFT1. simpl in LEFT1.
          congruence. }
      destruct FD_INTERNAL as [fd_f ->].
      (* Now we need to invert STEP2, which must also be step_call with cross-comp call *)
      (* Invert STEP2: only step_call can produce Event_call *)
      inv STEP2; try discriminate.
      * (* step_call: the real case *)
        (* Invert EV (STEP2's call_trace) — must be cross-compartment *)
        inv EV; try discriminate.
        (* From the trace equality Event_call cp1 cp1' i1 vl1 = Event_call cp cp' i vl *)
        (* Now: H15: comp_of f0 = comp_of f, H13: comp_of fd = comp_of fd_f,
           H23: Genv.invert_symbol ge2 b0 = Some i,
           H24: eventval_list_match ge2 vl ... vargs0 *)
        (* fd = Internal fd_f: both programs resolve symbol i to the same function *)
        (* b0 = b: senv_match gives find_symbol ge2 = find_symbol ge1 *)
        assert (FS: Genv.find_symbol ge2 i = Genv.find_symbol ge1 i).
        { exact (proj1 (Genv.senv_match match_W1_W2) i). }
        apply Genv.invert_find_symbol in H6. apply Genv.invert_find_symbol in H23.
        assert (B_EQ: b0 = b) by congruence. subst b0.
        (* fd = Internal fd_f: find_def_match_2 + match_right *)
        assert (FD_EQ: fd = Internal fd_f).
        { pose proof (Genv.find_def_match_2 match_W1_W2 b) as REL.
          unfold Genv.find_funct in H2, H10.
          destruct (Ptrofs.eq_dec ofs Ptrofs.zero); [| discriminate].
          destruct (Ptrofs.eq_dec ofs0 Ptrofs.zero); [| discriminate].
          (* H2: find_funct_ptr ge1 b = Some (Internal fd_f) *)
          (* H10: find_funct_ptr ge2 b = Some fd *)
          apply Genv.find_funct_ptr_iff in H2.
          change (Genv.find_def (Genv.globalenv W1) b) with (Genv.find_def ge1 b) in REL.
          change (Genv.find_def (Genv.globalenv W2) b) with (Genv.find_def ge2 b) in REL.
          rewrite H2 in REL.
          apply Genv.find_funct_ptr_iff in H10.
          rewrite H10 in REL. inv REL. inv H16. inv H18; try congruence.
          (* match_function_left: s cp = Left contradicts SCP = Right *)
          exfalso. simpl in SCP. unfold in_side in H16. simpl in H16. congruence. }
        subst fd.
        (* Types must match since fd_f is the same function *)
        assert (TYARGS_EQ: tyargs0 = tyargs /\ tyres0 = tyres /\ cconv0 = cconv).
        { rewrite H3 in H11. inv H11. auto. }
        destruct TYARGS_EQ as [-> [-> ->]].
        (* vargs0 = vargs: same eventvals, same types, no pointers *)
        assert (VARGS_EQ: vargs0 = vargs).
        { assert (NP: Forall not_ptr vargs) by (apply NO_CROSS_PTR; exact H4).
          clear - H7 H24 NP.
          revert vargs0 H24 NP. induction H7; intros vl2 HM NP; inv HM; auto.
          inv NP. f_equal; [| eauto].
          inv H; inv H5; try reflexivity.
          (* EVptr_global case: contradicts not_ptr *)
          simpl in H3. contradiction. }
        subst vargs0.
        (* Build inject_callstates *)
        apply inject_callstates.
        -- (* right_mem_injection m' m'0 *)
           simpl in RMI.
           (* Extract set_perm_list from the conditional *)
           assert (COMP_NEQ: comp_of f <> comp_of (Internal fd_f)).
           { intro EQ. unfold in_side in LEFT1; simpl in LEFT1, SCP, EQ.
             congruence. }
           assert (FD_NOT_BOTTOM: comp_of (Internal fd_f) <> bottom).
           { unfold Genv.find_funct in H2.
             destruct (Ptrofs.eq_dec ofs Ptrofs.zero); [| discriminate].
             apply Genv.find_funct_ptr_iff in H2.
             eapply no_bottom_W1; eauto. }
           assert (COMP_NEQ0: comp_of f0 <> comp_of (Internal fd_f)).
           { intro EQ. unfold in_side in LEFT2; simpl in LEFT2, SCP, EQ.
             congruence. }
           assert (SPL1: Mem.set_perm_list m (blocks_of_env ge1 e) Readable = Some m').
           { match type of SET_PERM with if ?d then _ else _ => destruct d; [contradiction|] end.
             match type of SET_PERM with if ?d then _ else _ => destruct d; [contradiction|] end.
             exact SET_PERM. }
           assert (SPL2: Mem.set_perm_list m0 (blocks_of_env ge2 e0) Readable = Some m'0).
           { match type of SET_PERM0 with if ?d then _ else _ => destruct d; [contradiction|] end.
             match type of SET_PERM0 with if ?d then _ else _ => destruct d; [contradiction|] end.
             exact SET_PERM0. }
           (* Step 1: handle left program's set_perm *)
           assert (LEFT1' : s (comp_of f) = Left).
           { exact LEFT1. }
           assert (RMI1: right_mem_injection s j ge1 ge2 m' m0).
           { eapply right_mem_injection_set_perm_list_left; eauto.
             intros b0 [lo [hi IN]].
             eapply (env_blocks_unmapped_via_same_domain j ge1 m e b0 (comp_of f)).
             - exact (same_dom _ _ _ _ _ _ RMI).
             - exact (same_blks1 _ _ _ _ _ _ RMI).
             - exact LEFT1'.
             - intros b' lo' hi' IN'.
               split; [exact (state_inv_env_above _ _ SI1 _ _ _ IN') |
                       exact (proj1 (state_inv_env_blocks_info _ _ SI1 _ _ _ IN'))].
             - eauto. }
           (* Step 2: handle right program's set_perm *)
           assert (LEFT2' : s (comp_of f0) = Left).
           { exact LEFT2. }
           eapply right_mem_injection_set_perm_list_left'; eauto.
           intros b0 [lo [hi IN]].
           pose proof (state_inv_env_blocks_info _ _ SI2) as EBI.
           pose proof (state_inv_env_above _ _ SI2) as EA.
           specialize (EBI _ _ _ IN).
           destruct EBI as [COMP NDEF].
           split.
           ++ exact (eq_ind_r (fun c => s c = Left) LEFT2' COMP).
           ++ exact NDEF.
        -- (* right_cont_injection (Kcall optid f e le k) (Kcall optid0 f0 e0 le0 k0) *)
           apply right_cont_injection_kcall_left.
           ++ (* s |= f ∈ Left *)
              exact LEFT1.
           ++ (* comp_of f = comp_of f0 *)
              simpl in LEFT1, LEFT2. unfold in_side in LEFT1, LEFT2.
              simpl in LEFT1, LEFT2.
              symmetry. assumption.
           ++ (* right_cont_injection (remove_until_right k) (remove_until_right k0) *)
              exact RCINJ.
        -- (* Val.inject_list j vargs vargs *)
           clear - NO_CROSS_PTR H4.
           specialize (NO_CROSS_PTR H4).
           induction vargs; constructor.
           ++ inv NO_CROSS_PTR. destruct a; simpl in H1; try contradiction; constructor.
           ++ apply IHvargs. inv NO_CROSS_PTR. assumption.
      * (* step_builtin: impossible — ec_no_crossing *)
        exfalso. pose proof (ec_no_crossing' _ _ _ _ _ _ _ _ H8). discriminate.
      * (* step_external_function: impossible — ec_no_crossing *)
        exfalso. pose proof (ec_no_crossing' _ _ _ _ _ _ _ _ H5). discriminate.
      * (* step_returnstate: impossible — return_trace can't produce Event_call *)
        inv EV; discriminate.
    + (* step_builtin: contradicts LEFT1/RIGHT1' *)
      simpl in LEFT1, RIGHT1'; congruence.
    + (* step_external_function: contradicts LEFT1/RIGHT1' *)
      exfalso.
      unfold in_side in LEFT1, RIGHT1'; simpl in LEFT1, RIGHT1'.
      destruct (cp_eq_dec bottom bottom); congruence.
    + (* step_returnstate: Left→Right cross-compartment return *)
      (* Establish s (comp_of f) = Right from RIGHT1' *)
      assert (RIGHT_F: s (comp_of f) = Right) by exact RIGHT1'.
      (* Establish that cp0 ≠ bottom *)
      assert (CP0_NOT_BOTTOM: cp0 <> bottom).
      { intro EQ. subst cp0.
        assert (LEFT_F: s (comp_of f) = Left) by exact LEFT1.
        congruence. }
      (* Establish s cp0 = Left *)
      assert (LEFT_CP0: s cp0 = Left).
      { unfold in_side in LEFT1. simpl in LEFT1.
        destruct (cp_eq_dec cp0 bottom); [contradiction |]. exact LEFT1. }
      (* The return is cross-compartment *)
      assert (COMP_NEQ: comp_of f <> cp0).
      { intro EQ. congruence. }
      (* EV must be return_trace_cross *)
      inv EV; [simpl in TNC; discriminate |].
      (* Now t = [Event_return (comp_of f) cp0 res] *)
      simpl in TNC. inv TNC.
      (* cp = comp_of f, SCP gives s (comp_of f) = Right — consistent *)
      (* Rewrite RCINJ: remove_until_right on Right-side Kcall gives identity *)
      assert (RUR1: remove_until_right s (Kcall optid f e le k) = Kcall optid f e le k).
      { exact (remove_until_right_kcall_right s optid f e le k RIGHT_F). }
      (* Simplify cont_of in RCINJ *)
      change (cont_of (Returnstate v (Kcall optid f e le k) m ty cp0))
        with (Kcall optid f e le k) in RCINJ.
      rewrite RUR1 in RCINJ.
      (* Invert STEP2: only step_returnstate can produce Event_return *)
      inv STEP2; try discriminate.
      * (* step_call: Event_call ≠ Event_return *)
        inv EV; discriminate.
      * (* step_builtin: ec_no_crossing *)
        exfalso.
        match goal with
        | H: external_call _ _ _ _ _ _ _ _ |- _ =>
            pose proof (ec_no_crossing' _ _ _ _ _ _ _ _ H); discriminate
        end.
      * (* step_external_function: ec_no_crossing *)
        exfalso.
        match goal with
        | H: external_call _ _ _ _ _ _ _ _ |- _ =>
            pose proof (ec_no_crossing' _ _ _ _ _ _ _ _ H); discriminate
        end.
      * (* step_returnstate: the real case *)
        (* EV must also be return_trace_cross *)
        inv EV; try discriminate.
        (* After inv EV: H1: comp_of f0 = comp_of f, H9: eventval_match ge2 res ... v0 *)
        (* Rewrite RCINJ for s2's continuation *)
        assert (RIGHT_F0: s (comp_of f0) = Right) by exact RIGHT2'.
        assert (RUR2: remove_until_right s (Kcall optid0 f0 e0 le0 k0) = Kcall optid0 f0 e0 le0 k0).
        { exact (remove_until_right_kcall_right s optid0 f0 e0 le0 k0 RIGHT_F0). }
        change (cont_of (Returnstate v0 (Kcall optid0 f0 e0 le0 k0) m0 ty0 cp0))
          with (Kcall optid0 f0 e0 le0 k0) in RCINJ.
        rewrite RUR2 in RCINJ.
        (* Now RCINJ: right_cont_injection (Kcall optid f e le k) (Kcall optid0 f0 e0 le0 k0) *)
        (* Invert: must be right_cont_injection_kcall_right (since f is Right) *)
        inv RCINJ.
        -- (* right_cont_injection_kcall_left: s |= f ∈ Left, contradicts RIGHT_F *)
           exfalso.
           match goal with
           | H: s |= f ∈ Left |- _ => unfold in_side in H; simpl in H; congruence
           end.
        -- (* right_cont_injection_kcall_right: f0 = f, optid0 = optid *)
           (* Establish v0 = v from eventval_match + same res *)
           assert (V_EQ: v0 = v).
           { inv H0; inv H9; try congruence; try discriminate.
             (* EVptr_global case: contradicts not_ptr *)
             exfalso. exact (NO_CROSS_PTR H). }
           subst v0.
           (* Build inject_states *)
           apply inject_states.
           ++ (* right_mem_injection m' m'0 *)
              simpl in RMI.
              assert (SPL1: Mem.set_perm_list m (blocks_of_env ge1 e) Freeable = Some m').
              { destruct (cp_eq_dec (comp_of f0) cp0); [contradiction |].
                destruct (cp_eq_dec cp0 bottom); [contradiction |].
                exact SET_PERM. }
              assert (SPL2: Mem.set_perm_list m0 (blocks_of_env ge2 e0) Freeable = Some m'0).
              { match type of SET_PERM0 with if ?d then _ else _ => destruct d; [exfalso; apply COMP_NEQ; congruence |] end.
                match type of SET_PERM0 with if ?d then _ else _ => destruct d; [contradiction |] end.
                exact SET_PERM0. }
              eapply right_mem_injection_set_perm_list_both; eauto.
              ** constructor.
              ** pose proof (proj1 H15) as EINJ_SOME.
                 pose proof (proj2 H15) as EINJ_NONE.
                 intros b1 b2 delta JB. split.
                 --- (* forward: b1 in blocks_of_env ge1 e -> b2 in blocks_of_env ge2 e0 *)
                     intros [lox [hix INx]].
                     unfold blocks_of_env in INx. rewrite in_map_iff in INx.
                     destruct INx as [[idx [bx tyx]] [EQx ELEMx]]. simpl in EQx. inv EQx.
                     apply PTree.elements_complete in ELEMx.
                     destruct (EINJ_SOME _ _ _ ELEMx) as [b2' [JBx E0x]].
                     assert (b2' = b2 /\ delta = 0%Z) by (rewrite JB in JBx; inv JBx; auto).
                     destruct H2 as [-> ->].
                     exists 0, (Ctypes.sizeof ge2 tyx).
                     unfold blocks_of_env. rewrite in_map_iff.
                     exists (idx, (b2, tyx)). split; [reflexivity |].
                     apply PTree.elements_correct. exact E0x.
                 --- (* backward: b2 in blocks_of_env ge2 e0 -> b1 in blocks_of_env ge1 e *)
                     intros [lox [hix INx]].
                     unfold blocks_of_env in INx. rewrite in_map_iff in INx.
                     destruct INx as [[idx [bx tyx]] [EQx ELEMx]]. simpl in EQx. inv EQx.
                     apply PTree.elements_complete in ELEMx.
                     (* e0!idx = Some(b2,tyx). Contrapositive of EINJ_NONE: e!idx <> None *)
                     destruct (e ! idx) as [[b1' ty']|] eqn:E1ID.
                     +++ destruct (EINJ_SOME _ _ _ E1ID) as [b2' [JBx' E0x']].
                         rewrite E0x' in ELEMx. inv ELEMx.
                         (* j b1' = Some(b2, 0) and j b1 = Some(b2, delta) *)
                         assert (DZ: delta = 0%Z) by (eapply (j_delta_zero _ _ _ _ _ _ RMI); eauto).
                         subst delta.
                         assert (b1 = b1') by (eapply (j_injective _ _ _ _ _ _ RMI); eauto).
                         subst b1'.
                         exists 0, (Ctypes.sizeof ge1 tyx).
                         unfold blocks_of_env. rewrite in_map_iff.
                         exists (idx, (b1, tyx)). split; [reflexivity |].
                         apply PTree.elements_correct. exact E1ID.
                     +++ pose proof (EINJ_NONE _ E1ID). congruence.
           ++ (* right_cont_injection k k0 *)
              assumption.
           ++ (* right_env_injection e e0 *)
              assumption.
           ++ (* right_tenv_injection (set_opttemp optid0 v le) (set_opttemp optid0 v le0) *)
              unfold set_opttemp. destruct optid0.
              ** intros id w. rewrite ! PTree.gsspec.
                 destruct (peq id i).
                 --- intros [= <-]. exists v. split; [| reflexivity].
                     destruct v; try constructor.
                     (* Vptr case: contradicts not_ptr *)
                     exfalso. exact (NO_CROSS_PTR H).
                 --- match goal with
                     | TINJ: right_tenv_injection _ _ _ |- _ => exact (TINJ id w)
                     end.
              ** match goal with
                 | TINJ: right_tenv_injection _ _ _ |- _ => exact TINJ
                 end.
  Qed.

  (* duplicate parallel_abstract_t removed — see line 2679 *)

Definition comp_of_event_or_default (e: event) (cp: compartment) :=
  match e with
  | Event_syscall _ _ _ _ _ => cp
  | Event_vload _ _ _ _ => cp
  | Event_vstore _ _ _ _ => cp
  | Event_annot _ _ => cp
  | Event_call _ cp' _ _ => cp'
  | Event_return cp' _ _ => cp'  (* return-TO compartment *)
  end.

Fixpoint last_comp_in_trace' (t: trace) (cp: compartment): compartment :=
  match t with
  | nil => cp
  | e :: t' => last_comp_in_trace' t' (comp_of_event_or_default e cp)
  end.

Definition last_comp_in_trace (t: trace): compartment :=
  last_comp_in_trace' t bottom.

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

Lemma parallel_concrete_star_E0: forall {j s1 s1a s1b s2 s2a s2b} (e: event),
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s1 ∈ Right ->
  state_wf s1 ->
  state_wf s2 ->
  state_inv ge1 s1 ->
  state_inv ge2 s2 ->
  Star (semantics1 W1) s1 E0 s1a ->
  Step (semantics1 W1) s1a (e :: nil) s1b ->
  Star (semantics1 W2) s2 E0 s2a ->
  Step (semantics1 W2) s2a (e :: nil) s2b ->
exists j',
  right_state_injection s j' ge1 ge2 s1a s2a.
Proof.
  intros j s1 s1a s1b s2 s2a s2b e INJ RIGHT WF1 WF2 SI1 SI2 STAR1 STEP1 STAR2 STEP2.
  simpl in *.
  assert (PROPER1: forall b f, Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W1 | eapply no_top_W1]; eauto).
  assert (PROPER2: forall b f, Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W2 | eapply no_top_W2]; eauto).
  revert j s2 s2a s2b INJ RIGHT WF1 WF2 SI1 SI2 STEP1 STAR2 STEP2.
  pattern s1, s1a; eapply star_E0_ind; eauto.
  - (* Base case: s0 = s1a, step1 s0 (e::nil) s1b available *)
    intros s0 j0 s2 s2a s2b INJ RIGHT WF_1 WF_2 SI_1 SI_2 STEP1 STAR2 STEP2.
    (* W1 takes event step e from s0. By parallel_concrete, W2 takes event step e from s2. *)
    destruct (parallel_concrete _ _ _ _ _ INJ RIGHT SI_1 SI_2 STEP1) as (j' & s2' & STEP2' & _).
    (* W2 can't take E0 steps from s2, since it also takes event step e from s2 *)
    assert (s2 = s2a).
    { inv STAR2; [reflexivity |].
      symmetry in H1. destruct (Eapp_E0_inv _ _ H1) as [-> ->].
      exfalso. eapply step1_E0_event_False; eauto. }
    subst. exists j0. exact INJ.
  - (* Inductive case: s0 ->_{E0} s0' then IH for s0' *)
    intros s0 s0' s0'' STEP0 IH j0 s2 s2a s2b INJ RIGHT WF_1 WF_2 SI_1 SI_2 STEP1 STAR2 STEP2.
    (* By parallel_concrete, W2 takes E0 step from s2 *)
    destruct (parallel_concrete _ _ _ _ _ INJ RIGHT SI_1 SI_2 STEP0) as (j' & s2' & STEP2' & INJ').
    (* Decompose W2's E0 star: first step must go to s2' by determinism *)
    assert (STAR2': star (step1 cpm2) ge2 s2' E0 s2a).
    { inv STAR2.
      - (* Star is empty: s2 = s2a, but s2 takes E0 step, contradicts event step *)
        exfalso. eapply step1_E0_event_False; eauto.
      - (* Star is non-empty *)
        symmetry in H1. destruct (Eapp_E0_inv _ _ H1) as [-> ->].
        assert (s2' = s4) by (eapply step1_E0_determ; eauto). subst.
        exact H0. }
    (* s0' is still Right *)
    assert (RIGHT': s |= s0' ∈ Right).
    { destruct INJ' as [LEFT1 LEFT2 | RIGHT1 RIGHT2]; [| exact RIGHT1].
      exfalso.
      apply (state_split_contra _ LEFT1).
      apply (step_E0_same_side ge1 _ _ _ Right PROPER1 WF_1 STEP0). exact RIGHT. }
    (* Thread state_wf *)
    assert (WF_1': state_wf s0').
    { eapply (step_E0_state_wf_preserved ge1). exact PROPER1. exact STEP0. exact WF_1. }
    assert (WF_2': state_wf s2').
    { eapply (step_E0_state_wf_preserved ge2). exact PROPER2. exact STEP2'. exact WF_2. }
    (* Thread state_inv *)
    assert (SI_1': state_inv ge1 s0').
    { eapply state_inv_step; eauto. }
    assert (SI_2': state_inv ge2 s2').
    { eapply state_inv_step; eauto. }
    eapply IH; eauto.
Qed.

Lemma parallel_abstract_star_E0: forall {j s1 s1a s1b s2 s2a s2b e},
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s1 ∈ Left ->
  state_wf s1 ->
  state_wf s2 ->
  state_inv ge1 s1 ->
  state_inv ge2 s2 ->
  Star (semantics1 W1) s1 E0 s1a ->
  Step (semantics1 W1) s1a (e :: nil) s1b ->
  Star (semantics1 W2) s2 E0 s2a ->
  Step (semantics1 W2) s2a (e :: nil) s2b ->
  right_state_injection s j ge1 ge2 s1a s2a.
Proof.
  intros j s1 s1a s1b s2 s2a s2b e INJ LEFT WF1 WF2 SI1 SI2 STAR1 STEP1 STAR2 STEP2.
  simpl in *.
  assert (PROPER1: forall b f, Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W1 | eapply no_top_W1]; eauto).
  assert (PROPER2: forall b f, Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W2 | eapply no_top_W2]; eauto).
  (* Process W1's E0 steps, threading state_inv through *)
  assert (INJ1: right_state_injection s j ge1 ge2 s1a s2).
  { revert INJ LEFT WF1 SI1.
    pattern s1, s1a; eapply star_E0_ind; eauto.
    intros s0 s0' s0'' STEP_E0 IH INJ0 LEFT0 WF0 SI0.
    assert (LEFT0': s |= s0' ∈ Left).
    { apply (step_E0_same_side ge1 _ _ _ Left PROPER1 WF0 STEP_E0). exact LEFT0. }
    assert (WF0': state_wf s0').
    { eapply (step_E0_state_wf_preserved ge1). exact PROPER1. exact STEP_E0. exact WF0. }
    assert (SI0': state_inv ge1 s0').
    { eapply state_inv_step; eauto. }
    apply IH; [| exact LEFT0' | exact WF0' | exact SI0'].
    pose proof (right_state_injection_left_rmi INJ0 LEFT0) as RMI0.
    eapply parallel_abstract_1; eauto.
    - exact (state_inv_gfun_no_perm _ _ SI0).
    - (* env_blocks_unmapped: derive from same_domain_right + same_blocks *)
      pose proof (state_inv_env_above _ _ SI0) as ENV_ABOVE0.
      pose proof (state_inv_env_blocks_info _ _ SI0) as ENV_INFO0.
      destruct s0; simpl in *; auto.
      + intros b0 EX.
        eapply (env_blocks_unmapped_via_same_domain j ge1 _ _ b0 (comp_of f));
          [exact (same_dom _ _ _ _ _ _ RMI0) | exact (same_blks1 _ _ _ _ _ _ RMI0) | exact LEFT0 |
           intros b' lo' hi' IN'; split; [exact (ENV_ABOVE0 _ _ _ IN') | exact (proj1 (ENV_INFO0 _ _ _ IN'))] | exact EX].
      + destruct k; simpl in *; auto.
        intros b0 EX.
        assert (COMP_F_LEFT: s (comp_of f) = Left).
        { inv STEP_E0; simpl in LEFT0'; exact LEFT0'. }
        eapply (env_blocks_unmapped_via_same_domain j ge1 _ _ b0 (comp_of f));
          [exact (same_dom _ _ _ _ _ _ RMI0) | exact (same_blks1 _ _ _ _ _ _ RMI0) | exact COMP_F_LEFT |
           intros b' lo' hi' IN'; split; [exact (ENV_ABOVE0 _ _ _ IN') | exact (proj1 (ENV_INFO0 _ _ _ IN'))] | exact EX]. }
  assert (LEFT_A: s |= s1a ∈ Left).
  { revert LEFT WF1. pattern s1, s1a; eapply star_E0_ind; eauto.
    intros s0 s0' s0'' STEP_E0 IH LEFT0 WF0.
    assert (WF0': state_wf s0').
    { eapply (step_E0_state_wf_preserved ge1). exact PROPER1. exact STEP_E0. exact WF0. }
    apply IH; [| exact WF0'].
    apply (step_E0_same_side ge1 _ _ _ Left PROPER1 WF0 STEP_E0). exact LEFT0. }
  assert (LEFT2: s |= s2 ∈ Left).
  { eauto using right_state_injection_same_side_right. }
  (* Process W2's E0 steps, threading state_inv through *)
  revert INJ1 LEFT2 WF2 SI2.
  pattern s2, s2a; eapply star_E0_ind; eauto.
  intros s0 s0' s0'' STEP_E0 IH INJ0 LEFT0 WF0 SI0.
  assert (LEFT0': s |= s0' ∈ Left).
  { apply (step_E0_same_side ge2 _ _ _ Left PROPER2 WF0 STEP_E0). exact LEFT0. }
  assert (WF0': state_wf s0').
  { eapply (step_E0_state_wf_preserved ge2). exact PROPER2. exact STEP_E0. exact WF0. }
  assert (SI0': state_inv ge2 s0').
  { eapply state_inv_step; eauto. }
  apply IH; [| exact LEFT0' | exact WF0' | exact SI0'].
  eapply parallel_abstract_2; eauto.
  - exact (state_inv_gfun_no_perm _ _ SI0).
  - exact (state_inv_env_blocks_info _ _ SI0).
Qed.

(* Related to old [context_epsilon_star_is_silent'] *)
Lemma parallel_star_E0: forall {j s1 s1' s1'' s2 s2' s2'' e},
  right_state_injection s j ge1 ge2 s1 s2 ->
  state_wf s1 ->
  state_wf s2 ->
  state_inv ge1 s1 ->
  state_inv ge2 s2 ->
  Star (semantics1 W1) s1 E0 s1' ->
  Step (semantics1 W1) s1' (e :: nil) s1'' ->
  Star (semantics1 W2) s2 E0 s2' ->
  Step (semantics1 W2) s2' (e :: nil) s2'' ->
exists j',
  right_state_injection s j' ge1 ge2 s1' s2'.
Proof.
  intros j s1.
  destruct (state_split_decidable s1) as [LEFT | RIGHT].
  - intros. exists j. eapply parallel_abstract_star_E0; eassumption.
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
  state_wf s1 ->
  state_wf s2 ->
  state_inv ge1 s1 ->
  state_inv ge2 s2 ->
  Star (semantics1 W1) s1 (t ** t1) s1'' ->
  Star (semantics1 W2) s2 (t ** t2) s2'' ->
  exists s1' s2' j',
    Star (semantics1 W1) s1 t s1' /\
    Star (semantics1 W2) s2 t s2' /\
    Star (semantics1 W1) s1' t1 s1'' /\
    Star (semantics1 W2) s2' t2 s2'' /\
    right_state_injection s j' ge1 ge2 s1' s2' /\
    state_wf s1' /\
    state_wf s2' /\
    state_inv ge1 s1' /\
    state_inv ge2 s2'.
Proof.
  assert (PROPER1: forall b f, Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W1 | eapply no_top_W1]; eauto).
  assert (PROPER2: forall b f, Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W2 | eapply no_top_W2]; eauto).
  intros j s1 s2 s1'' s2'' t; revert j s1 s2 s1'' s2''.
  induction t as [| e t IH];
    intros j s1 s2 s1'' s2'' t1 t2 RINJ WF1 WF2 SI1 SI2 STAR1 STAR2;
    (* Base case: follows trivially from the assumptions *)
    [exists s1, s2, j;
     exact (conj (star_refl _ _ _) (conj (star_refl _ _ _)
       (conj STAR1 (conj STAR2 (conj RINJ (conj WF1 (conj WF2 (conj SI1 SI2)))))))) |].
  (* Inductive case *)
  destruct (star_cons_inv (sr_traces (semantics_receptive _)) STAR1)
    as (s1_1 & s1_2 & STAR1_1 & STEP1_2 & STAR1_3).
  change (_ t t1) with (t ** t1) in STAR1_3. clear STAR1.
  destruct (star_cons_inv (sr_traces (semantics_receptive _)) STAR2)
    as (s2_1 & s2_2 & STAR2_1 & STEP2_2 & STAR2_3).
  change (_ t t2) with (t ** t2) in STAR2_3. clear STAR2.
  (* Compute state_wf at the event step points *)
  assert (WF1_1: state_wf s1_1).
  { eapply (star_state_wf_preserved ge1). exact PROPER1. exact STAR1_1. exact WF1. }
  assert (WF2_1: state_wf s2_1).
  { eapply (star_state_wf_preserved ge2). exact PROPER2. exact STAR2_1. exact WF2. }
  assert (WF1_2: state_wf s1_2).
  { eapply (step_state_wf_preserved ge1). exact PROPER1. exact STEP1_2. exact WF1_1. }
  assert (WF2_2: state_wf s2_2).
  { eapply (step_state_wf_preserved ge2). exact PROPER2. exact STEP2_2. exact WF2_1. }
  (* Compute state_inv at the event step points *)
  assert (SI1_1: state_inv ge1 s1_1) by (eapply state_inv_star; eassumption).
  assert (SI2_1: state_inv ge2 s2_1) by (eapply state_inv_star; eassumption).
  assert (SI1_2: state_inv ge1 s1_2).
  { eapply state_inv_step. exact STEP1_2. exact SI1_1. }
  assert (SI2_2: state_inv ge2 s2_2).
  { eapply state_inv_step. exact STEP2_2. exact SI2_1. }
  (* Case split on which side s1 is on *)
  destruct (state_split_decidable s1) as [LEFT | RIGHT].
  - (* Left side: j unchanged through E0 steps, use parallel_abstract_t *)
    assert (LEFT_1: s |= s1_1 ∈ Left).
    { pose proof STAR1_1 as STAR. simpl in STAR.
      exact (proj1 (star_E0_same_side ge1 cpm1 s1 s1_1 Left PROPER1 WF1 STAR) LEFT). }
    assert (RINJ1: right_state_injection s j ge1 ge2 s1_1 s2_1).
    { eapply parallel_abstract_star_E0; eauto. }
    assert (RINJ2: right_state_injection s j ge1 ge2 s1_2 s2_2).
    { exact (parallel_abstract_t _ _ _ _ _ _ RINJ1 LEFT_1 WF1_1 WF2_1 SI1_1 SI2_1 STEP1_2 STEP2_2). }
    destruct (IH j s1_2 s2_2 s1'' s2'' t1 t2 RINJ2 WF1_2 WF2_2 SI1_2 SI2_2 STAR1_3 STAR2_3)
      as (s1' & s2' & j'' & STAR1' & STAR2' & STAR1'' & STAR2'' & RINJ'' & WF1' & WF2' & SI1' & SI2').
    exists s1'. exists s2'. exists j''.
    assert (STAR1_comp: Star (semantics1 W1) s1 (e :: t) s1').
    { eapply star_trans; [exact STAR1_1 | eapply star_step; [exact STEP1_2 | exact STAR1' | reflexivity] | reflexivity]. }
    assert (STAR2_comp: Star (semantics1 W2) s2 (e :: t) s2').
    { eapply star_trans; [exact STAR2_1 | eapply star_step; [exact STEP2_2 | exact STAR2' | reflexivity] | reflexivity]. }
    exact (conj STAR1_comp (conj STAR2_comp (conj STAR1'' (conj STAR2'' (conj RINJ'' (conj WF1' (conj WF2' (conj SI1' SI2')))))))).
  - (* Right side: j may change through parallel_concrete *)
    assert (RIGHT_1: s |= s1_1 ∈ Right).
    { pose proof STAR1_1 as STAR. simpl in STAR.
      exact (proj1 (star_E0_same_side ge1 cpm1 s1 s1_1 Right PROPER1 WF1 STAR) RIGHT). }
    destruct (parallel_concrete_star_E0 e RINJ RIGHT WF1 WF2 SI1 SI2 STAR1_1 STEP1_2 STAR2_1 STEP2_2) as [j1 RINJ1].
    destruct (parallel_concrete _ _ _ _ _ RINJ1 RIGHT_1 SI1_1 SI2_1 STEP1_2) as (j2 & s2_step & STEP2_conc & RINJ2).
    assert (s2_step = s2_2) by (eapply step1_event_determ; eauto). subst s2_step.
    destruct (IH j2 s1_2 s2_2 s1'' s2'' t1 t2 RINJ2 WF1_2 WF2_2 SI1_2 SI2_2 STAR1_3 STAR2_3)
      as (s1' & s2' & j'' & STAR1' & STAR2' & STAR1'' & STAR2'' & RINJ'' & WF1' & WF2' & SI1' & SI2').
    exists s1'. exists s2'. exists j''.
    assert (STAR1_comp: Star (semantics1 W1) s1 (e :: t) s1').
    { eapply star_trans; [exact STAR1_1 | eapply star_step; [exact STEP1_2 | exact STAR1' | reflexivity] | reflexivity]. }
    assert (STAR2_comp: Star (semantics1 W2) s2 (e :: t) s2').
    { eapply star_trans; [exact STAR2_1 | eapply star_step; [exact STEP2_2 | exact STAR2' | reflexivity] | reflexivity]. }
    exact (conj STAR1_comp (conj STAR2_comp (conj STAR1'' (conj STAR2'' (conj RINJ'' (conj WF1' (conj WF2' (conj SI1' SI2')))))))).
Qed.

(* Helper: if s1 is Right with non-E0 trace and s2 reaches stuck via E0 only, contradiction. *)
Lemma right_E0_star_nostep_false: forall j0 s1_0 s2_0 s2_end s1_end t,
  right_state_injection s j0 ge1 ge2 s1_0 s2_0 ->
  s |= s1_0 ∈ Right ->
  state_wf s1_0 -> state_wf s2_0 ->
  state_inv ge1 s1_0 -> state_inv ge2 s2_0 ->
  Star (semantics1 W1) s1_0 t s1_end ->
  t <> E0 ->
  Star (semantics1 W2) s2_0 E0 s2_end ->
  Nostep (semantics1 W2) s2_end ->
  False.
Proof.
  assert (PROPER1: forall b f, Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W1 | eapply no_top_W1]; eauto).
  assert (PROPER2: forall b f, Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W2 | eapply no_top_W2]; eauto).
  intros j0 s1_0 s2_0 s2_end s1_end t PART RIGHT1 WF1 WF2 SI1 SI2 STAR1 HNE STAR2 NOSTEP.
  revert j0 s1_0 s1_end t PART RIGHT1 WF1 WF2 SI1 SI2 STAR1 HNE NOSTEP.
  pattern s2_0, s2_end; eapply star_E0_ind; eauto.
  - (* Base: s2_0 = s2_end. s1 can step, parallel_concrete gives s2 step, contradicts Nostep. *)
    intros s0 j1 s1_1 s1_e t0 PART0 RIGHT_1 WF_1 WF_2 SI_1 SI_2 STAR0 HNE0 NOSTEP0.
    inv STAR0; [congruence |].
    destruct (parallel_concrete _ _ _ _ _ PART0 RIGHT_1 SI_1 SI_2 H) as (_ & ? & STEP2' & _).
    eapply NOSTEP0; simpl; exact STEP2'.
  - (* Step: s0 →E0 s0', IH for (s0', s2_end). *)
    intros s0 s0' s0'' STEP_E0 IH j1 s1_1 s1_e t0 PART0 RIGHT_1 WF_1 WF_2 SI_1 SI_2 STAR0 HNE0 NOSTEP0.
    inv STAR0; [congruence |].
    destruct (parallel_concrete _ _ _ _ _ PART0 RIGHT_1 SI_1 SI_2 H) as (j2 & s2_n & STEP2_0 & PART1).
    (* t1 is E0 or singleton (by single_events) *)
    destruct t1 as [| e0 t1'].
    + (* t1 = E0: align E0 steps, apply IH *)
      assert (s2_n = s0') by (eapply step1_E0_determ; eauto). subst s2_n.
      simpl in HNE0. simpl in H. simpl in STEP_E0.
      eapply IH; try exact PART1; try exact H0; try exact HNE0; try exact NOSTEP0.
      * apply (step_E0_same_side ge1 _ _ _ Right PROPER1 WF_1 H). exact RIGHT_1.
      * exact (step_state_wf_preserved _ _ _ _ _ PROPER1 H WF_1).
      * exact (step_state_wf_preserved _ _ _ _ _ PROPER2 STEP_E0 WF_2).
      * exact (state_inv_step _ _ _ _ _ H SI_1).
      * exact (state_inv_step _ _ _ _ _ STEP_E0 SI_2).
    + (* t1 = e0 :: t1': s0 takes both E0 and event step, contradiction *)
      exfalso.
      pose proof (sr_traces (semantics_receptive _) _ _ _ H) as Hlen.
      simpl in Hlen. destruct t1'; [| simpl in Hlen; lia].
      eapply step1_E0_event_False. exact STEP_E0. exact STEP2_0.
Qed.

Lemma parallel_exec j s1 s1' s2 s2' n t t':
  right_state_injection s j ge1 ge2 s1 s2 ->
  state_wf s1 ->
  state_wf s2 ->
  state_inv ge1 s1 ->
  state_inv ge2 s2 ->
  Star (semantics1 W1) s1 (t ** t') s1' ->
  Star (semantics1 W2) s2  t        s2' ->
  Nostep (semantics1 W2) s2' ->
  Smallstep.final_state (semantics1 W1) s1' n ->
  s |= s2' ∈ Right ->
  Smallstep.final_state (semantics1 W2) s2' n.
Proof.
  rewrite <- (E0_right t) at 2.
  intros part wf1 wf2 si1 si2 star1 star2.
  exploit parallel_exec1; eauto.
  clear j star1 star2 part wf1 wf2 si1 si2.
  intros (s1'' & s2'' & (j' & _ & _ & star1 & star2 & part & wf1 & wf2 & si1 & si2)).
  clear s1 s2 t. rename s1'' into s1. rename s2'' into s2. rename j' into j.
  intros nostep2 final1 in_prog.
  (* s1 must be Right *)
  assert (PROPER1: forall b f, Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W1 | eapply no_top_W1]; eauto).
  assert (PROPER2: forall b f, Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W2 | eapply no_top_W2]; eauto).
  destruct (state_split_decidable s1) as [LEFT1 | RIGHT1].
  { (* s1 Left → s2 Left → s2' Left → contradicts in_prog *)
    exfalso.
    assert (LEFT2: s |= s2 ∈ Left).
    { destruct part as [L1 L2 | R1 R2]; [exact L2 | exfalso; eapply state_split_contra; eauto]. }
    eapply state_split_contra; [| exact in_prog].
    apply (star_E0_same_side ge2 _ _ _ Left PROPER2 wf2 star2). exact LEFT2. }
  (* t' must be E0 *)
  destruct t' as [| e0 t''].
  2: { (* t' = e0 :: t'': non-E0 trace from Right, contradicts nostep via helper *)
    exfalso. eapply right_E0_star_nostep_false; eauto. discriminate. }
  (* t' = E0: both stars are E0 *)
  simpl in star1.
  (* Induction on star1 to align E0 steps and establish final_state *)
  revert j s2 star2 part RIGHT1 wf1 wf2 si1 si2 in_prog final1.
  pattern s1, s1'; eapply star_E0_ind; eauto.
  - (* Base: s1 = s1'. Extract injection, show s2 is final. *)
    intros s0 j0 s2_0 STAR2 PART0 RIGHT_1 WF_1 WF_2 SI_1 SI_2 IN_PROG final0.
    (* s0 is final: Returnstate (Vint n) Kstop m ty cp *)
    inv final0.
    (* PART0 is RightControl since s0 is Right *)
    destruct PART0 as [LEFT_1 | RIGHT_1' RIGHT_2' REI].
    { exfalso. simpl in *. congruence. }
    (* REI: right_executing_injection ge1 ge2 (Returnstate (Vint n) Kstop m ty cp) s2_0 *)
    inv REI.
    (* right_cont_injection Kstop k2 → k2 = Kstop *)
    (* right_cont_injection Kstop k2 → k2 = Kstop *)
    inv H6.
    (* Val.inject (Vint n) v' → v' = Vint n *)
    inv H7.
    (* s2_0 = Returnstate (Vint n) Kstop m2 ty cp, can't step *)
    (* star2 must be empty *)
    inv STAR2; [constructor | exfalso; simpl in H; inv H].
  - (* Step: s0 →E0 s0'. parallel_concrete aligns, IH continues. *)
    intros s0 s0' s0'' STEP_E0 IH j0 s2_0 STAR2 PART0 RIGHT_1 WF_1 WF_2 SI_1 SI_2 IN_PROG FINAL.
    destruct (parallel_concrete _ _ _ _ _ PART0 RIGHT_1 SI_1 SI_2 STEP_E0) as (j1 & s2_n & STEP2_E0 & PART1).
    (* Decompose star2 *)
    inv STAR2.
    + (* star2 empty: s2_0 = s2', can't step, contradicts STEP2_E0 *)
      exfalso. eapply nostep2; simpl; exact STEP2_E0.
    + (* star2 non-empty: first E0 step *)
      destruct (app_eq_nil _ _ (eq_sym H1)) as [-> ->].
      assert (s2_n = s3) by (eapply step1_E0_determ; eauto). subst s3.
      eapply IH; eauto.
      * apply (step_E0_same_side ge1 _ _ _ Right PROPER1 WF_1 STEP_E0). exact RIGHT_1.
      * eapply (step_state_wf_preserved ge1); eauto.
      * eapply (step_state_wf_preserved ge2); eauto.
      * eapply state_inv_step; eauto.
      * eapply state_inv_step; eauto.
Qed.

Lemma parallel_exec' j s1 s1' s2 s2' t e t':
  right_state_injection s j ge1 ge2 s1 s2 ->
  state_wf s1 ->
  state_wf s2 ->
  state_inv ge1 s1 ->
  state_inv ge2 s2 ->
  Star (semantics1 W1) s1 (t ** e :: t') s1' ->
  Star (semantics1 W2) s2  t             s2' ->
  Nostep (semantics1 W2) s2' ->
  s |= s2' ∈ Left.
Proof.
  rewrite <- (E0_right t) at 2.
  intros part wf1 wf2 si1 si2 star1 star2.
  exploit parallel_exec1; eauto.
  clear j star1 star2 part wf1 wf2 si1 si2.
  intros (s1'' & s2'' & (j' & _ & _ & star1 & star2 & part & wf1 & wf2 & si1 & si2)).
  clear s1 s2 t. rename s1'' into s1. rename s2'' into s2. rename j' into j.
  intros nostep2.
  (* s2' is the stuck state. s2 is the mid-state from parallel_exec1.
     star2 : Star (semantics1 W2) s2 E0 s2'.
     First show s2 is Left, then transfer via star_E0_same_side. *)
  assert (PROPER2: forall b f, Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W2 | eapply no_top_W2]; eauto).
  destruct (state_split_decidable s2) as [LEFT2 | RIGHT2].
  - (* s2 Left => s2' Left via star_E0_same_side *)
    apply (star_E0_same_side ge2 _ _ _ Left PROPER2 wf2 star2). exact LEFT2.
  - (* s2 Right => contradiction via right_E0_star_nostep_false *)
    exfalso.
    assert (RIGHT1: s |= s1 ∈ Right).
    { destruct part as [LEFT1 LEFT_s2 | RIGHT1 RIGHT_s2]; [| exact RIGHT1].
      exfalso. eapply state_split_contra; eauto. }
    eapply right_E0_star_nostep_false; eauto. discriminate.
Qed.

Lemma last_comp_in_trace'_app t1 t2 cp:
  last_comp_in_trace' (t1 ++ t2) cp =
  last_comp_in_trace' t2 (last_comp_in_trace' t1 cp).
Proof.
  revert cp. induction t1 as [| e t1 IH]; simpl; auto.
Qed.

Lemma ec_trace_no_call_return ef ge0 cp0 vargs m t vres m' :
  external_call ef ge0 cp0 vargs m t vres m' ->
  forall e, In e t -> forall cp, comp_of_event_or_default e cp = cp.
Proof.
  intros EC e IN cp.
  exploit ec_no_crossing; eauto using external_call_spec.
  destruct t as [| e0 [| e1 t']].
  - inv IN.
  - simpl in IN. destruct IN as [<- | []].
    destruct e0; simpl; try reflexivity; intros []; auto.
  - exploit ec_trace_length; eauto using external_call_spec. simpl. lia.
Qed.

Lemma last_comp_in_trace'_ec ef ge0 cp0 vargs m t vres m' cp:
  external_call ef ge0 cp0 vargs m t vres m' ->
  last_comp_in_trace' t cp = cp.
Proof.
  intros EC.
  exploit ec_no_crossing; eauto using external_call_spec.
  destruct t as [| e0 [| e1 t']]; simpl; auto.
  - destruct e0; simpl; auto; intros [].
  - exploit ec_trace_length; eauto using external_call_spec. simpl. lia.
Qed.

(* Key invariant: last_comp_in_trace' tracks the side of the current state *)
Lemma step1_last_comp (ge0: genv) cpm0 s1 t s1' cp:
  (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  state_wf s1 ->
  step1 cpm0 ge0 s1 t s1' ->
  s cp = s (state_comp s1) ->
  s (last_comp_in_trace' t cp) = s (state_comp s1').
Proof.
  intros PROPER WF STEP HCP.
  inv STEP; simpl in *; try exact HCP.
  - (* step_call *)
    inv EV.
    + (* call_trace_intra: t = E0 *)
      simpl.
      destruct fd as [fi | ef tya tyr cc'].
      * (* Internal fi *)
        simpl.
        assert (FLOW: flowsto (comp_of fi) (comp_of f)).
        { simpl in *. unfold Genv.type_of_call in *.
          destruct (flowsto_dec (comp_of fi) (comp_of f)); [assumption | congruence]. }
        assert (HFD: exists b, Genv.find_def ge0 b = Some (Gfun (Internal fi))).
        { eapply find_funct_find_def_clight; eauto. }
        destruct HFD as [b' FD].
        destruct (PROPER _ _ FD) as [NB NT].
        destruct WF as [_ [WF_NT _]].
        assert (comp_of fi = comp_of f) by (eapply flowsto_no_bottom_no_top; eassumption).
        congruence.
      * (* External *) exact HCP.
    + (* call_trace_cross: t = Event_call :: nil *)
      simpl.
      destruct fd as [fi | ef tya tyr cc'].
      * (* Internal fi: call goes to comp_of fi *)
        simpl. reflexivity.
      * (* External fd: cross-comp call to bottom — impossible *)
        exfalso.
        unfold Genv.type_of_call in *; simpl in *.
        destruct (flowsto_dec bottom (comp_of f));
          [congruence | elim n; apply bottom_flowsto].
  - (* step_builtin *)
    erewrite last_comp_in_trace'_ec; eauto.
  - (* step_return_0 — E0 *)
    destruct WF as [NB _].
    destruct (cp_eq_dec (comp_of f) bottom); [congruence | exact HCP].
  - (* step_return_1 — E0 *)
    destruct WF as [NB _].
    destruct (cp_eq_dec (comp_of f) bottom); [congruence | exact HCP].
  - (* step_skip_call — E0 *)
    destruct WF as [NB _].
    destruct (cp_eq_dec (comp_of f) bottom); [congruence | exact HCP].
  - (* step_external_function *)
    erewrite last_comp_in_trace'_ec; eauto.
  - (* step_returnstate *)
    inv EV.
    + (* return_trace_intra: t = E0 *)
      simpl.
      destruct WF as [NB' [NT' KP']].
      destruct (cp_eq_dec cp0 bottom) as [-> | NB].
      * (* cp0 = bottom: state_comp before = comp_of f *)
        exact HCP.
      * (* cp0 <> bottom: state_comp before = cp0 *)
        assert (FLOW: flowsto cp0 (comp_of f)).
        { simpl in *. unfold Genv.type_of_call in *.
          destruct (flowsto_dec cp0 (comp_of f)); [assumption | congruence]. }
        assert (cp0 = comp_of f) by (eapply flowsto_no_bottom_no_top; eassumption).
        congruence.
    + (* return_trace_cross: Event_return (comp_of f) cp0 :: nil *)
      simpl. reflexivity.
Qed.

Lemma star_last_comp (ge0: genv) cpm0 s1 t s2 cp:
  (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  state_wf s1 ->
  star (step1 cpm0) ge0 s1 t s2 ->
  s cp = s (state_comp s1) ->
  s (last_comp_in_trace' t cp) = s (state_comp s2).
Proof.
  intros PROPER WF STAR HCP.
  revert cp HCP.
  induction STAR; intros cp HCP.
  - simpl. exact HCP.
  - subst t. rewrite last_comp_in_trace'_app.
    assert (WF2: state_wf s2) by (eapply step_state_wf_preserved; eauto).
    apply IHSTAR; [exact WF2 |].
    eapply step1_last_comp with (s1 := s1); eauto.
Qed.

Lemma last_comp_in_trace'_side_eq t cp1 cp2:
  s cp1 = s cp2 ->
  s (last_comp_in_trace' t cp1) = s (last_comp_in_trace' t cp2).
Proof.
  revert cp1 cp2. induction t as [| e t IH]; simpl; auto.
  intros cp1 cp2 EQ. apply IH.
  destruct e; simpl; auto.
Qed.

(* Alternative: the first call/return event overwrites the initial cp *)
Lemma last_comp_in_trace'_call_overwrite t cp1 cp2 e t':
  t = e :: t' ->
  (exists cp cp' id vl, e = Event_call cp cp' id vl) \/
  (exists cp cp' res, e = Event_return cp cp' res) ->
  last_comp_in_trace' t cp1 = last_comp_in_trace' t cp2.
Proof.
  intros -> [[cp [cp' [id [vl ->]]]] | [cp [cp' [res ->]]]]; simpl; auto.
Qed.

Lemma last_comp_step_overwrite (ge0: genv) cpm0 s1 t s1' :
  (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  state_wf s1 ->
  step1 cpm0 ge0 s1 t s1' ->
  s (state_comp s1) <> s (state_comp s1') ->
  forall cp1 cp2, last_comp_in_trace' t cp1 = last_comp_in_trace' t cp2.
Proof.
  intros PROPER WF STEP DIFF.
  (* Side-changing steps must produce call/return events *)
  inv STEP; simpl in *; try congruence;
  try (exfalso; apply DIFF;
    repeat match goal with
    | |- context [cp_eq_dec ?a ?b] => destruct (cp_eq_dec a b); try congruence
    | H : _ /\ _ |- _ => destruct H
    end; congruence).
  - (* step_call *)
    inv EV.
    + (* call_trace_intra: E0 — side preserved → contradiction *)
      exfalso. apply DIFF. clear DIFF.
      destruct fd as [fi | ef tya tyr cc'].
      * simpl.
        assert (FLOW: flowsto (comp_of fi) (comp_of f)).
        { simpl in *. unfold Genv.type_of_call in *.
          destruct (flowsto_dec (comp_of fi) (comp_of f)); [assumption | congruence]. }
        destruct (find_funct_find_def_clight _ _ _ H2) as [b FD].
        destruct (PROPER _ _ FD) as [NB NT].
        destruct WF as [_ [WF_NT _]].
        replace (comp_of fi) with (comp_of f) by (symmetry; eapply flowsto_no_bottom_no_top; eassumption).
        reflexivity.
      * simpl. reflexivity.
    + (* call_trace_cross: Event_call :: nil — overwrites cp *)
      simpl. reflexivity.
  - (* step_returnstate *)
    inv EV.
    + (* return_trace_intra: E0 — side preserved → contradiction *)
      exfalso. apply DIFF. clear DIFF.
      destruct WF as [NB' [NT' KP']].
      destruct (cp_eq_dec cp bottom) as [-> | NB]; [reflexivity |].
      assert (FLOW: flowsto cp (comp_of f)).
      { simpl in *. unfold Genv.type_of_call in *.
        destruct (flowsto_dec cp (comp_of f)); [assumption | congruence]. }
      assert (cp = comp_of f) by (eapply flowsto_no_bottom_no_top; eassumption).
      congruence.
    + (* return_trace_cross: Event_return :: nil — overwrites cp *)
      simpl. reflexivity.
Qed.

(* If state goes from Right to Left, last_comp_in_trace' gives Left for any initial cp *)
Lemma star_last_comp_right_to_left (ge0: genv) cpm0 s1 t s2 :
  (forall b f, Genv.find_def ge0 b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top) ->
  state_wf s1 ->
  star (step1 cpm0) ge0 s1 t s2 ->
  s (state_comp s1) = Right ->
  s (state_comp s2) = Left ->
  forall cp, s (last_comp_in_trace' t cp) = Left.
Proof.
  intros PROPER WF STAR RIGHT LEFT.
  revert WF RIGHT LEFT.
  induction STAR; intros WF RIGHT LEFT.
  - (* Base: s1 = s2. Right = Left → contradiction *)
    congruence.
  - subst. intros cp.
    rewrite last_comp_in_trace'_app.
    assert (WF_MID: state_wf s2) by (eapply step_state_wf_preserved; eauto).
    destruct (s (state_comp s2)) eqn:MID_SIDE.
    + (* s2 is Left: step changes Right→Left, trace overwrites initial cp *)
      assert (OVR: forall cp1 cp2, last_comp_in_trace' t1 cp1 = last_comp_in_trace' t1 cp2).
      { apply last_comp_step_overwrite with ge0 cpm0 s1 s2; auto.
        rewrite RIGHT, MID_SIDE. discriminate. }
      rewrite OVR with (cp2 := state_comp s1).
      assert (STEP_LAST: s (last_comp_in_trace' t1 (state_comp s1)) = s (state_comp s2)).
      { eapply step1_last_comp with (s1 := s1); eauto. }
      rewrite <- LEFT.
      eapply star_last_comp with (s1 := s2); eauto; congruence.
    + (* s2 is Right: recurse *)
      apply IHSTAR; auto.
Qed.

Lemma blame_last_comp_star p s1 t s2
  (PROPER: forall b f, Genv.find_def (globalenv p) b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top):
  Smallstep.initial_state (semantics1 p) s1 ->
  Star (semantics1 p) s1 t s2 ->
  s |= s2 ∈ Left ->
  blame_on_program t.
Proof.
  intros INI STAR LEFT.
  unfold blame_on_program, last_comp_in_trace.
  simpl in LEFT.
  inv INI.
  assert (WF: state_wf (Callstate (Internal f) nil Kstop m0)).
  { simpl. split.
    - apply Genv.find_funct_ptr_iff in H1. exact (PROPER _ _ H1).
    - exact I. }
  destruct (s (comp_of f)) eqn:COMP_SIDE.
  - (* Main is Left: s bottom = Left = s (comp_of f) *)
    erewrite last_comp_in_trace'_side_eq with (cp2 := comp_of f);
      [| rewrite s_bottom_left; symmetry; exact COMP_SIDE].
    rewrite <- LEFT.
    eapply star_last_comp; try exact STAR; eauto.
  - (* Main is Right: state goes Right → Left, trace overwrites initial cp *)
    eapply star_last_comp_right_to_left; try exact STAR; eauto.
Qed.

Definition init_meminj_block (b: block): option block :=
  match Genv.invert_symbol ge1 b with
  | Some id =>
    match Genv.find_def ge1 b with
    | Some (Gfun _) =>
      (* Function definitions: always mapped *)
      match Genv.find_symbol ge2 id with
      | Some b' => Some b'
      | None => None
      end
    | Some (Gvar v) =>
      (* Variable definitions: only mapped if Right-side *)
      match s (comp_of v) with
      | Right =>
        match Genv.find_symbol ge2 id with
        | Some b' => Some b'
        | None => None
        end
      | Left => None
      end
    | None => None
    end
  | None => None
  end.

Definition init_meminj: meminj :=
  fun b =>
    match init_meminj_block b with
    | Some b' => Some (b', 0)
    | None => None
    end.

Lemma init_meminj_injective:
  forall b1 b1' b2,
    init_meminj b1 = Some (b2, 0) ->
    init_meminj b1' = Some (b2, 0) ->
    b1 = b1'.
Proof.
  intros b1 b1' b2 H1 H2.
  unfold init_meminj in H1, H2.
  destruct (init_meminj_block b1) as [b2a|] eqn:E1; [| congruence].
  destruct (init_meminj_block b1') as [b2b|] eqn:E2; [| congruence].
  inv H1. inv H2.
  unfold init_meminj_block in E1, E2.
  destruct (Genv.invert_symbol ge1 b1) as [id1|] eqn:S1; [| congruence].
  destruct (Genv.invert_symbol ge1 b1') as [id2|] eqn:S2; [| congruence].
  destruct (Genv.find_def ge1 b1) as [[fd1|v1]|] eqn:D1; try congruence;
  destruct (Genv.find_def ge1 b1') as [[fd2|v2]|] eqn:D2; try congruence.
  - (* Both Gfun *)
    destruct (Genv.find_symbol ge2 id1) eqn:FS1; [| congruence].
    destruct (Genv.find_symbol ge2 id2) eqn:FS2; [| congruence].
    inv E1. inv E2.
    assert (id1 = id2) by (eapply Genv.genv_vars_inj; eauto). subst id2.
    apply Genv.invert_find_symbol in S1. apply Genv.invert_find_symbol in S2.
    congruence.
  - (* Gfun / Gvar *)
    destruct (Genv.find_symbol ge2 id1) eqn:FS1; [| congruence].
    destruct (s (comp_of v2)) eqn:SIDE2; [congruence|].
    destruct (Genv.find_symbol ge2 id2) eqn:FS2; [| congruence].
    inv E1. inv E2.
    assert (id1 = id2) by (eapply Genv.genv_vars_inj; eauto). subst id2.
    apply Genv.invert_find_symbol in S1. apply Genv.invert_find_symbol in S2.
    congruence.
  - (* Gvar / Gfun *)
    destruct (s (comp_of v1)) eqn:SIDE1; [congruence|].
    destruct (Genv.find_symbol ge2 id1) eqn:FS1; [| congruence].
    destruct (Genv.find_symbol ge2 id2) eqn:FS2; [| congruence].
    inv E1. inv E2.
    assert (id1 = id2) by (eapply Genv.genv_vars_inj; eauto). subst id2.
    apply Genv.invert_find_symbol in S1. apply Genv.invert_find_symbol in S2.
    congruence.
  - (* Both Gvar *)
    destruct (s (comp_of v1)) eqn:SIDE1; [congruence|].
    destruct (Genv.find_symbol ge2 id1) eqn:FS1; [| congruence].
    destruct (s (comp_of v2)) eqn:SIDE2; [congruence|].
    destruct (Genv.find_symbol ge2 id2) eqn:FS2; [| congruence].
    inv E1. inv E2.
    assert (id1 = id2) by (eapply Genv.genv_vars_inj; eauto). subst id2.
    apply Genv.invert_find_symbol in S1. apply Genv.invert_find_symbol in S2.
    congruence.
Qed.

Lemma find_symbol_init_mem_compartment (pr: program) m1 id b
      (SYM: Genv.find_symbol (Genv.globalenv pr) id = Some b)
      (MEM: Genv.init_mem pr = Some m1):
  Genv.find_comp_of_ident (Genv.globalenv pr) id =
  Mem.block_compartment m1 b.
Proof.
  unfold Genv.find_comp_of_ident. rewrite SYM.
  unfold Genv.find_comp_of_block.
  pose proof (init_mem_same_blocks pr m1 MEM) as SB.
  destruct (Genv.find_def (Genv.globalenv pr) b) eqn:DEF.
  - symmetry. exact (same_blocks_comp _ _ SB _ _ DEF).
  - pose proof SYM as SYM0.
    apply Genv.find_symbol_inversion in SYM0.
    apply prog_defmap_dom in SYM0 as [g DEFMAP].
    apply Genv.find_def_symbol in DEFMAP as [b' [SYM' DEF']].
    assert (b = b') by congruence. subst b'. congruence.
Qed.

Lemma find_symbol_right id cp
  (SYM: Genv.find_symbol ge1 id <> None)
  (COMP : Genv.find_comp_of_ident ge1 id = cp)
  (RIGHT: s cp = Right):
  Genv.find_symbol ge2 id <> None.
Proof.
  assert (FS: Genv.find_symbol ge2 id = Genv.find_symbol ge1 id).
  { exact (proj1 (Genv.senv_match match_W1_W2) id). }
  congruence.
Qed.

Lemma init_mem_invert_symbol (pr: program) m b
  (MEM: Genv.init_mem pr = Some m)
  (NR: list_norepet (prog_defs_names pr))
  (VALID: Mem.valid_block m b):
  Genv.invert_symbol (globalenv pr) b <> None.
Proof.
  edestruct Genv.find_def_init_mem as (g & Hg & _); [exact MEM | exact VALID |].
  edestruct Genv.find_def_find_symbol_inversion as [id SYM]; [exact Hg | exact NR |].
  apply Genv.find_invert_symbol in SYM.
  change (Genv.invert_symbol (Genv.globalenv pr) b <> None).
  congruence.
Qed.

Lemma same_domain_right_init_meminj m1
      (MEM: Genv.init_mem W1 = Some m1):
  same_domain_right s init_meminj ge1 m1.
Proof.
  pose proof (init_mem_same_blocks W1 m1 MEM) as SB.
  intros b. split.
  - (* init_meminj b <> None -> Right \/ exists fd, find_def = Some (Gfun fd) *)
    unfold init_meminj, init_meminj_block. intros INJ.
    destruct (Genv.invert_symbol ge1 b) as [id|] eqn:SYM1; [| congruence].
    destruct (Genv.find_def ge1 b) as [[fd | v]|] eqn:DEF.
    + (* Gfun fd *) right. exists fd. reflexivity.
    + (* Gvar v: only mapped if Right-side *)
      destruct (s (comp_of v)) eqn:SIDE; [congruence|].
      left. simpl. rewrite (same_blocks_comp _ _ SB _ _ DEF). exact SIDE.
    + congruence.
  - (* backward: Right \/ exists fd -> init_meminj b <> None *)
    intros [BRIGHT | [fd FD]].
    + (* s (block_compartment m1 b) = Right *)
      destruct (Pos.ltb b (Mem.nextblock m1)) eqn:VB.
      * assert (VALID: Mem.valid_block m1 b).
        { unfold Mem.valid_block, Plt. now apply Pos.ltb_lt. }
        edestruct (Genv.find_def_init_mem W1) as [gd [DEF COMP]]; [exact MEM | exact VALID |].
        exploit Genv.find_def_find_symbol_inversion; [exact DEF | exact W1_norepet |].
        intros [id SYM].
        pose proof (Genv.find_invert_symbol _ _ SYM) as INV.
        assert (INV': Genv.invert_symbol ge1 b = Some id).
        { unfold ge1, globalenv; simpl. exact INV. }
        assert (DEF': Genv.find_def ge1 b = Some gd) by exact DEF.
        unfold init_meminj, init_meminj_block. rewrite INV'. rewrite DEF'.
        assert (Genv.find_symbol ge2 id = Some b) as SYM2.
        { unfold ge2, globalenv; simpl.
          rewrite (Genv.find_symbol_match match_W1_W2). exact SYM. }
        destruct gd as [fd | v].
        { rewrite SYM2. congruence. }
        { simpl in BRIGHT.
          rewrite (same_blocks_comp _ _ SB _ _ DEF') in BRIGHT. simpl in BRIGHT.
          rewrite BRIGHT. rewrite SYM2. congruence. }
      * exfalso.
        assert (INVALID: ~ Mem.valid_block m1 b).
        { unfold Mem.valid_block, Plt. apply Pos.ltb_nlt in VB. lia. }
        simpl in BRIGHT.
        rewrite (Mem.block_compartment_valid_block _ _ INVALID) in BRIGHT.
        congruence.
    + (* exists fd, find_def ge1 b = Some (Gfun fd) *)
      exploit Genv.find_def_find_symbol_inversion.
      { unfold ge1, globalenv in FD; simpl in FD. exact FD. }
      { exact W1_norepet. }
      intros [id SYM].
      pose proof (Genv.find_invert_symbol _ _ SYM) as INV.
      assert (INV': Genv.invert_symbol ge1 b = Some id).
      { unfold ge1, globalenv; simpl. exact INV. }
      assert (FD': Genv.find_def ge1 b = Some (Gfun fd)) by exact FD.
      unfold init_meminj, init_meminj_block. rewrite INV'. rewrite FD'.
      assert (Genv.find_symbol ge2 id = Some b) as SYM2.
      { unfold ge2, globalenv; simpl.
        rewrite (Genv.find_symbol_match match_W1_W2). exact SYM. }
      rewrite SYM2. congruence.
Qed.

Lemma delta_zero_init_meminj:
  Mem.delta_zero init_meminj.
Proof.
  unfold init_meminj. intros loc loc' delta INJ.
  destruct init_meminj_block; [| discriminate].
  injection INJ as <- <-.
  reflexivity.
Qed.

Lemma init_meminj_has_symbol b:
  init_meminj b <> None -> exists id, Genv.invert_symbol ge1 b = Some id.
Proof.
  unfold init_meminj, init_meminj_block.
  destruct (Genv.invert_symbol ge1 b) as [id|] eqn:INV.
  - intros _. exists id. reflexivity.
  - intros H. exfalso. apply H. reflexivity.
Qed.

(* These characterizations need to be a bit more general to be
   independent of init_meminj in particular *)
Lemma init_mem_characterization_rel sp (pr1 pr2: program) id gd m1 m2 b1 b2
    (MATCH: match_prog sp tt pr1 pr2)
    (PROGDEFS1: In (id, gd) (prog_defs pr1))
    (PROGDEFS2: In (id, gd) (prog_defs pr2))
    (MEM1: Genv.init_mem pr1 = Some m1)
    (MEM2: Genv.init_mem pr2 = Some m2)
    (SYM1: Genv.find_symbol (globalenv pr1) id = Some b1)
    (SYM2: Genv.find_symbol (globalenv pr2) id = Some b2)
    (DEF1: Genv.find_def (globalenv pr1) b1 = Some gd)
    (DEF2: Genv.find_def (globalenv pr2) b2 = Some gd):
  (forall ofs k p, Mem.perm m1 b1 ofs k p <-> Mem.perm m2 b2 ofs k p) /\
  (forall cp, Mem.can_access_block m1 b1 cp <-> Mem.can_access_block m2 b2 cp).
Proof.
  pose proof (init_mem_same_blocks pr1 m1 MEM1) as SB1.
  pose proof (init_mem_same_blocks pr2 m2 MEM2) as SB2.
  split.
  - (* permissions *)
    destruct gd as [fd | gv].
    + (* Gfun *)
      intros ofs k p0. split; intros PERM; exfalso.
      * assert (FP: Genv.find_funct_ptr (globalenv pr1) b1 = Some fd).
        { unfold Genv.find_funct_ptr. rewrite DEF1. reflexivity. }
        exact (@Genv.init_mem_characterization_2 _ _ _ pr1 b1 fd m1 FP MEM1 ofs k p0 PERM).
      * assert (FP: Genv.find_funct_ptr (globalenv pr2) b2 = Some fd).
        { unfold Genv.find_funct_ptr. rewrite DEF2. reflexivity. }
        exact (@Genv.init_mem_characterization_2 _ _ _ pr2 b2 fd m2 FP MEM2 ofs k p0 PERM).
    + (* Gvar *)
      assert (VI1: Genv.find_var_info (globalenv pr1) b1 = Some gv).
      { unfold Genv.find_var_info. rewrite DEF1. reflexivity. }
      assert (VI2: Genv.find_var_info (globalenv pr2) b2 = Some gv).
      { unfold Genv.find_var_info. rewrite DEF2. reflexivity. }
      destruct (@Genv.init_mem_characterization _ _ _ pr1 b1 gv m1 VI1 MEM1) as [RP1 [BND1 _]].
      destruct (@Genv.init_mem_characterization _ _ _ pr2 b2 gv m2 VI2 MEM2) as [RP2 [BND2 _]].
      intros ofs k p0. split; intros PERM.
      * destruct (BND1 _ _ _ PERM) as [RANGE ORD].
        eapply Mem.perm_cur.
        eapply Mem.perm_implies; [exact (RP2 ofs RANGE) | exact ORD].
      * destruct (BND2 _ _ _ PERM) as [RANGE ORD].
        eapply Mem.perm_cur.
        eapply Mem.perm_implies; [exact (RP1 ofs RANGE) | exact ORD].
  - (* can_access_block *)
    intros cp0. unfold Mem.can_access_block. simpl.
    rewrite (same_blocks_comp _ _ SB1 _ _ DEF1).
    rewrite (same_blocks_comp _ _ SB2 _ _ DEF2).
    tauto.
Qed.

(* Second version of init_mem_characterization_rel with explicit SYM/DEF *)
Lemma init_mem_characterization_rel_2 sp (pr1 pr2: program) id gd m1 m2 b1 b2
      (MATCH: match_prog sp tt pr1 pr2)
      (MEM1: Genv.init_mem pr1 = Some m1)
      (MEM2: Genv.init_mem pr2 = Some m2)
      (SYM1: Genv.find_symbol (globalenv pr1) id = Some b1)
      (SYM2: Genv.find_symbol (globalenv pr2) id = Some b2)
      (DEF1: Genv.find_def (globalenv pr1) b1 = Some gd)
      (DEF2: Genv.find_def (globalenv pr2) b2 = Some gd):
  (forall ofs k p, Mem.perm m1 b1 ofs k p <-> Mem.perm m2 b2 ofs k p) /\
  (forall cp, Mem.can_access_block m1 b1 cp <-> Mem.can_access_block m2 b2 cp).
Proof.
  assert (PD1: In (id, gd) (AST.prog_defs (program_of_program pr1))).
  { apply in_prog_defmap.
    apply Genv.find_def_symbol. exists b1. exact (conj SYM1 DEF1). }
  assert (PD2: In (id, gd) (AST.prog_defs (program_of_program pr2))).
  { apply in_prog_defmap.
    apply Genv.find_def_symbol. exists b2. exact (conj SYM2 DEF2). }
  eapply init_mem_characterization_rel; eassumption.
Qed.

Definition globdef_blocks p1 p2 '(id, gd) b1 b2 :=
  Genv.find_symbol (globalenv p1) id = Some b1 /\
  Genv.find_symbol (globalenv p2) id = Some b2 /\
  Genv.find_def (globalenv p1) b1 = Some gd /\
  Genv.find_def (globalenv p2) b2 = Some gd.

Lemma globdef_right id gd1 gd2 b1 b2 cp
      (COMP : Genv.find_comp_of_ident (Genv.globalenv W1) id = cp)
      (RIGHT : s cp = Right)
      (SYM1 : Genv.find_symbol ge1 id = Some b1)
      (SYM2 : Genv.find_symbol ge2 id = Some b2)
      (DEF1 : Genv.find_def (Genv.globalenv W1) b1 = Some gd1)
      (DEF2 : Genv.find_def (Genv.globalenv W2) b2 = Some gd2):
  gd1 = gd2.
Proof.
  assert (FS: Genv.find_symbol ge2 id = Genv.find_symbol ge1 id).
  { exact (proj1 (Genv.senv_match match_W1_W2) id). }
  assert (b1 = b2).
  { change (Genv.find_symbol (Genv.globalenv W1) id) with
      (Senv.find_symbol ge1 id) in SYM1.
    change (Genv.find_symbol (Genv.globalenv W2) id) with
      (Senv.find_symbol ge2 id) in SYM2.
    congruence. }
  subst b2.
  edestruct (Genv.find_def_match match_W1_W2) as [tg [TG MG]]; [exact DEF1 |].
  assert (H_eq: Some tg = Some gd2).
  { rewrite <- TG. exact DEF2. }
  inv H_eq.
  inv MG.
  - (* Gfun case *)
    f_equal. inv H0.
    + (* match_function_left *)
      exfalso. simpl in H1.
      unfold Genv.find_comp_of_ident in RIGHT.
      assert (SYM1' : Genv.find_symbol (Genv.globalenv W1) id = Some b1) by exact SYM1.
      rewrite SYM1' in RIGHT.
      unfold Genv.find_comp_of_block in RIGHT.
      rewrite DEF1 in RIGHT.
      simpl in RIGHT. congruence.
    + (* match_external_left *) reflexivity.
    + (* match_right *) reflexivity.
  - (* Gvar case *)
    f_equal. inv H.
    unfold match_varinfo in H0. subst. reflexivity.
Qed.

(* Helper: extract individual memval from getN relation *)
Lemma getN_forall2:
  forall (P: memval -> memval -> Prop) c1 c2 n p,
    list_forall2 P (Mem.getN n p c1) (Mem.getN n p c2) ->
    forall i, p <= i -> i < p + Z.of_nat n ->
    P (ZMap.get i c1) (ZMap.get i c2).
Proof.
  induction n; simpl Mem.getN; intros.
  - simpl in H1. lia.
  - inv H. rewrite Nat2Z.inj_succ in H1. destruct (zeq i p).
    + congruence.
    + apply IHn with (p + 1); auto; lia.
Qed.

Lemma getN_eq:
  forall c1 c2 n p,
    Mem.getN n p c1 = Mem.getN n p c2 ->
    forall i, p <= i -> i < p + Z.of_nat n ->
    ZMap.get i c1 = ZMap.get i c2.
Proof.
  induction n; simpl; intros.
  - lia.
  - injection H as EQ_HD EQ_TL.
    destruct (zeq i p).
    + subst. exact EQ_HD.
    + apply IHn with (p + 1); auto; lia.
Qed.

(* bytes_of_init_data_list produces identical results when symbols match *)
Lemma bytes_of_init_data_list_match:
  forall il,
    Genv.bytes_of_init_data_list (Genv.globalenv W1) il =
    Genv.bytes_of_init_data_list (Genv.globalenv W2) il.
Proof.
  induction il as [|i il]; simpl; [reflexivity|].
  f_equal; [|exact IHil].
  destruct i; try reflexivity.
  unfold Genv.bytes_of_init_data.
  pose proof (Genv.find_symbol_match match_W1_W2 i) as FS.
  replace (Genv.find_symbol (Genv.globalenv W2) i)
    with (Genv.find_symbol (Genv.globalenv W1) i) by exact (eq_sym FS).
  reflexivity.
Qed.

(* No Fragment values in inj_bytes *)
Lemma in_inj_bytes_no_fragment:
  forall bl mv, In mv (inj_bytes bl) -> forall v q n, mv <> Fragment v q n.
Proof.
  induction bl; simpl; intros.
  - contradiction.
  - destruct H as [<- | H]; [discriminate | eapply IHbl; eauto].
Qed.

(* Fragment (Vptr b _) in bytes_of_init_data_list comes from Init_addrof *)
Lemma bytes_of_init_data_list_ptr_fragment {F V} (ge0: Genv.t F V):
  forall il mv,
    In mv (Genv.bytes_of_init_data_list ge0 il) ->
    forall b ofs q n, mv = Fragment (Vptr b ofs) q n ->
    exists id ofs', In (Init_addrof id ofs') il /\
                    Genv.find_symbol ge0 id = Some b.
Proof.
  induction il as [|i il IH]; simpl; intros mv HIN b ofs q n EQ.
  - contradiction.
  - apply in_app_or in HIN. destruct HIN as [HIN | HIN].
    + destruct i; simpl in HIN;
        try (exfalso; eapply in_inj_bytes_no_fragment with (v := Vptr b ofs) (q := q) (n := n); eauto; subst; eauto; fail).
      * (* Init_space *)
        exfalso. apply repeat_spec in HIN. subst. discriminate.
      * (* Init_addrof *)
        rename i into addr_id. rename i0 into addr_ofs.
        unfold Genv.bytes_of_init_data in HIN.
        destruct (Genv.find_symbol ge0 addr_id) as [b0|] eqn:FS.
        -- exists addr_id, addr_ofs. split; [left; reflexivity|].
           unfold inj_value in HIN.
           assert (b = b0).
           { subst mv. revert HIN.
             generalize (size_quantity_nat (if Archi.ptr64 then Q64 else Q32)).
             induction n0; simpl; intros.
             - contradiction.
             - destruct HIN as [E | HIN].
               + injection E as -> _ _. reflexivity.
               + eapply IHn0. exact HIN. }
           subst. exact FS.
        -- exfalso. apply repeat_spec in HIN. subst. discriminate.
    + destruct (IH _ HIN _ _ _ _ EQ) as (id' & ofs'' & HIN' & FS').
      exists id', ofs''. split; [right; exact HIN' | exact FS'].
Qed.

(* getN element at index is nth *)
Lemma getN_nth:
  forall n p c i,
    0 <= i -> i < Z.of_nat n ->
    ZMap.get (p + i) c = nth (Z.to_nat i) (Mem.getN n p c) Undef.
Proof.
  induction n; simpl; intros.
  - lia.
  - destruct (zeq i 0).
    + subst. rewrite Z.add_0_r. reflexivity.
    + replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
      simpl. rewrite <- IHn; [f_equal; lia | lia | lia].
Qed.

(* nth in a list implies In *)
Lemma In_nth_exists:
  forall {A} (l: list A) (x d: A) (i: nat),
    (i < length l)%nat -> nth i l d = x -> In x l.
Proof.
  intros A l x d i. revert l. induction i; destruct l; simpl; intros.
  - lia.
  - left. exact H0.
  - lia.
  - right. eapply IHi; [lia | exact H0].
Qed.

(* For inject-neutral memvals whose pointer targets are in init_meminj,
   memval_inject holds under init_meminj *)
Lemma memval_inject_neutral_init_meminj:
  forall m1 mv,
    Genv.init_mem W1 = Some m1 ->
    memval_inject (Mem.flat_inj (Mem.nextblock m1)) mv mv ->
    (forall b ofs q n, mv = Fragment (Vptr b ofs) q n -> init_meminj b <> None) ->
    memval_inject init_meminj mv mv.
Proof.
  intros ? ? ? MVINJ PTDOM.
  inv MVINJ; try constructor.
  (* Fragment case: goal is Val.inject init_meminj v1 v1,
     have H2: Val.inject flat_inj v1 v1 *)
  destruct v1;
    first [ constructor (* handles Vundef, Vint, Vlong, Vfloat, Vsingle *)
          | idtac (* Vptr case falls through *) ].
  (* Vptr case *)
  inv H2.
  assert (HDOM: init_meminj b <> None) by (eapply PTDOM; reflexivity).
  destruct (init_meminj b) as [[b' d]|] eqn:MAP; [|congruence].
  (* d = 0 and b' = b from init_meminj structure *)
  assert (d = 0 /\ b' = b).
  { unfold init_meminj in MAP.
    destruct (init_meminj_block b) as [b''|] eqn:BLOCK; [|discriminate].
    injection MAP as <- <-. split; [reflexivity|].
    unfold init_meminj_block in BLOCK.
    destruct (Genv.invert_symbol ge1 b) as [id0|] eqn:INV; [|discriminate].
    apply Genv.invert_find_symbol in INV.
    pose proof (Genv.find_symbol_match match_W1_W2 id0) as FS.
    assert (SYM2: Genv.find_symbol ge2 id0 = Some b).
    { transitivity (Genv.find_symbol (Genv.globalenv W2) id0); [reflexivity|].
      transitivity (Genv.find_symbol (Genv.globalenv W1) id0); [exact FS|exact INV]. }
    destruct (Genv.find_def ge1 b) as [g|]; [|discriminate].
    destruct g as [fd|v0].
    - rewrite SYM2 in BLOCK. injection BLOCK as <-. reflexivity.
    - destruct (s (comp_of v0)); [discriminate|].
      rewrite SYM2 in BLOCK. injection BLOCK as <-. reflexivity. }
  destruct H0 as [-> ->].
  eapply Val.inject_ptr; [exact MAP | rewrite Ptrofs.add_zero; reflexivity].
Qed.

(* Genv.initmem_inject *)
Lemma inject_init_meminj m1 m2
      (MEM1: Genv.init_mem W1 = Some m1)
      (MEM2: Genv.init_mem W2 = Some m2):
  Mem.inject init_meminj m1 m2.
Proof.
  (* Common tactic for decomposing init_meminj *)
  assert (DECOMP: forall b1 b2 delta,
    init_meminj b1 = Some (b2, delta) ->
    exists id, Genv.find_symbol ge1 id = Some b1 /\
               Genv.find_symbol ge2 id = Some b2 /\
               delta = 0).
  { intros b1 b2 delta INJ.
    unfold init_meminj, init_meminj_block in INJ.
    destruct (Genv.invert_symbol ge1 b1) as [id|] eqn:INV; [| discriminate].
    destruct (Genv.find_def ge1 b1) as [g|] eqn:DEF; [| discriminate].
    destruct g as [fd|v].
    - destruct (Genv.find_symbol ge2 id) as [b'|] eqn:SYM2; [| discriminate].
      injection INJ as -> <-.
      apply Genv.invert_find_symbol in INV.
      exists id. eauto.
    - destruct (s (comp_of v)); [discriminate|].
      destruct (Genv.find_symbol ge2 id) as [b'|] eqn:SYM2; [| discriminate].
      injection INJ as -> <-.
      apply Genv.invert_find_symbol in INV.
      exists id. eauto. }
  (* For any mapped pair, get the global defs *)
  assert (GLOBS: forall id b1 b2,
    Genv.find_symbol ge1 id = Some b1 ->
    Genv.find_symbol ge2 id = Some b2 ->
    exists gd1 gd2,
      Genv.find_def ge1 b1 = Some gd1 /\
      Genv.find_def ge2 b2 = Some gd2 /\
      comp_of gd1 = comp_of gd2 /\
      (gd1 = gd2 \/
       exists f1 f2, gd1 = Gfun (Internal f1) /\ gd2 = Gfun (Internal f2))).
  { intros id b1 b2 SYM1 SYM2.
    destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as [gd1 DEF1].
    destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as [gd2 DEF2].
    exists gd1, gd2. split; [exact DEF1|]. split; [exact DEF2|].
    assert (FS: Genv.find_symbol ge2 id = Genv.find_symbol ge1 id).
    { exact (proj1 (Genv.senv_match match_W1_W2) id). }
    assert (b1 = b2) by congruence. subst b2.
    edestruct (Genv.find_def_match match_W1_W2) as [tg [TG MG]]; [exact DEF1 |].
    assert (tg = gd2) by congruence. subst tg.
    inv MG.
    - (* Gfun *) inv H0.
      + (* match_function_left *)
        split; [reflexivity|]. right. eauto.
      + (* match_external_left *)
        split; [reflexivity|]. left. reflexivity.
      + (* match_right *)
        split; [reflexivity|]. left. reflexivity.
    - (* Gvar *) inv H. unfold match_varinfo in H0. subst.
      split; [reflexivity|]. left. reflexivity. }
  (* Function blocks have no permissions in initial memory *)
  assert (FUN_NO_PERM1: forall b fd,
    Genv.find_def ge1 b = Some (Gfun fd) ->
    forall ofs k p, Mem.perm m1 b ofs k p -> False).
  { intros b0 fd0 DEF0.
    eapply @Genv.init_mem_characterization_2; eauto.
    unfold Genv.find_funct_ptr.
    replace (Genv.find_def (Genv.globalenv W1) b0) with (Genv.find_def ge1 b0) by reflexivity.
    rewrite DEF0. reflexivity. }
  assert (FUN_NO_PERM2: forall b fd,
    Genv.find_def ge2 b = Some (Gfun fd) ->
    forall ofs k p, Mem.perm m2 b ofs k p -> False).
  { intros b0 fd0 DEF0.
    eapply @Genv.init_mem_characterization_2; eauto.
    unfold Genv.find_funct_ptr.
    replace (Genv.find_def (Genv.globalenv W2) b0) with (Genv.find_def ge2 b0) by reflexivity.
    rewrite DEF0. reflexivity. }
  (* Permissions iff for identical defs *)
  assert (PERMS: forall id b1 b2 gd,
    Genv.find_symbol ge1 id = Some b1 ->
    Genv.find_symbol ge2 id = Some b2 ->
    Genv.find_def ge1 b1 = Some gd ->
    Genv.find_def ge2 b2 = Some gd ->
    forall ofs k p, Mem.perm m1 b1 ofs k p <-> Mem.perm m2 b2 ofs k p).
  { intros id b1 b2 gd SYM1 SYM2 DEF1 DEF2.
    exact (proj1 (init_mem_characterization_rel_2 _ _ _ _ _ _ _ _ _
                    match_W1_W2 MEM1 MEM2 SYM1 SYM2 DEF1 DEF2)). }
  constructor.
  - (* mem_inj *)
    constructor.
    + (* mi_perm *)
      intros b1 b2 delta ofs k p INJ PERM.
      destruct (DECOMP _ _ _ INJ) as (id & SYM1 & SYM2 & ->).
      destruct (GLOBS _ _ _ SYM1 SYM2) as (gd1 & gd2 & DEF1 & DEF2 & COMP_EQ & [EQ | [f1 [f2 [E1 E2]]]]).
      * subst gd2. rewrite Z.add_0_r.
        eapply (PERMS _ _ _ gd1 SYM1 SYM2 DEF1 DEF2). exact PERM.
      * (* Left Internal function — no perms *)
        subst gd1. exfalso.
        eapply FUN_NO_PERM1; [exact DEF1 | exact PERM].
    + (* mi_access *)
      intros b1 b2 delta ofs p k INJ PERM.
      destruct (DECOMP _ _ _ INJ) as (id & SYM1 & SYM2 & ->).
      destruct (GLOBS _ _ _ SYM1 SYM2) as (gd1 & gd2 & DEF1 & DEF2 & COMP_EQ & _).
      pose proof (init_mem_same_blocks W1 m1 MEM1) as SB1.
      pose proof (init_mem_same_blocks W2 m2 MEM2) as SB2.
      rewrite (same_blocks_comp _ _ SB1 _ _ DEF1).
      rewrite (same_blocks_comp _ _ SB2 _ _ DEF2).
      rewrite COMP_EQ. reflexivity.
    + (* mi_align *)
      intros b1 b2 delta chunk ofs p INJ _.
      destruct (DECOMP _ _ _ INJ) as (_ & _ & _ & ->).
      apply Z.divide_0_r.
    + (* mi_memval *)
      intros b1 ofs b2 delta INJ PERM.
      destruct (DECOMP _ _ _ INJ) as (id & SYM1 & SYM2 & ->).
      rewrite Z.add_0_r.
      destruct (GLOBS _ _ _ SYM1 SYM2) as (gd1 & gd2 & DEF1 & DEF2 & _ & [EQ | [f1 [f2 [E1 E2]]]]).
      * (* Identical defs — memval_inject from inject-neutral + content equality *)
        subst gd2.
        (* m1 is inject-neutral, so contents self-inject under flat_inj *)
        (* gd1 is either a variable or a function. Functions have no perms. *)
        destruct gd1 as [[fd|ef]|gv].
        -- (* Internal function — no perms *)
           exfalso. eapply FUN_NO_PERM1; [exact DEF1 | exact PERM].
        -- (* External function — no perms *)
           exfalso. eapply FUN_NO_PERM1; [exact DEF1 | exact PERM].
        -- (* Variable — gv is a Gvar *)
           (* Get loadbytes characterization for both memories *)
           assert (FVI1: Genv.find_var_info ge1 b1 = Some gv).
           { unfold Genv.find_var_info. rewrite DEF1. reflexivity. }
           assert (FVI2: Genv.find_var_info ge2 b2 = Some gv).
           { unfold Genv.find_var_info. rewrite DEF2. reflexivity. }
           assert (FVI1': Genv.find_var_info (Genv.globalenv W1) b1 = Some gv) by exact FVI1.
           assert (FVI2': Genv.find_var_info (Genv.globalenv W2) b2 = Some gv) by exact FVI2.
           destruct (@Genv.init_mem_characterization _ _ _ W1 b1 gv m1 FVI1' MEM1) as [RP1 [BOUNDS1 [_ LB1]]].
           destruct (@Genv.init_mem_characterization _ _ _ W2 b2 gv m2 FVI2' MEM2) as [RP2 [BOUNDS2 [_ LB2]]].
           destruct (gvar_volatile gv) eqn:VOL.
           ++ (* volatile — no readable perm *)
              destruct (BOUNDS1 _ _ _ PERM) as [RANGE1 PORD1].
              unfold Genv.perm_globvar in PORD1. rewrite VOL in PORD1.
              inv PORD1.
           ++ (* non-volatile — use loadbytes to show contents equal *)
              specialize (LB1 eq_refl). specialize (LB2 eq_refl).
              assert (BYTES_EQ: Genv.bytes_of_init_data_list (Genv.globalenv W1) (gvar_init gv) =
                                Genv.bytes_of_init_data_list (Genv.globalenv W2) (gvar_init gv)).
              { apply bytes_of_init_data_list_match. }
              destruct (BOUNDS1 _ _ _ PERM) as [OFS_RANGE _].
              (* Unfold loadbytes to access getN *)
              Transparent Mem.loadbytes.
              unfold Mem.loadbytes in LB1, LB2.
              destruct (Mem.range_perm_dec m1 b1 0 _ Cur Readable && _); [|discriminate].
              destruct (Mem.range_perm_dec m2 b2 0 _ Cur Readable && _); [|discriminate].
              injection LB1 as LB1. injection LB2 as LB2.
              Opaque Mem.loadbytes.
              (* getN results are equal *)
              rewrite <- BYTES_EQ in LB2. rewrite <- LB1 in LB2.
              assert (GET_EQ: ZMap.get ofs (Mem.mem_contents m1) !! b1 =
                              ZMap.get ofs (Mem.mem_contents m2) !! b2).
              { eapply getN_eq; eauto; (try rewrite Z2Nat.id); lia. }
              rewrite <- GET_EQ.
              (* Self-injection under init_meminj *)
              assert (INJ_N: Mem.inject (Mem.flat_inj (Mem.nextblock m1)) m1 m1).
              { eapply Genv.initmem_inject; eauto. }
              assert (FLAT_B1: Mem.flat_inj (Mem.nextblock m1) b1 = Some (b1, 0)).
              { unfold Mem.flat_inj.
                destruct (plt b1 (Mem.nextblock m1)); [reflexivity|].
                exfalso. apply n. eapply Genv.find_symbol_not_fresh; eauto. }
              assert (MV_SELF: memval_inject (Mem.flat_inj (Mem.nextblock m1))
                (ZMap.get ofs (Mem.mem_contents m1) !! b1)
                (ZMap.get ofs (Mem.mem_contents m1) !! b1)).
              { pose proof (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ INJ_N) _ _ _ _ FLAT_B1 PERM) as MV.
                rewrite Z.add_0_r in MV. exact MV. }
              (* Lift from flat_inj to init_meminj *)
              eapply memval_inject_neutral_init_meminj; eauto.
              (* Pointer targets in this memval are in init_meminj domain.
                 b1 is a Right-side Gvar (since init_meminj mapped it and it's Gvar).
                 Pointer targets come from Init_addrof in gvar_init gv.
                 By init_addrof_right_closed, targets are Gfun or Right-side Gvar,
                 so they are in init_meminj. *)
              intros b' ofs' q' n' FRAG.
              (* b' is valid (from flat_inj self-injection) *)
              assert (MV_FRAG: memval_inject (Mem.flat_inj (Mem.nextblock m1))
                (Fragment (Vptr b' ofs') q' n') (Fragment (Vptr b' ofs') q' n')).
              { rewrite <- FRAG. exact MV_SELF. }
              (* Extract Plt b' from the flat_inj *)
              assert (PLT_B': Plt b' (Mem.nextblock m1)).
              { inversion MV_FRAG; subst.
                match goal with H: Val.inject _ _ _ |- _ => inversion H; subst end.
                match goal with H: Mem.flat_inj _ _ = Some _ |- _ =>
                  unfold Mem.flat_inj in H;
                  destruct (plt b' (Mem.nextblock m1)); [assumption|discriminate]
                end. }
              (* b' is a valid global block *)
              assert (VALID': Mem.valid_block m1 b') by (red; auto).
              exploit Genv.find_def_init_mem; [exact MEM1 | exact VALID' |].
              intros [g' [DEF' _]].
              exploit Genv.find_def_find_symbol_inversion; [exact DEF' | exact W1_norepet |].
              intros [id' SYM'].
              unfold init_meminj, init_meminj_block.
              apply Genv.find_invert_symbol in SYM' as INV'.
              assert (INV'': Genv.invert_symbol ge1 b' = Some id') by exact INV'.
              rewrite INV''.
              assert (DEF'': Genv.find_def ge1 b' = Some g') by exact DEF'.
              rewrite DEF''.
              pose proof (Genv.find_symbol_match match_W1_W2 id') as FS'.
              assert (SYM2': Genv.find_symbol ge2 id' = Some b').
              { transitivity (Genv.find_symbol (Genv.globalenv W2) id'); [reflexivity|].
                transitivity (Genv.find_symbol (Genv.globalenv W1) id'); [exact FS'|exact SYM']. }
              destruct g' as [fd'|v'].
              ** (* Gfun: always in init_meminj *)
                 rewrite SYM2'. congruence.
              ** (* Gvar: must be Right-side by init_addrof_right_closed *)
                 (* TODO: need to trace pointer back to Init_addrof in gvar_init gv.
                    For now, we know b1 is mapped → Right-side Gvar.
                    The pointer at (b1, ofs) comes from init data of gv.
                    By init_addrof_right_closed, any Gvar target is Right-side. *)
                 (* Need: s (comp_of gv) = Right (b1 is Right-side Gvar) *)
                 assert (RIGHT_GV: s (comp_of gv) = Right).
                 { unfold init_meminj, init_meminj_block in INJ.
                   destruct (Genv.invert_symbol ge1 b1) eqn:INV_B1; [|discriminate].
                   destruct (Genv.find_def ge1 b1) eqn:DEF_B1; [|discriminate].
                   destruct g as [fd0|gv0].
                   - (* Gfun — contradiction: DEF1 says Gvar *)
                     exfalso.
                     assert (Gfun fd0 = Gvar gv).
                     { assert (Some (Gfun fd0) = Some (Gvar gv)) by congruence. congruence. }
                     discriminate.
                   - (* Gvar gv0 *)
                     assert (gv0 = gv) by congruence.
                     subst gv0.
                     destruct (s (comp_of gv)) eqn:SIDE; [discriminate|reflexivity]. }
                 destruct (s (comp_of v')) eqn:SIDE'.
                 --- (* Left — contradiction with init_addrof_right_closed *)
                     exfalso.
                     (* Fragment (Vptr b' ofs') is at position ofs in bytes_of_init_data_list *)
                     assert (IN_BYTES: In (Fragment (Vptr b' ofs') q' n')
                       (Genv.bytes_of_init_data_list (Genv.globalenv W1) (gvar_init gv))).
                     { rewrite <- LB1.
                       assert (GETEQ: ZMap.get ofs (Mem.mem_contents m1) !! b1 =
                         nth (Z.to_nat ofs) (Mem.getN (Z.to_nat (init_data_list_size (gvar_init gv))) 0 (Mem.mem_contents m1) !! b1) Undef).
                       { rewrite <- getN_nth; [f_equal; lia | lia | rewrite Z2Nat.id; lia]. }
                       rewrite FRAG in GETEQ.
                       eapply In_nth_exists with (d := Undef) (i := Z.to_nat ofs).
                       - rewrite Mem.getN_length. apply Z2Nat.inj_lt; lia.
                       - symmetry. exact GETEQ. }
                     (* Trace fragment back to Init_addrof *)
                     destruct (bytes_of_init_data_list_ptr_fragment (Genv.globalenv W1)
                       (gvar_init gv) _ IN_BYTES b' ofs' q' n' eq_refl) as (iid & iofs & HIN_INIT & FS_B').
                     (* Apply init_addrof_right_closed *)
                     assert (FS_EQ: Genv.find_symbol ge1 iid = Some b').
                     { exact FS_B'. }
                     assert (RIGHT_V': s (comp_of v') = Right).
                     { eapply (init_addrof_right_closed b1 gv iid iofs b' v');
                       eauto. }
                     congruence.
                 --- rewrite SYM2'. congruence.
      * (* Left Internal function — no perms *)
        subst gd1. exfalso.
        eapply FUN_NO_PERM1; [exact DEF1 | exact PERM].
  - (* mi_freeblocks *)
    intros b NVALID. unfold init_meminj, init_meminj_block.
    destruct (Genv.invert_symbol ge1 b) as [id|] eqn:INV; [| reflexivity].
    apply Genv.invert_find_symbol in INV.
    exfalso. apply NVALID.
    eapply Genv.find_symbol_not_fresh; eauto.
  - (* mi_mappedblocks *)
    intros b b' delta INJ.
    destruct (DECOMP _ _ _ INJ) as (id & _ & SYM2 & _).
    eapply Genv.find_symbol_not_fresh; eauto.
  - (* mi_no_overlap *)
    intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 NEQ INJ1 INJ2 PERM1 PERM2.
    destruct (DECOMP _ _ _ INJ1) as (id1 & SYM1_1 & SYM2_1 & ->).
    destruct (DECOMP _ _ _ INJ2) as (id2 & SYM1_2 & SYM2_2 & ->).
    left. intros <-. apply NEQ.
    apply Genv.find_invert_symbol in SYM2_1.
    apply Genv.find_invert_symbol in SYM2_2.
    assert (id1 = id2) by congruence. subst.
    congruence.
  - (* mi_representable *)
    intros b b' delta ofs INJ _.
    destruct (DECOMP _ _ _ INJ) as (_ & _ & _ & ->).
    split; [lia |]. rewrite Z.add_0_r. apply Ptrofs.unsigned_range_2.
  - (* mi_perm_inv *)
    intros b1 ofs b2 delta k p INJ PERM.
    destruct (DECOMP _ _ _ INJ) as (id & SYM1 & SYM2 & ->).
    destruct (GLOBS _ _ _ SYM1 SYM2) as (gd1 & gd2 & DEF1 & DEF2 & _ & [EQ | [f1 [f2 [_ E2]]]]).
    * subst gd2. rewrite Z.add_0_r in PERM.
      left. eapply (PERMS _ _ _ gd1 SYM1 SYM2 DEF1 DEF2). exact PERM.
    * (* Left Internal function — no perms on b2 either *)
      subst gd2. exfalso.
      eapply FUN_NO_PERM2; [exact DEF2 | rewrite Z.add_0_r in PERM; exact PERM].
Qed.

Lemma symbols_inject_init_meminj cp:
  s cp = Right ->
  symbols_inject init_meminj ge1 ge2 cp.
Proof.
  intros CP_RIGHT.
  split; [|split; [|split; [|split]]].
  - (* public symbol preservation *)
    intros id _.
    pose proof (Genv.senv_match match_W1_W2) as [_ [SM _]].
    exact (SM id).
  - (* mapped blocks: delta = 0 and find_symbol ge2 *)
    intros id b1 b2 delta INJ SYM1.
    unfold init_meminj, init_meminj_block in INJ.
    destruct (Genv.invert_symbol ge1 b1) as [id'|] eqn:INV; [| discriminate].
    destruct (Genv.find_def ge1 b1) as [g|] eqn:DEF; [| discriminate].
    destruct g as [fd|v].
    + destruct (Genv.find_symbol ge2 id') as [b'|] eqn:SYM2; [| discriminate].
      injection INJ as <- <-.
      assert (SYM1': Genv.find_symbol ge1 id = Some b1) by exact SYM1.
      apply Genv.find_invert_symbol in SYM1'.
      assert (id = id') by congruence. subst id'.
      split; [reflexivity|]. exact SYM2.
    + destruct (s (comp_of v)); [discriminate|].
      destruct (Genv.find_symbol ge2 id') as [b'|] eqn:SYM2; [| discriminate].
      injection INJ as <- <-.
      assert (SYM1': Genv.find_symbol ge1 id = Some b1) by exact SYM1.
      apply Genv.find_invert_symbol in SYM1'.
      assert (id = id') by congruence. subst id'.
      split; [reflexivity|]. exact SYM2.
  - (* public symbols with find_comp ⊆ cp are mapped *)
    intros id b1 PUB SYM1 COMP.
    assert (INV: Genv.invert_symbol ge1 b1 = Some id).
    { apply Genv.find_invert_symbol. exact SYM1. }
    assert (SYM2: Genv.find_symbol ge2 id = Some b1).
    { rewrite (Genv.find_symbol_match match_W1_W2). exact SYM1. }
    exists b1. split; [|exact SYM2].
    unfold init_meminj, init_meminj_block.
    rewrite INV.
    (* b1 has a def since it comes from find_symbol *)
    destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as [gd DEF1c].
    assert (DEF1: Genv.find_def ge1 b1 = Some gd) by exact DEF1c.
    rewrite DEF1.
    destruct gd as [fd|v].
    + rewrite SYM2. reflexivity.
    + destruct (s (comp_of v)) eqn:SIDE; [|rewrite SYM2; reflexivity].
      (* Left-side Gvar — contradiction: COMP says flowsto (comp_of v) cp,
         but comp_of v is Left-side and cp is Right-side *)
      exfalso.
      assert (FCOMP: Senv.find_comp ge1 id = comp_of v).
      { assert (SYM1': Genv.find_symbol ge1 id = Some b1) by exact SYM1.
        assert (H0 := policy_comp_def_W1 _ _ _ SYM1' DEF1). simpl in H0. exact H0. }
      rewrite FCOMP in COMP.
      assert (comp_of v = cp) by
        (apply flowsto_no_bottom_no_top; [exact COMP | eapply no_bottom_var_W1; exact DEF1 |
         intro EQ; rewrite EQ in CP_RIGHT; rewrite s_top_left in CP_RIGHT; discriminate]).
      rewrite H in SIDE. rewrite SIDE in CP_RIGHT. discriminate.
  - (* volatility preservation *)
    intros b1 b2 delta INJ.
    unfold init_meminj, init_meminj_block in INJ.
    destruct (Genv.invert_symbol ge1 b1) as [id|] eqn:INV; [| discriminate].
    destruct (Genv.find_def ge1 b1) as [g|] eqn:DEF; [| discriminate].
    destruct g as [fd|v0];
      [ destruct (Genv.find_symbol ge2 id) as [b'|] eqn:FSYM; [| discriminate];
        injection INJ as <- <-
      | destruct (s (comp_of v0)); [discriminate|];
        destruct (Genv.find_symbol ge2 id) as [b'|] eqn:FSYM; [| discriminate];
        injection INJ as <- <- ];
    apply Genv.invert_find_symbol in INV;
    assert (b' = b1) by
      (assert (Some b' = Some b1) by
        (rewrite <- FSYM; rewrite (Genv.find_symbol_match match_W1_W2);
         exact INV);
       congruence);
    subst b';
    pose proof (Genv.senv_match match_W1_W2) as [_ [_ [VOL' _]]];
    change (Senv.block_is_volatile ge1 b1) with
      (Senv.block_is_volatile (Genv.globalenv W1) b1);
    change (Senv.block_is_volatile ge2 b1) with
      (Senv.block_is_volatile (Genv.globalenv W2) b1);
    exact (VOL' b1).
  - (* comp preservation *)
    intros id.
    pose proof (Genv.senv_match match_W1_W2) as [_ [_ [_ COMP]]].
    change (Senv.find_comp ge1 id) with
      (Senv.find_comp (Genv.to_senv (Genv.globalenv W1)) id).
    change (Senv.find_comp ge2 id) with
      (Senv.find_comp (Genv.to_senv (Genv.globalenv W2)) id).
    exact (eq_sym (COMP id)).
Qed.

Lemma initial_mem_injection m1 m2
      (MEM1: Genv.init_mem W1 = Some m1)
      (MEM2: Genv.init_mem W2 = Some m2):
  right_mem_injection s init_meminj ge1 ge2 m1 m2.
Proof.
  unfold init_meminj.
  constructor.
  - apply same_domain_right_init_meminj; assumption.
  - apply inject_init_meminj; assumption.
  - apply delta_zero_init_meminj.
  - apply init_meminj_injective.
  - intros cp0 CP0R. apply symbols_inject_init_meminj. exact CP0R.
  - (* j_preserves_symbols *)
    intros id b1 b2 delta JB SYM1.
    unfold init_meminj, init_meminj_block in JB.
    destruct (Genv.invert_symbol ge1 b1) as [id'|] eqn:INV; [| discriminate].
    destruct (Genv.find_def ge1 b1) as [g|] eqn:DEF; [| discriminate].
    destruct g as [fd|v0].
    + destruct (Genv.find_symbol ge2 id') as [b'|] eqn:SYM2; [| discriminate].
      injection JB as <- <-.
      assert (INV': Genv.invert_symbol ge1 b1 = Some id).
      { apply Genv.find_invert_symbol. exact SYM1. }
      assert (id = id') by congruence. subst id'.
      split; [reflexivity | exact SYM2].
    + destruct (s (comp_of v0)); [discriminate|].
      destruct (Genv.find_symbol ge2 id') as [b'|] eqn:SYM2; [| discriminate].
      injection JB as <- <-.
      assert (INV': Genv.invert_symbol ge1 b1 = Some id).
      { apply Genv.find_invert_symbol. exact SYM1. }
      assert (id = id') by congruence. subst id'.
      split; [reflexivity | exact SYM2].
  - apply init_mem_same_blocks; assumption.
  - apply init_mem_same_blocks; assumption.
  - (* right_side_image *)
    intros b1 b2 delta JB.
    unfold init_meminj_block in JB.
    destruct (Genv.invert_symbol ge1 b1) as [id|] eqn:INV; [| discriminate].
    destruct (Genv.find_def ge1 b1) as [g|] eqn:DEF; [| discriminate].
    destruct g as [fd|v0].
    + destruct (Genv.find_symbol ge2 id) as [b2'|] eqn:SYM2; [| discriminate].
      injection JB as <- <-.
      right.
      apply Genv.invert_find_symbol in INV.
      assert (b2' = b1).
      { assert (INV': Genv.find_symbol ge1 id = Some b1) by exact INV.
        assert (SYM2': Genv.find_symbol ge2 id = Some b2') by exact SYM2.
        assert (FS: Genv.find_symbol ge1 id = Genv.find_symbol ge2 id).
        { symmetry. exact (Genv.find_symbol_match match_W1_W2 id). }
        congruence. }
      subst b2'.
      assert (SYM2': Genv.find_symbol (Genv.globalenv W2) id = Some b1).
      { exact SYM2. }
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM2') as [gd DEF2].
      assert (DEF2': Genv.find_def ge2 b1 = Some gd) by exact DEF2.
      rewrite DEF2'. discriminate.
    + destruct (s (comp_of v0)); [discriminate|].
      destruct (Genv.find_symbol ge2 id) as [b2'|] eqn:SYM2; [| discriminate].
      injection JB as <- <-.
      right.
      apply Genv.invert_find_symbol in INV.
      assert (b2' = b1).
      { assert (INV': Genv.find_symbol ge1 id = Some b1) by exact INV.
        assert (SYM2': Genv.find_symbol ge2 id = Some b2') by exact SYM2.
        assert (FS: Genv.find_symbol ge1 id = Genv.find_symbol ge2 id).
        { symmetry. exact (Genv.find_symbol_match match_W1_W2 id). }
        congruence. }
      subst b2'.
      assert (SYM2': Genv.find_symbol (Genv.globalenv W2) id = Some b1).
      { exact SYM2. }
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM2') as [gd DEF2].
      assert (DEF2': Genv.find_def ge2 b1 = Some gd) by exact DEF2.
      rewrite DEF2'. discriminate.
  - (* target_gvar_right *)
    intros b1 b2 delta gv JB FDEF2.
    unfold init_meminj_block in JB.
    destruct (Genv.invert_symbol ge1 b1) as [id|] eqn:INV; [| discriminate].
    destruct (Genv.find_def ge1 b1) as [g|] eqn:DEF; [| discriminate].
    destruct g as [fd|v0].
    + destruct (Genv.find_symbol ge2 id) as [b'|] eqn:SYM2; [| discriminate].
      injection JB as <- <-.
      apply Genv.invert_find_symbol in INV.
      assert (b' = b1).
      { assert (FS: Genv.find_symbol ge1 id = Genv.find_symbol ge2 id).
        { symmetry. exact (Genv.find_symbol_match match_W1_W2 id). }
        congruence. }
      subst b'.
      (* find_def_match_2 at b1: ge1 has Gfun fd, ge2 has Gvar gv — contradiction *)
      pose proof (Genv.find_def_match_2 match_W1_W2 b1) as REL.
      unfold ge1 in DEF. unfold ge2 in FDEF2. simpl in DEF, FDEF2.
      setoid_rewrite DEF in REL. setoid_rewrite FDEF2 in REL. inv REL. inv H1.    + destruct (s (comp_of v0)) eqn:SIDE; [discriminate|].
      destruct (Genv.find_symbol ge2 id) as [b'|] eqn:SYM2; [| discriminate].
      injection JB as <- <-.
      apply Genv.invert_find_symbol in INV.
      assert (b' = b1).
      { assert (FS: Genv.find_symbol ge1 id = Genv.find_symbol ge2 id).
        { symmetry. exact (Genv.find_symbol_match match_W1_W2 id). }
        congruence. }
      subst b'.
      pose proof (Genv.find_def_match_2 match_W1_W2 b1) as REL.
      unfold ge1 in DEF. unfold ge2 in FDEF2. simpl in DEF, FDEF2.
      setoid_rewrite DEF in REL. setoid_rewrite FDEF2 in REL. inv REL.
      inv H1. inv H2. simpl. exact SIDE.
Qed.

Lemma initial_state_injection s1 s2 :
  Smallstep.initial_state (semantics1 W1) s1 ->
  Smallstep.initial_state (semantics1 W2) s2 ->
  right_state_injection s init_meminj ge1 ge2 s1 s2.
Proof.
  intros INI1 INI2.
  inv INI1. inv INI2.
  assert (MAIN_EQ: prog_main W2 = prog_main W1).
  { exact (match_program_gen_main _ _ _ _ _ match_W1_W2). }
  change ge with (Genv.globalenv W1) in *.
  change ge0 with (Genv.globalenv W2) in *.
  clear ge ge0.
  (* b0 = b *)
  assert (b0 = b).
  { assert (FS := proj1 (Genv.senv_match match_W1_W2) (prog_main W1)).
    change (Senv.find_symbol ge2 (prog_main W1) = Senv.find_symbol ge1 (prog_main W1)) in FS.
    change (Genv.find_symbol (Genv.globalenv W1) (prog_main W1)) with
      (Senv.find_symbol ge1 (prog_main W1)) in H0.
    change (Genv.find_symbol (Genv.globalenv W2) (prog_main W2)) with
      (Senv.find_symbol ge2 (prog_main W2)) in H4.
    rewrite MAIN_EQ in H4. congruence. }
  subst b0.
  (* Use find_funct_ptr_match to get match_fundef at the find_funct_ptr level *)
  edestruct (Genv.find_funct_ptr_match match_W1_W2) as (cunit & tf & FP2 & MF & LO);
    [exact H1|].
  (* FP2 : find_funct_ptr (globalenv W2) b = Some tf *)
  (* MF : match_fundef s cunit (Internal f) tf *)
  (* H5 : find_funct_ptr (globalenv W2) b = Some (Internal f0) *)
  assert (tf = Internal f0) as ->.
  { assert (E: Genv.find_funct_ptr (Genv.globalenv W2) b = Some tf) by exact FP2.
    congruence. }
  assert (COMP_EQ: comp_of f = comp_of f0).
  { exact (@has_comp_match_fundef s cunit (Internal f) (Internal f0) MF). }
  destruct (s (comp_of f)) eqn:SIDE.
  - (* Main is Left *)
    apply LeftControl; simpl.
    + exact SIDE.
    + rewrite <- COMP_EQ. exact SIDE.
    + eapply initial_mem_injection; eauto.
    + constructor.
  - (* Main is Right *)
    apply RightControl; simpl.
    + exact SIDE.
    + rewrite <- COMP_EQ. exact SIDE.
    + inv MF.
      * simpl in *. congruence.
      * apply inject_callstates.
        -- eapply initial_mem_injection; eauto.
        -- constructor.
        -- constructor.
Qed.

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
  pose proof (initial_state_injection _ _ Hini1 Hini2) as Hpartialize.
  set (j0 := init_meminj) in *.
  assert (PROPER1: forall b f, Genv.find_def (globalenv W1) b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W1; eauto | eapply no_top_W1; eauto]).
  assert (PROPER2': forall b f, Genv.find_def (globalenv W2) b = Some (Gfun (Internal f)) ->
    comp_of f <> bottom /\ comp_of f <> top)
    by (intros; split; [eapply no_bottom_W2; eauto | eapply no_top_W2; eauto]).
  assert (WF_INI1: state_wf sini1).
  { eapply (initial_state_wf W1). exact PROPER1. exact Hini1. }
  assert (WF_INI2: state_wf sini2).
  { eapply (initial_state_wf W2). exact PROPER2'. exact Hini2. }
  assert (SI1: state_inv ge1 sini1) by (eapply initial_state_inv; exact Hini1).
  assert (SI2: state_inv ge2 sini2) by (eapply initial_state_inv; exact Hini2).
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
      Hpartialize WF_INI1 WF_INI2 SI1 SI2
      HStar1 HStar2 HNostep2 Hfinal1
      as Hparallel.
    destruct (state_split_decidable sfin2) as [Hparallel1 | Hparallel1].
    + exact (blame_last_comp_star _ _ _ _ PROPER2' Hini2 HStar2 Hparallel1).
    + specialize (Hparallel Hparallel1) as Hfinal2.
      specialize (Hnot_final2 n). contradiction.
  - simpl in Hnot_wrong'. contradiction.
  - simpl. destruct tm'.
    + left. exists (Goes_wrong nil). simpl. repeat rewrite E0_right. reflexivity.
    + right.
      pose proof parallel_exec' _ _ _ _ _ _ _ _
        Hpartialize WF_INI1 WF_INI2 SI1 SI2
        HStar1 HStar2 HNostep2
        as Hparallel.
      exact (blame_last_comp_star _ _ _ _ PROPER2' Hini2 HStar2 Hparallel).
Qed.

(* Theorem blame (t m: trace): *)
(*   clight_program_has_initial_trace W2 t -> *)
(*   trace_prefix m t -> *)
(*   m <> t -> *)
(*   program_behaves (semantics1 W1) (Goes_wrong m) -> *)
(*   blame_on_program m. *)
(* Proof. *)

(* The mirror form of the above statement (W1 <-> W2), to avoid
   dealing with symmetry here. *)
Theorem blame (t m: trace):
  clight_program_has_initial_trace W1 t ->
  trace_prefix m t ->
  m <> t ->
  program_behaves (semantics1 W2) (Goes_wrong m) ->
  blame_on_program m.
Proof.
  intros INI PREFIX NEQ WRONG.
  inversion WRONG as [s2 b _ s2_m | CONTRA];
    [| destruct W2_ini as (s2 & INI2); specialize (CONTRA s2); contradiction];
    subst b.
  inversion s2_m as [| | | t' s2' STAR NOSTEP NOTFINAL EQ];
    subst t'.
  destruct PREFIX as (tm & ->).
  destruct tm as [| e tm];
    [rewrite E0_right in NEQ; contradiction |].
  destruct (program_behaves_exists (semantics1 W1)) as (b & W1_b).
  specialize (INI _ W1_b) as (b' & ->).
  inversion W1_b as [s1 b _ s1_m | CONTRA];
    [| destruct W1_ini as (s1 & INI1); specialize (CONTRA s1); contradiction];
    subst b.
  assert (PREFIX: does_prefix (semantics1 W1) (FTbc (m ** e :: tm))). {
    exists (behavior_app (m ** e :: tm) b'). split; [assumption | ].
    exists b'. reflexivity. }
  assert (FINPREF: trace_finpref_prefix m (FTbc (m ** e :: tm))). {
    exists (e :: tm). reflexivity. }
  destruct (blame_program _ _ WRONG PREFIX I FINPREF) as [[b CONTRA] | G];
    [| assumption].
  destruct b; try discriminate.
  injection CONTRA as CONTRA.
  { clear -CONTRA. exfalso.
    induction m.
    - discriminate.
    - injection CONTRA as Hm. exact (IHm Hm). }
Qed.

Print Assumptions blame.

End Simulation.
