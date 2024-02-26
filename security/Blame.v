Require Import String.
Require Import Coqlib Maps Errors Integers.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.
Require Import SimplLocalsproof.
Require Import Unusedglobproof.
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

(* FIXME add definitions *)

Section Equivalence.
  Variable s: split.
  Variable j: meminj.

  (* Definition same_domain_right (m1: mem) := *)
  (*   forall b, j b <> None <-> (s, m1) |= b ∈ Right. *)

  Definition same_domain_right (ge1: genv) (m1: mem) :=
    forall b, j b <> None <-> (s, m1) |= b ∈ Right \/
                              exists fd, Genv.find_def ge1 b = Some (Gfun fd).

  Definition same_domain_left (ge1: genv) :=
    forall b,
      j b <> None <->
      exists cp, Genv.find_comp_of_block ge1 b = Some cp /\
                 s cp = Left.

  (* TODO: Move to memory *)
  Lemma free_block_compartment {m b lo hi cp m' b'} :
    Mem.free m b lo hi cp = Some m' ->
    Mem.block_compartment m b' = Mem.block_compartment m' b'.
  Proof.
    intros FREE.
    destruct (Mem.block_compartment m b') as [cp'|] eqn:BLK.
    { now rewrite (Mem.free_can_access_block_inj_1 _ _ _ _ _ _ FREE
                     _ (Some cp') BLK). }
    destruct (Mem.block_compartment m' b') as [cp'|] eqn:BLK'; trivial.
    now rewrite (Mem.free_can_access_block_inj_2 _ _ _ _ _ _ FREE
                   _ (Some cp') BLK') in BLK.
  Qed.

  Lemma same_domain_right_free m b lo hi cp m' ge
    (FREE : Mem.free m b lo hi cp = Some m')
    (BLOCKS : same_domain_right ge m) :
    same_domain_right ge m'.
  Proof.
    intros b'. specialize (BLOCKS b'). simpl in *.
    now rewrite <- (free_block_compartment FREE).
  Qed.

  Lemma same_domain_right_free_list m bs cp m' ge
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

  Lemma same_domain_right_store chunk m b off v cp m' ge :
    Mem.store chunk m b off v cp = Some m' ->
    same_domain_right ge m ->
    same_domain_right ge m'.
  Proof.
    intros STORE DOM b'. specialize (DOM b'). simpl in *.
    now rewrite (Mem.store_block_compartment _ _ _ _ _ _ _ STORE).
  Qed.

  Lemma same_domain_right_storebytes m b ofs sz ocp m' ge :
    Mem.storebytes m b ofs sz ocp = Some m' ->
    same_domain_right ge m ->
    same_domain_right ge m'.
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

  Lemma same_blocks_alloc m cp lo hi m' b ge
    (ALLOC : Mem.alloc m cp lo hi = (m', b))
    (BLOCKS : same_blocks ge m) :
    same_blocks ge m'.
  Proof.
    intros b' cp' FIND.
    exploit BLOCKS; eauto. intros m_b'.
    erewrite Mem.alloc_block_compartment; eauto.
    rewrite dec_eq_false; trivial. intros ->.
    assert (~ Mem.valid_block m b) as contra
        by eauto using Mem.fresh_block_alloc.
    rewrite Mem.block_compartment_valid_block in contra.
    congruence.
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
    { same_dom: same_domain_right ge1 m1;
      partial_mem_inject: Mem.inject j m1 m2;
      j_delta_zero: Mem.delta_zero j;
      (* FIXME: The condition below contradicts same_domain_right when the left
         side has a public symbol.  This is because symbols_inject says that any
         public symbol must be covered by the memory injection. *)
      (* TODO replace symbols_inject with meminj_preserves_globals *)
      same_symb: forall cp, s cp = Right -> symbols_inject j ge1 ge2 (Genv.find_comp_of_ident ge1) cp;
      same_blks1: same_blocks ge1 m1;
      same_blks2: same_blocks ge2 m2;
    }.


Lemma right_mem_injection_right ge1 ge2 m1 m2 b1 b2 delta :
  right_mem_injection ge1 ge2 m1 m2 ->
  j b1 = Some (b2, delta) ->
  exists cp, Mem.block_compartment m2 b2 = Some cp /\
             (s cp = Left -> exists fd, Genv.find_def ge1 b1 = Some (Gfun fd)).
Proof.
  intros [DOM MI _ _ BLOCKS1 BLOCKS2] j_b1.
  assert (j b1 <> None) as j_b1_def by congruence.
  apply DOM in j_b1_def. simpl in j_b1_def.
  destruct (Mem.block_compartment m1 b1) as [cp|] eqn:m1_b1.
  - exists cp. split.
    + enough (Mem.can_access_block m2 b2 (Some cp)) by (simpl in *; eauto).
      eauto using Mem.mi_inj, Mem.mi_own.
    + intros LEFT.
      destruct j_b1_def as [RIGHT | [fd DEF]]; [congruence | now eauto].
  - destruct j_b1_def as [CONTRA | [fd DEF]]; [contradiction |].
    apply Genv.find_funct_ptr_iff in DEF.
    exploit Genv.find_funct_ptr_find_comp_of_block; eauto. intros COMP.
    exploit BLOCKS1; eauto. congruence.
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

Section Simulation.
  Context (c p1 p2: Clight.program).
  Variable s: split.

  Context (W1 W2: Clight.program).
  Hypothesis c_p1: link p1 c = Some W1.
  Hypothesis c_p2: link p2 c = Some W2.

  Hypothesis match_W1_W2: match_prog s W1 W2.

  Hypothesis W1_ini: exists s, Smallstep.initial_state (semantics1 W1) s.
  Hypothesis W2_ini: exists s, Smallstep.initial_state (semantics1 W2) s.

  Hypothesis W1_compat: clight_compatible s p1 c.
  Hypothesis W2_compat: clight_compatible s p2 c.

  (* TODO These become redundant *)
  Hypothesis c_Right: s |= c ∈ Right.
  Hypothesis p1_Left: s |= p1 ∈ Left.
  Hypothesis p2_Left: s |= p2 ∈ Left.

  Hypothesis main_is_public:
    forall {F} (p: Ctypes.program F), In (prog_main p) (prog_public p).

  (* Context (ge1 ge2: genv). *)
  Notation ge1 := (globalenv W1).
  Notation ge2 := (globalenv W2).
(*
  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol ge2 s = Genv.find_symbol ge1 s.
  Proof (Genv.find_symbol_match match_W1_W2).
*)

  Definition wf_gvar_init (ge: genv) :=
    forall gv b,
      Genv.find_var_info ge b = Some gv ->
      Forall
        (fun i =>
           forall id ofs,
             i = Init_addrof id ofs ->
             Genv.find_comp_of_ident ge id = Some (comp_of gv))
        (gvar_init gv).

  Hypothesis W1_gvars: wf_gvar_init ge1.
  Hypothesis W2_gvars: wf_gvar_init ge2.

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

Lemma right_state_injection_same_side_right: forall {j ge1 ge2 s1 s2 sd},
  right_state_injection s j ge1 ge2 s1 s2 ->
  s |= s1 ∈ sd ->
  s |= s2 ∈ sd.
Proof.
  intros j ge1 ge2 s1 s2 sd RINJ SIDE.
  destruct sd; inv RINJ.
  - assumption.
  - exfalso. eapply state_split_contra; eauto.
  - exfalso. eauto using state_split_contra.
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

  Lemma assign_loc_can_access_block ce cp ty m b ofs bf v m' :
    assign_loc ce cp ty m b ofs bf v m' ->
    Mem.block_compartment m b = Some cp.
  Proof.
    intros A. case A; clear.
    - simpl. intros v chunk m' _ STORE.
      exploit Mem.store_valid_access_3; eauto.
      now intros (_ & ? & _).
    - simpl. intros _ _ bytes m' _ _ _ _ _ STORE.
      exploit Mem.storebytes_can_access_block_1; eauto.
    - intros sz sg pos width v m' v' STORE.
      inv STORE. simpl in *.
      exploit Mem.store_valid_access_3; eauto.
      now intros (_ & ? & _).
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

  Lemma same_blocks_step1 s1 t s1'
    (BLKS : same_blocks ge1 (memory_of s1))
    (STEP : step1 ge1 s1 t s1'):
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

  Lemma init_mem_same_blocks (p: program) m1
        (MEM: Genv.init_mem p = Some m1):
    same_blocks (globalenv p) m1.
  Proof.
    intros b cp COMP.
    unfold Genv.find_comp_of_block in COMP.
    destruct Genv.find_def eqn:DEF; [| discriminate].
    injection COMP as <-.
    exact (Genv.init_mem_find_def _ _ MEM DEF).
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
    unfold Genv.allowed_addrof.
    intros cp id RIGHT H.
    exploit match_prog_globdefs; eauto. rewrite RIGHT. simpl.
    intros (b1 & b2 & ge1_id & ge2_id & MATCH).
    unfold Genv.find_comp_of_ident in *.
    simpl in H. rewrite ge1_id in H.
    rewrite ge2_id.
    unfold Genv.find_comp_of_block in *. now rewrite <- MATCH.
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
  destruct MEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
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
  - eauto using same_domain_right_free.
  - exploit Mem.free_parallel_inject; eauto.
    rewrite !Z.add_0_r. intros (? & ? & ?). congruence.
  - eapply same_blocks_free; eauto.
  - eapply same_blocks_free; eauto.
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
  destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
  split; trivial.
  - eauto using same_domain_right_free_list.
  - eauto using Mem.free_list_left_inject.
  - eauto using same_blocks_free_list.
Qed.

Lemma right_mem_injection_free_list_left':
  forall {j m1 m2 blks cp m2'}
         (RMEMINJ : right_mem_injection s j ge1 ge2 m1 m2)
         (LEFT : s cp = Left)
         (FREE2 : Mem.free_list m2 blks cp = Some m2'),
    right_mem_injection s j ge1 ge2 m1 m2'.
Proof.
  intros.
  split; try now destruct RMEMINJ.
  - assert (Mem.unchanged_on (loc_not_in_compartment cp m2) m2 m2')
      as UNCHANGED.
    { exploit Mem.free_list_unchanged_on; eauto.
      apply Forall_forall. simpl. unfold loc_not_in_compartment.
      intros [[b lo] hi] _ m2_b _ _ ?. congruence. }
    exploit Mem.unchanged_on_inject'; eauto using partial_mem_inject.
    intros b1 b2 delta ofs j_b1 m2_b2.
    exploit right_mem_injection_right; eauto.
    intros (? & m2_b2' & DEF). rewrite m2_b2 in m2_b2'. injection m2_b2' as <-.
    specialize (DEF LEFT) as [fd DEF].
    admit.
  - destruct RMEMINJ; eauto using same_blocks_free_list.
(* Qed. *)
Admitted.

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
    destruct inj as [inj_dom inj_inject j_delta_zero same_symb SAMEBLKS].
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
      assert (id_cp : Genv.find_comp_of_ident ge1 id = Some cp).
      { trivial. }
      assert (b_right : (s, m1) |= b ∈ Right).
      { unfold Mem.has_side_block. simpl.
        unfold Genv.find_comp_of_ident in id_cp.
        rewrite W1_id in id_cp.
        apply SAMEBLKS in id_cp. now rewrite id_cp. }
      eapply or_introl in b_right.
      apply idP in b_right.
      destruct (j b) as [[loc' ofs']|] eqn:j_b; try easy.
      clear b_right idP.
      exists loc', ofs'. split; trivial.
      assert (ofs' = 0 /\ Genv.find_symbol (globalenv W2) id = Some loc')
          as [? W2_id].
      { specialize (same_symb cp) as (_ & same_symb & _); auto.
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
    symbols_inject j ge1 ge2 (Genv.find_comp_of_ident ge1) (comp_of f) ->
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
      { exploit same_symb; eauto. instantiate (1 := cp). admit.
        intros (H1 & H2 & H3 & H4).
        exploit H2; eauto. intros (-> & ge2_id). now simpl in ge2_id. }
      now exploit find_comp_of_block_preserved; eauto.
    - unfold Genv.allowed_cross_call in *.
      revert cross. case vf12; try easy.
      simpl. intros b1 _ b2 ofs2 delta j_b1 _.
      intros (id & cp' & ge1_b1 & ge1_b1' & imp & exp).
      exists id, cp'.
      exploit same_symb; eauto. instantiate (1 := cp). admit. intros (H1 & H2 & H3 & H4). simpl in *.
      exploit Genv.invert_find_symbol; eauto. intros ge1_id.
      exploit H2; eauto. intros (-> & ge2_id).
      split; [now apply Genv.find_invert_symbol|].
      split.
      { exploit find_comp_of_block_preserved; eauto. }
      rewrite Genv.globalenv_policy in *. simpl in *.
      now rewrite (match_prog_pol _ _ _ match_W1_W2); split.
  (* Qed. *)
  Admitted.

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
    exploit same_symb; eauto. admit.
    intros (_ & H & ?).
    now destruct (H id b1 b2 delta j_b1 FIND1) as [??].
  (* Qed. *)
  Admitted.

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
    split; [| split; [| split; [| split]]].
    - rewrite sizeof_preserved. assumption.
    - destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
      constructor; auto.
      + intros b. specialize (DOM b).
        simpl in *.
        rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ ALLOC).
        destruct eq_block as [<-|b_b1].
        { rewrite ZERO. intuition congruence. }
        now rewrite EXT; trivial.
      + intros b1' b2' delta j'_b1. specialize (D0 b1' b2' delta).
        destruct (peq b1' b1) as [-> | NEQ].
        * rewrite ZERO in j'_b1. injection j'_b1 as <- <-.
          reflexivity.
        * specialize (EXT b1' NEQ). rewrite EXT in j'_b1.
          auto.
      + intros cp' RIGHT'.
        specialize (SYMB cp' RIGHT') as (PUB & FIND & PUB_FIND & VOL).
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
        * intros id' b1' PUB_id id_b1' id'_b1'.
          specialize (PUB_FIND id' b1' PUB_id id_b1' id'_b1') as (b2' & b1'_b2' & id'_b2').
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

  Lemma same_domain_right_alloc_left :
    forall j ge m cp lo hi m' b,
      same_domain_right s j ge m ->
      Mem.alloc m cp lo hi = (m', b) ->
      s cp = Left ->
      same_domain_right s j ge m'.
  Proof.
    intros j ge m cp lo hi m' b j_m m_m' s_cp b'.
    specialize (j_m b'). simpl in *.
    rewrite (Mem.alloc_block_compartment _ _ _ _ _ _ m_m').
    destruct eq_block as [->|?]; trivial.
    destruct (Mem.block_compartment m b) as [cp'|] eqn:m_b.
    - assert (~ ~ Mem.valid_block m b) as valid.
      { rewrite Mem.block_compartment_valid_block.
        congruence. }
      pose proof (Mem.fresh_block_alloc _ _ _ _ _ _ m_m').
      easy.
    - rewrite j_m, s_cp. split.
      + intros [[] | [fd DEF]]. eauto.
      + intros [| [fd DEF]]; [discriminate |]. eauto.
  Qed.

  Lemma right_mem_injection_alloc_left {j cp m1 m2 m1' b1 lo hi}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (LEFT: s cp = Left)
    (ALLOC: Mem.alloc m1 cp lo hi = (m1', b1)):
    right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
    split; trivial.
    - eauto using same_domain_right_alloc_left.
    - eauto using Mem.alloc_left_unmapped_inject_strong.
    - eauto using same_blocks_alloc.
  Qed.

  Lemma right_mem_injection_alloc_left' {j cp m1 m2 m2' b2 lo hi}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (LEFT: s cp = Left)
    (ALLOC: Mem.alloc m2 cp lo hi = (m2', b2)):
    right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
    split; trivial.
    - eauto using Mem.alloc_right_inject.
    - eauto using same_blocks_alloc.
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
    destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
    exploit Mem.store_mapped_inject; eauto.
    rewrite Z.add_0_r. intros (m2' & STORE2 & INJ').
    exists m2'; split; trivial. constructor; trivial;
    eauto using same_domain_right_store, same_blocks_store.
  Qed.

  Lemma right_mem_injection_store_unmapped :
    forall {j chunk m1 m2 b1 ofs v1 cp m1'}
           (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (LOCINJ: j b1 = None)
           (STORE1: Mem.store chunk m1 b1 ofs v1 cp = Some m1'),
      right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    intros.
    destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
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
    destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
    exploit Mem.store_outside_inject; eauto.
    { intros ??? INJ. destruct (LOCINJ _ _ INJ). }
    intros MI'.
    constructor; trivial; eauto using same_blocks_store.
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
    intros [DOM MI D0 SYMB BLKS1 BLKS2] b1_b2 BYTESINJ STORE1.
    exploit Mem.storebytes_mapped_inject; eauto.
    rewrite Z.add_0_r. intros (m2' & STORE2 & MI').
    exists m2'. split; trivial.
    constructor;
    eauto using same_domain_right_storebytes, same_blocks_storebytes.
  Qed.

  Lemma right_mem_injection_storebytes_unmapped
    {j m1 m2 b1 ofs bytes1 cp m1'} :
    forall (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (LOCINJ: j b1 = None)
           (STORE1: Mem.storebytes m1 b1 ofs bytes1 cp = Some m1'),
      right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    intros [DOM MI D0 SYMB BLKS1 BLKS2] LOCINJ STORE1.
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
    intros [DOM MI D0 SYMB BLKS1 BLKS2] LOCINJ STORE2.
    exploit Mem.storebytes_outside_inject; eauto.
    { intros. eapply LOCINJ. eauto. }
    constructor;
    eauto using same_domain_right_storebytes, same_blocks_storebytes.
  Qed.

Lemma same_domain_right_assign_loc
        e ge j cp ty m b ofs bf v m' :
  assign_loc e cp ty m b ofs bf v m' ->
  same_domain_right s ge j m ->
  same_domain_right s ge j m'.
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
    destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
    constructor; eauto using same_domain_right_assign_loc, same_blocks_assign_loc.
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
    (LEFT: s cp = Left):
    right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    induction BIND as [
      | m1 id ty params v1 vl1 b1 m1' m1'' e1_id ASSIGN1 _ IH]; trivial.
    exploit @right_mem_injection_assign_loc_unmapped; eauto.
    exploit assign_loc_can_access_block; eauto. intros m1_b1.
    destruct (j b1) as [?|] eqn:j_b1; trivial.
    assert (j b1 <> None) as contra by congruence.
    eapply same_dom in contra; eauto. simpl in contra.
    rewrite m1_b1, LEFT in contra.
    destruct contra as [| [fd DEF]]; [discriminate |].
    admit. (* cannot bind parameters to function block *)
  (* Qed. *)
  Admitted.

  Lemma right_mem_injection_bind_parameters_left'
    {j m1 m2 m2' e2 vargs2 params cp}
    (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
    (BIND: bind_parameters ge2 cp e2 m2 params vargs2 m2')
    (LEFT: s cp = Left):
    right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    induction BIND as [
      | m2 id ty params v2 vl2 b2 m2' m2'' e2_id ASSIGN2 _ IH]; trivial.
    exploit @right_mem_injection_assign_loc_outside; eauto.
    exploit assign_loc_can_access_block; eauto. intros m2_b2.
    intros b1 delta j_b1.
    assert (j b1 <> None) as contra by congruence.
    eapply same_dom in contra; eauto. simpl in contra.
    destruct contra as [contra | [fd DEF]].
    - destruct (Mem.block_compartment m1 b1) as [cp'|] eqn:m1_b1; try easy.
      exploit partial_mem_inject; eauto. intros INJ.
      exploit Mem.mi_inj; eauto. intros INJ'.
      enough (Mem.can_access_block m2 b2 (Some cp')).
      { simpl in *; congruence. }
      eapply Mem.mi_own; eauto.
    - admit. (* cannot bind parameters to function block *)
  (* Qed. *)
  Admitted.

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
    eauto using right_mem_injection_bind_parameters_left.
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
    eauto using right_mem_injection_bind_parameters_left'.
  Qed.

  (* FIXME: Move to Genv. *)
  Lemma invert_symbol_find_comp_of_block p b id :
    Genv.invert_symbol (globalenv p) b = Some id ->
    exists cp, Genv.find_comp_of_block (globalenv p) b = Some cp.
  Proof.
    intros ge_b.
    apply Genv.invert_find_symbol in ge_b.
    destruct (Genv.find_symbol_find_def_inversion _ _ ge_b) as [def def_ge_b].
    unfold Genv.find_comp_of_block. simpl.
    unfold program, fundef in *. rewrite def_ge_b. eauto.
  Qed.

  Lemma same_blocks_extcall :
    forall sem cp sg (ge: genv) vargs m t v m',
      extcall_properties sem cp sg ->
      sem ge vargs m t v m' ->
      same_blocks ge m ->
      same_blocks ge m'.
  Proof.
    intros sem cp sg ge vargs m t v m' EXT m_m' BLKS b cp' b_cp'.
    specialize (BLKS _ _ b_cp').
    enough (Mem.can_access_block m' b (Some cp')) by trivial.
    eauto using ec_can_access_block.
  Qed.

  Lemma symbols_inject_incr : forall j j' m1 m2 find_comp cp,
      symbols_inject j ge1 ge2 find_comp cp ->
      same_blocks ge1 m1 ->
      same_blocks ge2 m2 ->
      inject_incr j j' ->
      inject_separated j j' m1 m2 ->
      symbols_inject j' ge1 ge2 find_comp cp.
  Proof.
    intros j j' m1 m2 find_comp cp SYMB BLKS1 BLKS2 incr j_j'_sep.
    destruct SYMB as (SYMB1 & SYMB2 & SYMB3 & SYMB4).
    split; [|split; [|split]]; eauto.
    - intros id b1 b2 delta j'_b1 ge1_id.
      destruct (j b1) as [[b2' delta']|] eqn:j_b1.
      { exploit incr; eauto. rewrite j'_b1.
        intros I. injection I as <- <-.
        eauto. }
      exploit j_j'_sep; eauto. intros (invalid_b1 & invalid_b2).
      pose proof (Genv.find_invert_symbol _ _ ge1_id) as ge1_b1.
      apply invert_symbol_find_comp_of_block in ge1_b1.
      destruct ge1_b1 as [cp' ge1_b1].
      exploit BLKS1; eauto. intros m1_b1.
      apply Mem.block_compartment_valid_block in invalid_b1.
      congruence.
    - intros id b1 comp_id public_id id_b1.
      exploit SYMB3; eauto. intros (b2 & j_b1 & id_b2).
      eauto.
    - intros b1 b2 delta j'_b1.
      destruct (j b1) as [[b2' delta']|] eqn:j_b1.
      { exploit incr; eauto. rewrite j'_b1.
        intros I. injection I as <- <-.
        eauto. }
      exploit j_j'_sep; eauto. intros (invalid_b1 & invalid_b2).
      simpl.
      destruct (Genv.block_is_volatile _ b2) eqn:volatile_b2.
      { exfalso. apply invalid_b2.
        eauto using block_is_volatile_valid_block. }
      destruct (Genv.block_is_volatile _ b1) eqn:volatile_b1; trivial.
      exfalso. apply invalid_b2.
      eauto using block_is_volatile_valid_block.
  Qed.

  Lemma right_mem_injection_external_call_right {j ef vargs1 vargs2 vres1 t m1 m1' m2}
    (RMEMINJ : right_mem_injection s j ge1 ge2 m1 m2)
    (EXTCALL: external_call ef ge1 vargs1 m1 t vres1 m1')
    (ARGINJ: Val.inject_list j vargs1 vargs2)
    (RIGHT: s (comp_of ef) = Right):
    exists j' m2' vres2,
      external_call ef ge2 vargs2 m2 t vres2 m2' /\
      right_mem_injection s j' ge1 ge2 m1' m2' /\
      inject_incr j j' /\
      Val.inject j' vres1 vres2.
  Proof.
    pose proof (external_call_spec ef) as ef_props.
    exploit ec_mem_inject; eauto.
    { eapply same_symb; eauto. }
    { eapply partial_mem_inject; eauto. }
    intros (j' & vres2 & m2' & is_ext & inj_res & inj' & unchanged1 & unchanged2 &
              incr & j_j'_sep & comps_m1').
    exists j', m2', vres2.
    split; [| split; [| split]]; auto.
    destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
    assert (same_domain_right s j' ge1 m1') as DOM'.
    { (* FIXME: Separate lemma? *)
      clear - DOM incr j_j'_sep comps_m1' unchanged1 RIGHT inj'.
      intros b. specialize (DOM b). simpl in *.
      destruct (Mem.block_compartment m1 b) as [cp|] eqn:block_m1_b.
      + assert (Mem.valid_block m1 b) as valid_m1_b.
        { eapply Mem.can_access_block_valid_block; simpl; eauto. }
        assert (Mem.can_access_block m1' b (Some cp)) as block_m1'_b.
        { apply (Mem.unchanged_on_own _ _ _ unchanged1); eauto. }
        simpl in block_m1'_b. rewrite block_m1'_b.
        destruct (j b) as [[b' ofs]|] eqn:j_b.
        * assert (s cp = Right \/
                  (exists fd : fundef, Genv.find_def (Genv.globalenv W1) b = Some (Gfun fd)))
            as [cp_right | [fd DEF]] by (apply DOM; congruence).
          -- rewrite (incr _ _ _ j_b). intuition.
          -- split; eauto.
             intros ? j'_b.
             admit. (* cannot invalidate function block *)
        * rewrite <- DOM. split; eauto.
          destruct (j' b) as [[b'' ofs']|] eqn:j'_b; try congruence.
          exploit j_j'_sep; eauto.
          rewrite Mem.block_compartment_valid_block, block_m1_b.
          intuition congruence.
      + destruct (Mem.block_compartment m1' b) as [cp|] eqn:block_m1'_b.
        * assert (~ Mem.valid_block m1 b) as invalid_m1_b.
          { apply Mem.block_compartment_valid_block. eauto. }
          assert (Mem.valid_block m1' b) as valid_m1_b.
          { eapply Mem.can_access_block_valid_block; simpl; eauto. }
          exploit comps_m1'; eauto.
          intros (b' & -> & block_m1'_b_alt).
          assert (cp = comp_of ef) as -> by congruence.
          clear block_m1'_b_alt.
          split; try congruence.
          auto.
        * split; eauto.
          -- rewrite <- Mem.block_compartment_valid_block in block_m1'_b.
             eapply Mem.mi_freeblocks in block_m1'_b; eauto.
          -- intros [[] | [fd DEF]].
             admit. (* cannot invalidate function block *) }
    constructor;
    eauto using symbols_inject_incr, external_call_spec, same_blocks_extcall.
    intros b b' delta j'_b.
    destruct (j b) as [[b'' delta'']|] eqn:j_b.
    - exploit D0; eauto. intros ->.
      exploit incr; eauto. congruence.
    - exploit j_j'_sep; eauto. intros [invalid_b _].
      enough (Mem.valid_block m1' b) as valid_b.
      { exploit comps_m1'; eauto.
        intros (? & ? & ?). congruence. }
      apply Classical_Prop.NNPP. (* FIXME *) intros contra.
      exploit Mem.mi_freeblocks; eauto. congruence.
  (* Qed. *)
  Admitted.

  Lemma right_mem_injection_external_call_left :
    forall j ef vargs1 vres1 t m1 m1' m2
           (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (EXTCALL: external_call ef ge1 vargs1 m1 t vres1 m1')
           (LEFT: s (comp_of ef) = Left),
      right_mem_injection s j ge1 ge2 m1' m2.
  Proof.
    intros.
    destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
    constructor; eauto.
    - intros b. specialize (DOM b). simpl in *.
      destruct (Mem.block_compartment m1 b) as [cp|] eqn:m1_b.
      + assert (Mem.can_access_block m1' b (Some cp)) as m1'_b.
        { exploit ec_can_access_block; eauto.
          { apply external_call_spec. }
          eauto. }
        simpl in m1'_b. now rewrite m1'_b.
      + destruct (Mem.block_compartment m1' b) as [cp|] eqn:m1'_b; trivial.
        rewrite <- Mem.block_compartment_valid_block in m1_b.
        assert (Mem.valid_block m1' b) as m1'_b_valid.
        { eapply Mem.can_access_block_valid_block. simpl. eauto. }
        exploit ec_new_valid; eauto.
        { eapply external_call_spec. }
        intros E. assert (cp = comp_of ef) as -> by congruence.
        intuition congruence.
    - exploit ec_mem_outside_compartment; eauto.
      { apply external_call_spec. }
      intros m1_m1'.
      exploit Mem.unchanged_on_inject; eauto.
      intros b off j_b_undef m1_b.
      apply DOM in j_b_undef. simpl in j_b_undef.
      rewrite m1_b in j_b_undef.
      destruct j_b_undef as [| [fd DEF]]; [congruence |].
      admit.
    - intros b cp ge_b. specialize (BLKS1 _ _ ge_b).
      enough (Mem.can_access_block m1' b (Some cp)) by easy.
      eapply ec_can_access_block; eauto.
      { apply external_call_spec. }
  (* Qed. *)
  Admitted.

  Lemma right_mem_injection_external_call_left' :
    forall j ef vargs2 vres2 t m1 m2 m2'
           (RMEMINJ: right_mem_injection s j ge1 ge2 m1 m2)
           (EXTCALL: external_call ef ge2 vargs2 m2 t vres2 m2')
           (LEFT: s (comp_of ef) = Left),
      right_mem_injection s j ge1 ge2 m1 m2'.
  Proof.
    intros.
    destruct RMEMINJ as [DOM MI D0 SYMB BLKS1 BLKS2].
    constructor; eauto.
    - exploit ec_mem_outside_compartment; eauto.
      { apply external_call_spec. }
      intros m2_m2'.
      exploit Mem.unchanged_on_inject'; eauto.
      intros b1 b2 delta ofs j_b1 m2_b2.
      assert (j b1 <> None) as j_b1_def by congruence.
      apply DOM in j_b1_def. simpl in j_b1_def.
      destruct (Mem.block_compartment m1 b1) as [cp|] eqn:m1_b1.
      + destruct j_b1_def as [j_b1_def | [fd DEF]].
        * enough (Mem.can_access_block m2 b2 (Some cp)) by (simpl in *; congruence).
          exploit Mem.mi_inj; eauto. intros INJ'.
          eapply Mem.mi_own; eauto.
        * admit.
      + destruct j_b1_def as [[] | [fd DEF]].
        apply Genv.find_funct_ptr_iff in DEF.
        assert (COMP := Genv.find_funct_ptr_find_comp_of_block _ _ DEF).
        exploit BLKS1; eauto. congruence.
    - intros b cp ge_b. specialize (BLKS2 _ _ ge_b).
      enough (Mem.can_access_block m2' b (Some cp)) by easy.
      eapply ec_can_access_block; eauto.
      { apply external_call_spec. }
  (* Qed. *)
  Admitted.

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
    assert (COMP1: Genv.find_comp_of_ident ge1 id = Some (comp_of fd1)). {
      unfold Genv.find_comp_of_ident. setoid_rewrite SYM1.
      eapply Genv.find_funct_ptr_find_comp_of_block in FUN1.
      exact FUN1. }
    destruct (match_prog_globdefs _ _ _ match_W1_W2
                                  _ _ (or_introl COMP1) (or_introl RIGHT))
      as (b1' & b2' & SYM1' & SYM2' & MATCH).
    setoid_rewrite SYM1 in SYM1'. injection SYM1' as <-.
    setoid_rewrite SYM2 in SYM2'. injection SYM2' as <-.
    unfold match_opt_globdefs in MATCH. rewrite RIGHT in MATCH.
    unfold Genv.find_funct_ptr in FUN1, FUN2.
    setoid_rewrite <- MATCH in FUN2.
    destruct (Genv.find_def _ b1) as [f |] eqn:DEF; [| discriminate].
    destruct f; [| discriminate].
    congruence.
  Qed.

  (** Sub-invariant lemmas, mostly on injections *)

  Lemma right_mem_injection_left_step_1: forall j s1 t s2 s1',
    right_mem_injection s j ge1 ge2 (memory_of s1) (memory_of s2) ->
    s |= s1 ∈ Left ->
    step1 ge1 s1 t s1' ->
    right_mem_injection s j ge1 ge2 (memory_of s1') (memory_of s2).
  Proof.
    intros j s1 t s2 s1' RMEMINJ LEFT STEP.
    inversion STEP; subst; try eauto.
    - (* assign *)
      simpl in *.
      assert (j loc = None).
      { exploit assign_loc_can_access_block; eauto.
        intros m_loc. destruct RMEMINJ as [DOM].
        specialize (DOM loc). simpl in DOM. rewrite m_loc, LEFT in DOM.
        destruct (j loc) as [p|] eqn:j_loc; eauto.
        enough (Left = Right \/
                (exists fd : fundef, Genv.find_def (Genv.globalenv W1) loc = Some (Gfun fd)));
          [| now apply DOM].
        destruct H3 as [| [fd DEF]]; [discriminate |].
        admit. (* cannot assign_loc to function block *) }
      exploit @right_mem_injection_assign_loc_unmapped; eauto.
    - (* builtin *)
      simpl in *.
      exploit right_mem_injection_external_call_left; eauto.
      congruence.
    - (* return 0 *)
      simpl in *.
      eauto using right_mem_injection_free_list_left.
    - (* return 1 *)
      simpl in *.
      eauto using right_mem_injection_free_list_left.
    - (* skip call *)
      simpl in *.
      eauto using right_mem_injection_free_list_left.
    - (* internal function *)
      simpl in *.
      eauto using right_mem_injection_function_entry1_left.
    - (* external call *)
      simpl in *.
      exploit right_mem_injection_external_call_left; eauto.
  (* Qed. *)
  Admitted.

  Lemma right_mem_injection_left_step_2: forall j s1 s2 t s2',
    right_mem_injection s j ge1 ge2 (memory_of s1) (memory_of s2) ->
    s |= s2 ∈ Left ->
    step1 ge2 s2 t s2' ->
    right_mem_injection s j ge1 ge2 (memory_of s1) (memory_of s2').
  Proof.
    intros j s1 s2 t s2' RMEMINJ LEFT STEP.
    inversion STEP; subst; try eauto.
    - (* assign *)
      simpl in *.
      assert (forall b delta, j b <> Some (loc, delta)).
      { exploit assign_loc_can_access_block; eauto.
        intros m_loc b delta j_b. destruct RMEMINJ as [DOM].
        assert (j b <> None) as j_b_def by congruence.
        apply DOM in j_b_def. simpl in j_b_def.
        destruct j_b_def as [j_b_def | [fd DEF]].
        + destruct (Mem.block_compartment (memory_of s1) b) as [cp|] eqn:s1_b;
            try easy.
          enough (Mem.can_access_block m loc (Some cp))
            by (simpl in *; congruence).
          eapply Mem.mi_own; eauto. now eapply Mem.mi_inj.
        + admit. (* cannot assign loc to function block *) }
      exploit @right_mem_injection_assign_loc_outside; eauto.
    - (* builtin *)
      simpl in *.
      exploit right_mem_injection_external_call_left'; eauto.
      congruence.
    - (* return 0 *)
      simpl in *.
      eauto using right_mem_injection_free_list_left'.
    - (* return 1 *)
      simpl in *.
      eauto using right_mem_injection_free_list_left'.
    - (* skip call *)
      simpl in *.
      eauto using right_mem_injection_free_list_left'.
    - (* internal function *)
      simpl in *.
      eauto using right_mem_injection_function_entry1_left'.
    - (* external call *)
      simpl in *.
      exploit right_mem_injection_external_call_left'; eauto.
  (* Qed. *)
  Admitted.

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

Lemma remove_until_right_step: forall ge s1 t s1',
  s |= s1 ∈ Left ->
  s |= s1' ∈ Left ->
  step1 ge s1 t s1' ->
  remove_until_right s (cont_of s1') = remove_until_right s (cont_of s1).
Proof.
  intros ge s1 t s1' LEFT LEFT' STEP. inv STEP; auto; simpl.
  - rewrite LEFT. reflexivity.
  - symmetry. rewrite remove_until_right_call_cont. reflexivity.
  - symmetry. rewrite remove_until_right_call_cont. reflexivity.
  - rewrite <- (proj1 find_label_remove_until_right _ _ _ _ _ H).
    symmetry. rewrite remove_until_right_call_cont. reflexivity.
  - inv EV. unfold Genv.type_of_call in H.
    destruct (Pos.eqb_spec (comp_of f) cp) as [<- | NEQ].
    + rewrite LEFT. reflexivity.
    + contradiction.
    + simpl in LEFT'. now rewrite LEFT'.
Qed.

Lemma right_cont_injection_left_step_left_1: forall j s1 t s2 s1',
  right_cont_injection s j (remove_until_right s (cont_of s1)) (remove_until_right s (cont_of s2)) ->
  step1 ge1 s1 t s1' ->
  s |= s1 ∈ Left ->
  s |= s1' ∈ Left ->
  right_cont_injection s j (remove_until_right s (cont_of s1')) (remove_until_right s (cont_of s2)).
Proof.
  intros j s1 t s2 s1' RCONTINJ STEP LEFT LEFT'.
  now rewrite (remove_until_right_step _ _ _ _ LEFT LEFT' STEP).
Qed.

Lemma right_cont_injection_left_step_left_2: forall j s1 s2 t s2',
  right_cont_injection s j (remove_until_right s (cont_of s1)) (remove_until_right s (cont_of s2)) ->
  step1 ge2 s2 t s2' ->
  s |= s2 ∈ Left ->
  s |= s2' ∈ Left ->
  right_cont_injection s j (remove_until_right s (cont_of s1)) (remove_until_right s (cont_of s2')).
Proof.
  intros j s1 s2 t s2' RCONTINJ STEP LEFT LEFT'.
  now rewrite (remove_until_right_step _ _ _ _ LEFT LEFT' STEP).
Qed.

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
        { inv vf1_vf2; try discriminate.
          injection H1 as -> ->.
          exploit same_symb; eauto. instantiate (1 := comp_of f); auto. intros (_ & FIND & _ & _).
          destruct (FIND _ _ _ _ H ge1_id) as (-> & ge2_id').
          setoid_rewrite ge2_id in ge2_id'.
          injection ge2_id' as <-.
          reflexivity. }
        assert (Genv.find_funct ge2 vf2 = Some fd2) as find_vf2'.
        { unfold Genv.find_funct, Genv.find_funct_ptr. rewrite evf2.
          destruct Ptrofs.eq_dec as [_|?]; try congruence.
          now rewrite ge2_b2. }
        assert (type_of_fundef fd2 = Tfunction tyargs tyres cconv)
          as type_fd2.
        { inv match_fd''; eauto. }
        assert (Genv.allowed_call ge2 (comp_of f) vf2) as ALLOWED2.
        { eapply allowed_call_preserved; eauto. }
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
        exploit find_funct_preserved; eauto.
        { eapply same_symb; eauto. }
        intros find_vf2.
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
    + (* step_builtin *)
      (* prefix *)
      exploit eval_exprlist_injection; eauto.
      auto.
      intros [vs' [? ?]].
      (* same as step_external_function *)
      destruct (right_mem_injection_external_call_right RMEMINJ H0 H1)
        as (j' & m2' & vres' & EXTCALL' & RMEMINJ' & INCR & RESINJ).
      { simpl in *. congruence. }
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
      destruct (right_mem_injection_free_list_right RMEMINJ RENVINJ H is_r1) as (m2' & FREE' & RMEMINJ').
      inv RMEMINJ. exists j; eexists; split; [apply step_return_0 | apply RightControl]; eauto.
      constructor; auto.
      apply right_cont_injection_call_cont; auto.
    + (* step_return_1 *)
      destruct (right_mem_injection_free_list_right RMEMINJ RENVINJ H1 is_r1) as (m2' & FREE' & RMEMINJ').
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
      destruct (right_mem_injection_free_list_right RMEMINJ RENVINJ H0 is_r1) as (m2' & FREE' & RMEMINJ').
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
      destruct (right_mem_injection_external_call_right RMEMINJ H ARGINJ)
        as (j' & m2' & vres' & EXTCALL' & RMEMINJ' & INCR & RESINJ).
      { simpl in *. eauto. }
      exists j'; eexists; split.
      econstructor; eauto.
      apply RightControl; eauto.
      constructor; eauto.
      { eapply right_cont_injection_inject_incr; eauto. }
    + (* step_returnstate *)
      inv RCONTINJ.
      * exists j. eexists. split.
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
        }
        { apply LeftControl; auto.
          congruence.
        }
      * exists j. eexists. split.
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

  Lemma parallel_abstract_1: forall j s1 t s2 s1',
    right_state_injection s j ge1 ge2 s1 s2 ->
    step1 ge1 s1 t s1' ->
    s |= s1 ∈ Left ->
    s |= s1' ∈ Left ->
    right_state_injection s j ge1 ge2 s1' s2.
  Proof.
    intros j s1 t s2 s1' INJ LEFT LEFT' STEP.
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
    step1 ge2 s2 t s2' ->
    s |= s1 ∈ Left ->
    s |= s2' ∈ Left ->
    right_state_injection s j ge1 ge2 s1 s2'.
  Proof.
    intros j s1 s2 t s2' INJ STEP LEFT LEFT'.
    inversion INJ as [SIDE1 SIDE2 MEMINJ CONTINJ |]; subst; clear INJ;
      [| exfalso; eauto using state_split_contra].
    exploit right_mem_injection_left_step_2; eauto.
    intros MEMINJ'.
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

  Lemma step1_next_compartment: forall ge s1 t s1',
    step1 ge s1 t s1' ->
    match trace_next_compartment t with
    | Some cp => s |= s1' ∈ s cp
    | None => forall δ, s |= s1 ∈ δ -> s |= s1' ∈ δ
    end.
  Proof.
    intros ge s1 t s1' STEP.
    case STEP; simpl; clear t STEP; try solve [unfold E0; trivial; congruence].
    - intros f optid a al k e0 le m tyargs tyres cconv vf vargs fd t.
      intros _ _ _ _ _ _ _ TRACE. simpl.
      case TRACE; simpl; try solve [unfold E0; congruence]; trivial.
      unfold Genv.type_of_call.
      intros cp cp'.
      destruct (Pos.eqb_spec cp cp') as [->|]; congruence.
    - intros f optid ef tyargs al k e le m vars t vres m' _ _ CALL.
      exploit ec_no_crossing; eauto.
      { eapply external_call_spec. }
      destruct t as [|[] [|??]]; simpl; intuition eauto.
    - intros ef targs tres cconv vargs k m vres t m' CALL.
      exploit ec_no_crossing; eauto.
      { eapply external_call_spec. }
      destruct t as [|[] [|??]]; simpl; intuition eauto.
    - intros v optid f e le ty cp k m t _ RET. simpl.
      case RET; simpl; eauto.
      intros cp1 cp2 _ _.
      unfold Genv.type_of_call.
      destruct (Pos.eqb_spec cp1 cp2) as [->|]; congruence.
  Qed.

  Lemma ec_no_crossing' ef ge vargs m t vres m' :
    external_call ef ge vargs m t vres m' ->
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
    destruct (Pos.eqb_spec cp cp') as [->|?]; try congruence.
    eauto 10.
  Qed.

  Lemma return_trace_cons_inv F V (ge: Genv.t F V) cp cp' vret tyret t :
    return_trace ge cp cp' vret tyret t ->
    t <> E0 ->
    exists res,
      t = Event_return cp cp' res :: nil /\
      cp <> cp' /\
      eventval_match ge res (proj_rettype tyret) vret.
  Proof.
    intros rt; inv rt; try congruence; eauto.
    intros _.
    unfold Genv.type_of_call in *.
    destruct (Pos.eqb_spec cp cp') as [->|?]; try congruence.
    eauto 10.
  Qed.

  Lemma call_trace_return_trace F V (ge1 ge2: Genv.t F V)
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
    step1 ge1 s1 t s1' ->
    step1 ge2 s2 t s2' ->
    right_state_injection s j ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' s2' t INJ LEFT1 STEP1 STEP2.
    assert (s |= s2 ∈ Left) as LEFT2.
    { eauto using right_state_injection_same_side_right. }
    pose proof (step1_next_compartment _ _ _ _ STEP1) as EV1.
    pose proof (step1_next_compartment _ _ _ _ STEP2) as EV2.
    (* If the next states remain on the left (which we can check by analyzing
       the value of trace_next_compartment), then the goal follows by a simple
       application of the previous parallel_abstract lemmas. *)
    assert (trace_next_compartment t = None \/
            exists cp, trace_next_compartment t = Some cp)
      as [E|[cp E]]; try rewrite E in *.
    { destruct trace_next_compartment; eauto. }
    { eauto using parallel_abstract_1, parallel_abstract_2. }
    destruct (s cp);
    eauto using parallel_abstract_1, parallel_abstract_2.
    (* Now, we know that s1' and s2' are on the right. *)
    rename EV1 into RIGHT1'. rename EV2 into RIGHT2'.
    assert (trace_next_compartment t <> None) as DEF by congruence.
    clear cp E.
    destruct INJ as [_ _ MEMINJ CONTINJ|];
      try solve [exfalso; eauto using state_split_contra].
    revert STEP2 DEF MEMINJ CONTINJ LEFT1 RIGHT1'.
    case STEP1; clear STEP1 s1 s1' t;
      try solve [ simpl; congruence
                | intros; exploit ec_no_crossing'; eauto; congruence ].
    - (* step_call *)
      intros f1 optid1 a1 al1 k1 e1 le1 m1 tyargs1 tyres1 cconv1 vf1 vargs1
        fd1 t _ _ _ vf1_fd1 type_fd1 _ not_ptr1
        trace_t1 STEP2 DEF MEMINJ CONTINJ LEFT1 RIGHT1'.
      simpl in LEFT1, RIGHT1', MEMINJ, CONTINJ.
      assert (Genv.type_of_call (comp_of f1) (comp_of fd1) =
                Genv.CrossCompartmentCall) as cross1.
      { unfold Genv.type_of_call.
        destruct (Pos.eqb_spec (comp_of f1) (comp_of fd1));
        congruence. }
      specialize (not_ptr1 cross1). clear cross1.
      revert DEF MEMINJ CONTINJ trace_t1 LEFT2 RIGHT2'.
      case STEP2; clear STEP2 s2 s2' t;
        try solve [ simpl; congruence
                  | intros; exploit ec_no_crossing'; eauto; congruence ].
      + (* matching case *)
        intros f2 optid2 a2 al2 k2 e2 le2 m2 tyargs2 tyres2 cconv2 vf2 vargs2
          fd2 t _ _ _ vf2_fd2 type_fd2 _ not_ptr2
          trace_t2 DEF MEMINJ CONTINJ trace_t1 LEFT2 RIGHT2'.
        simpl in LEFT2, RIGHT2', MEMINJ, CONTINJ.
        assert (Genv.type_of_call (comp_of f2) (comp_of fd2) =
                  Genv.CrossCompartmentCall) as cross2.
        { unfold Genv.type_of_call.
          destruct (Pos.eqb_spec (comp_of f2) (comp_of fd2));
          congruence. }
        specialize (not_ptr2 cross2). clear cross2.
        exploit call_trace_cons_inv; eauto.
        { intros ->; simpl in *; congruence. }
        clear trace_t1.
        intros (b1 & ofs1 & id & vl & -> & -> & _ & b1_id & match1).
        exploit call_trace_cons_inv; eauto.
        { unfold E0. congruence. }
        intros (b2 & ofs2 & id' & vl' & E1 & -> & _ & b2_id & match2).
        injection E1 as E11 E12 <- <-.
        simpl in vf1_fd1, vf2_fd2.
        destruct Ptrofs.eq_dec in vf1_fd1; try congruence.
        destruct Ptrofs.eq_dec in vf2_fd2; try congruence.
        assert (fd1 = fd2) as <- by (eapply find_funct_ptr_right; eauto).
        assert (tyargs2 = tyargs1) as -> by congruence.
        apply RightControl; trivial.
        apply inject_callstates; trivial.
        * apply right_cont_injection_kcall_left; try assumption.
        * eauto using eventval_list_match_inject_inv.
      + intros. exploit call_trace_return_trace; eauto.
        intros ->. simpl in *. congruence.
    - intros v1 optid1 f1 e1 le1 ty1 cp1 k1 m1 t cross1 ret1
        STEP2 DEF MEMINJ CONTINJ LEFT1 RIGHT1'.
      simpl in DEF, MEMINJ, CONTINJ, LEFT1, RIGHT1'.
      rewrite RIGHT1' in CONTINJ.
      revert DEF MEMINJ CONTINJ ret1 LEFT2 RIGHT2'.
      case STEP2; clear STEP2 s2 s2' t;
        try solve [ simpl; congruence
                  | intros; exploit ec_no_crossing'; eauto; congruence ].
      + intros. exploit call_trace_return_trace; eauto.
        intros ->. simpl in *. congruence.
      + intros v2 optid2 f2 e2 le2 ty2 cp2 k2 m2 t cross2 ret2
          DEF MEMINJ CONTINJ ret1 LEFT2 RIGHT2'.
        simpl in MEMINJ, CONTINJ, LEFT2, RIGHT2'.
        rewrite RIGHT2' in CONTINJ.
        assert (optid2 = optid1 /\
                  f2 = f1 /\
                  right_env_injection j e1 e2 /\
                  right_tenv_injection j le1 le2 /\
                  right_cont_injection s j k1 k2)
          as (-> & -> & ENVINJ & TENVINJ & CONTINJ').
        { inv CONTINJ; eauto. simpl in *. congruence. }
        exploit return_trace_cons_inv; eauto.
        { intros ->; simpl in *; congruence. }
        intros (res & -> & H11 & H12). clear ret1.
        exploit return_trace_cons_inv; eauto; try easy.
        intros (res' & E & _ & H22). clear ret2.
        injection E as <- <-.
        assert (Genv.type_of_call (comp_of f1) cp1 =
                  Genv.CrossCompartmentCall) as cross.
        { unfold Genv.type_of_call.
          destruct (Pos.eqb_spec (comp_of f1) cp1); trivial.
          congruence. }
        specialize (cross1 cross). specialize (cross2 cross).
        assert (Val.inject j v1 v2) as VALINJ.
        { inv H12; try easy; inv H22; try easy. }
        apply RightControl; eauto.
        apply inject_states; try assumption.
        destruct optid1 as [id|]; try assumption.
        intros id' v' GET. simpl in *.
        destruct (peq id' id) as [-> | NEQ].
        * rewrite PTree.gss in GET. injection GET as <-.
          simpl. rewrite PTree.gss. eauto.
        * rewrite PTree.gso in GET; trivial. rewrite PTree.gso; trivial.
          eauto.
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
  right_state_injection s j ge1 ge2 s1' s2'.
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
    exploit @right_state_injection_same_side_right; eauto. intros LEFT2.
    assert (s |= s2' ∈ Left) as LEFT2'.
    { apply (step_E0_same_side STEP2); eauto. }
    exploit parallel_abstract_2; eauto.
  - intros -> j s1''' s2 s2' s2'' e INJ LEFT STEP1' STAR2 STEP2.
    symmetry in SILENT. apply Eapp_E0_inv in SILENT as [-> ->].
    remember E0 as t eqn:SILENT.
    revert SILENT j s1''' s2'' e INJ LEFT STEP1' STEP2.
    induction STAR2 as [s2' | s2 t1 s2' t2 s2'' ? STEP2 STAR2 IH' SILENT].
    + intros _ j s1''' s2'' e INJ LEFT STEP1' STEP2.
      assert (s |= s1' ∈ Left) as LEFT1.
      { erewrite <- step_E0_same_side; eauto. }
      assert (right_state_injection s j ge1 ge2 s1' s2')
        as INJ' by (eapply parallel_abstract_1; eauto).
      exact (IH eq_refl _ _ _ _ _ _
               INJ' LEFT1 STEP1' (star_refl _ _ _) STEP2).
    + intros -> j s1''' s2''' e INJ LEFT STEP1' STEP2'.
      symmetry in SILENT. apply Eapp_E0_inv in SILENT as [-> ->].
      assert (s |= s2 ∈ Left).
      { eauto using right_state_injection_same_side_right. }
      assert (s |= s2' ∈ Left).
      { erewrite <- step_E0_same_side; eauto. }
      assert (right_state_injection s j ge1 ge2 s1 s2')
        as INJ' by (eapply parallel_abstract_2; eauto).
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
  - intros; eauto using parallel_abstract_star_E0.
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
(* TODO: delete? *)
Lemma blame_last_comp_star p s1 t s2:
  Smallstep.initial_state (semantics1 p) s1 ->
  Star (semantics1 p) s1 t s2 ->
  s |= s2 ∈ Left ->
  blame_on_program t.
Proof.
Admitted. (* With default_compartment gone, needs minor adjustments *)

(* WIP *)
Definition init_meminj_block (b: block): option block :=
  match Genv.invert_symbol ge1 b with
  | Some id =>
    match Genv.find_comp_of_ident ge1 id with
    | Some cp =>
      match s cp with
      | Left =>
          match Genv.find_def ge1 b with
          | Some (Gfun fd) =>
              match  Genv.find_symbol ge2 id with
              | Some b' => Some b'
              | None => None
              end
          | _ => None
          end
      | Right =>
        match Genv.find_symbol ge2 id with (* compact match *)
        | Some b' => Some b'
        | None => None (* should not happen *)
        end
      end
    | None => None (* should not happen *)
    end
  | None => None
  end.

Definition init_meminj: meminj :=
  fun b =>
    match init_meminj_block b with
    | Some b' => Some (b', 0)
    | None => None
    end.

Lemma find_symbol_init_mem_compartment (pr: program) m1 id b
      (SYM: Genv.find_symbol (Genv.globalenv pr) id = Some b)
      (MEM: Genv.init_mem pr = Some m1):
  Genv.find_comp_of_ident (Genv.globalenv pr) id =
  Mem.block_compartment m1 b.
Proof.
  unfold Genv.find_comp_of_ident.
  rewrite SYM.
  erewrite Genv.init_mem_block_compartment_find_comp_of_block; eauto.
Qed.

Lemma find_symbol_right id cp
  (SYM: Genv.find_symbol ge1 id <> None)
  (COMP : Genv.find_comp_of_ident ge1 id = Some cp)
  (RIGHT: s cp = Right):
  Genv.find_symbol ge2 id <> None.
Proof.
  exploit match_prog_globdefs; eauto.
  intros (? & ? & ? & ? & ?). congruence.
Qed.

Lemma init_mem_invert_symbol (pr: program) m b
  (NOREPET: list_norepet (prog_defs_names pr))
  (MEM: Genv.init_mem pr = Some m)
  (COMP : Mem.block_compartment m b <> None):
  Genv.invert_symbol (globalenv pr) b <> None.
Proof.
  erewrite Genv.init_mem_block_compartment_find_comp_of_block in COMP; eauto.
  unfold Genv.find_comp_of_block in *.
  destruct Genv.find_def as [d|] eqn:pr_b; try congruence.
  exploit Genv.find_def_find_symbol_inversion; eauto.
  intros (id & id_b).
  apply Genv.find_invert_symbol in id_b.
  simpl. unfold fundef in *. rewrite id_b. congruence.
Qed.

Lemma same_domain_right_init_meminj m1
      (MEM: Genv.init_mem W1 = Some m1):
  same_domain_right s init_meminj ge1 m1.
Proof.
  intros b. split.
  - unfold init_meminj, init_meminj_block. intros INJ.
    (* Slight variation on standard processing *)
    destruct (Genv.invert_symbol ge1 b) as [id |] eqn:SYM1; [| contradiction].
    assert (NONE: Genv.find_symbol ge1 id <> None). {
      apply Genv.invert_find_symbol in SYM1. congruence. }
    destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
    setoid_rewrite COMP in INJ.
    destruct (s cp) eqn:SIDE.
    + destruct (Genv.find_def ge1 b) as [gd |]; [| contradiction].
      destruct gd as [fd | gv]; [| contradiction].
      destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| contradiction].
      right. eauto.
    + destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| contradiction].
      apply Genv.invert_find_symbol in SYM1.
      setoid_rewrite (find_symbol_init_mem_compartment _ _ _ _ SYM1 MEM) in COMP.
      { simpl. rewrite COMP. left. assumption. }
  - simpl. unfold init_meminj, init_meminj_block. intros RIGHT INJ.
    destruct RIGHT as [RIGHT | [fd DEF]].
    (* Variation on standard processing *)
    + destruct (Genv.invert_symbol ge1 b) as [id |] eqn:SYM1.
      * assert (NONE: Genv.find_symbol ge1 id <> None). {
          apply Genv.invert_find_symbol in SYM1. congruence. }
        destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
        setoid_rewrite COMP in INJ.
        destruct (Mem.block_compartment m1 b) as [cp' |] eqn:COMP'; [| contradiction].
        apply Genv.invert_find_symbol in SYM1.
        assert (cp = cp') as <-. {
          setoid_rewrite (find_symbol_init_mem_compartment _ _ _ _ SYM1 MEM) in COMP.
          { setoid_rewrite COMP in COMP'. injection COMP' as <-. reflexivity. }
        }
        rewrite RIGHT in INJ.
        destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [discriminate |].
        assert (CONTRA := find_symbol_right _ _ NONE COMP RIGHT). contradiction.
      * destruct Mem.block_compartment as [cp |] eqn:COMP; [| contradiction].
        assert (NONE: Mem.block_compartment m1 b <> None) by congruence.
        exploit init_mem_invert_symbol; eauto.
        exploit match_prog_unique1; eauto.
    + (* Initially very similar to the right case, can reuse *)
      destruct (Genv.invert_symbol ge1 b) as [id |] eqn:SYM1.
      * assert (NONE: Genv.find_symbol ge1 id <> None). {
          apply Genv.invert_find_symbol in SYM1. congruence. }
        destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
        setoid_rewrite COMP in INJ.
        destruct (s cp) eqn:SIDE.
        -- simpl in INJ. rewrite DEF in INJ.
           destruct (Genv.find_symbol (Genv.globalenv W2) id) as [b' |] eqn:SYM2;
             setoid_rewrite SYM2 in INJ; [discriminate |].
           admit.
        -- destruct (Genv.find_symbol ge2 id) eqn:SYM2; [discriminate |].
           admit.
      * admit.
(* Qed. *)
Admitted.

Lemma delta_zero_init_meminj:
  Mem.delta_zero init_meminj.
Proof.
  unfold init_meminj. intros loc loc' delta INJ.
  destruct init_meminj_block; [| discriminate].
  injection INJ as <- <-.
  reflexivity.
Qed.

(* These characterizations need to be a bit more general to be
   independent of init_meminj in particular *)
Lemma init_mem_characterization_rel sp (pr1 pr2: program) id gd m1 m2 b1 b2
    (MATCH: match_prog sp pr1 pr2)
    (PROGDEFS1: In (id, gd) (prog_defs pr1))
    (PROGDEFS2: In (id, gd) (prog_defs pr2))
    (MEM1: Genv.init_mem pr1 = Some m1)
    (MEM2: Genv.init_mem pr2 = Some m2)
    (SYM1: Genv.find_symbol (globalenv pr1) id = Some b1)
    (SYM2: Genv.find_symbol (globalenv pr2) id = Some b2)
    (DEF1: Genv.find_def (globalenv pr1) b1 = Some gd)
    (DEF2: Genv.find_def (globalenv pr2) b2 = Some gd):
  (forall ofs k p, Mem.perm m1 b1 ofs k p <-> Mem.perm m2 b2 ofs k p) /\
  (forall cp, Mem.can_access_block m1 b1 cp <-> Mem.can_access_block m2 b2 cp) /\
  (* Any restrictions on gvar_init and init_data, esp. Init_addrof? *)
  (forall ofs, Mem.perm m1 b1 ofs Cur Readable ->
               memval_inject init_meminj (ZMap.get ofs (Mem.mem_contents m1) !! b1)
                                         (ZMap.get ofs (Mem.mem_contents m2) !! b2)).
Proof.
  (* From PROGDEFS and MEM we can get SYM and DEF, although without
     these there is no explicit link between blocks *)
  change (In _ _)
    with (In (id, gd) (AST.prog_defs (program_of_program pr1)))
    in PROGDEFS1.
  change (In _ _)
    with (In (id, gd) (AST.prog_defs (program_of_program pr2)))
    in PROGDEFS2.
  destruct (Genv.find_symbol_exists _ _ _ PROGDEFS1) as (b1' & SYM1').
  destruct (Genv.find_symbol_exists _ _ _ PROGDEFS2) as (b2' & SYM2').
  setoid_rewrite SYM1 in SYM1'. injection SYM1' as <-.
  setoid_rewrite SYM2 in SYM2'. injection SYM2' as <-.
  assert (DEFMAP1 := prog_defmap_norepet _ _ _ (match_prog_unique1 _ _ _ MATCH) PROGDEFS1).
  assert (DEFMAP2 := prog_defmap_norepet _ _ _ (match_prog_unique2 _ _ _ MATCH) PROGDEFS2).
  apply Genv.find_def_symbol in DEFMAP1 as (b1' & SYM1' & DEF1').
  apply Genv.find_def_symbol in DEFMAP2 as (b2' & SYM2' & DEF2').
  setoid_rewrite SYM1 in SYM1'. injection SYM1' as <-.
  setoid_rewrite SYM2 in SYM2'. injection SYM2' as <-.
  clear DEF1' DEF2'.
  (* So those four we can get, but we need to tie id and gd to b1, b2 *)
Abort.

Lemma init_mem_characterization_rel id gd m1 m2 b1 b2
      (* (MATCH: match_prog sp pr1 pr2) *)
      (* (VAR1: wf_gvar_init ge1) *)
      (* (VAR2: wf_gvar_init ge2) *)
      (* (PROGDEFS1: In (id, gd) (prog_defs pr1)) *)
      (* (PROGDEFS2: In (id, gd) (prog_defs pr2)) *)
      (MEM1: Genv.init_mem W1 = Some m1)
      (MEM2: Genv.init_mem W2 = Some m2)
      (SYM1: Genv.find_symbol ge1 id = Some b1)
      (SYM2: Genv.find_symbol ge2 id = Some b2)
      (b1_b2: init_meminj b1 = Some (b2, 0))
      (DEF1: Genv.find_def ge1 b1 = Some gd)
      (DEF2: Genv.find_def ge2 b2 = Some gd):
  (forall ofs k p, Mem.perm m1 b1 ofs k p <-> Mem.perm m2 b2 ofs k p) /\
  (forall cp, Mem.can_access_block m1 b1 cp <-> Mem.can_access_block m2 b2 cp) /\
  (* Any restrictions on gvar_init and init_data, esp. Init_addrof? *)
  (forall ofs, Mem.perm m1 b1 ofs Cur Readable ->
               memval_inject init_meminj (ZMap.get ofs (Mem.mem_contents m1) !! b1)
                                         (ZMap.get ofs (Mem.mem_contents m2) !! b2)).
Proof.
  destruct gd as [fd | gv].
  - apply Genv.find_funct_ptr_iff in DEF1, DEF2.
    destruct (Genv.init_mem_characterization_2' _ _ DEF1 MEM1) as (PERM1 & ACC1 & INJ1).
    destruct (Genv.init_mem_characterization_2' _ _ DEF2 MEM2) as (PERM2 & ACC2 & INJ2).
    split; [| split].
    + intros ofs k p. specialize (PERM1 ofs k). specialize (PERM2 ofs k).
      unfold Mem.perm. rewrite PERM1, PERM2.
      reflexivity.
    + intros [cp |]; [| reflexivity].
      unfold Mem.can_access_block, Mem.block_compartment.
      rewrite ACC1, ACC2.
      reflexivity.
    + intros ofs PERM. specialize (INJ1 ofs). specialize (INJ2 ofs).
      rewrite INJ1, INJ2.
      exact (memval_inject_undef _ _).
  - apply Genv.find_var_info_iff in DEF1, DEF2.
    destruct (Genv.init_mem_characterization' _ _ DEF1 MEM1) as (PERM1 & ACC1 & INJ1).
    destruct (Genv.init_mem_characterization' _ _ DEF2 MEM2) as (PERM2 & ACC2 & INJ2).
    split; [| split].
    + intros ofs k p. specialize (PERM1 ofs k). specialize (PERM2 ofs k).
      unfold Mem.perm. rewrite PERM1, PERM2.
      reflexivity.
    + intros [cp |]; [| reflexivity].
      unfold Mem.can_access_block, Mem.block_compartment.
      rewrite ACC1, ACC2.
      reflexivity.
    + intros ofs PERM.
      unfold Mem.perm, Mem.perm_order' in PERM.
      destruct ((Mem.mem_access m1) !! b1 ofs Cur) as [p' |] eqn:ACC;
        [| contradiction].
      assert (PERMEQ: (if zle 0 ofs && zlt ofs (init_data_list_size (gvar_init gv))
                       then Some (Genv.perm_globvar gv) else None) = Some p'). {
        rewrite <- ACC. erewrite <- PERM1. reflexivity. }
      destruct (zle 0 ofs && zlt ofs (init_data_list_size (gvar_init gv))) eqn:RANGE;
        [| discriminate].
      injection PERMEQ as <-.
      unfold Genv.perm_globvar in PERM.
      destruct (gvar_volatile gv) eqn:VOL; [now inversion PERM |].
      (* in the process of proving this, we can replicate the use of
         [Mem.loadbytes_inj] with a modified proof that exploits facts
         we know from our specific context *)
      assert (MEMVAL: list_forall2 (memval_inject init_meminj)
                        (Genv.bytes_of_init_data_list ge1 (gvar_init gv))
                        (Genv.bytes_of_init_data_list ge2 (gvar_init gv))). {
Local Transparent Mem.loadbytes.
  unfold Mem.loadbytes in *.
Local Opaque Mem.loadbytes.
  destruct (Mem.range_perm_dec m1 b1 0 (0 + init_data_list_size (gvar_init gv)) Cur Readable) as [RANGE1 |];
  destruct (Mem.can_access_block_dec m1 b1 (Some (gvar_comp gv))) as [BLOCK1 |];
  inv INJ1.
  (* same thing for the second memory now, replacing the use of
     [Mem.range_perm_inj] and [Mem.mi_own] *)
  destruct (Mem.range_perm_dec m2 b2 0 (0 + init_data_list_size (gvar_init gv)) Cur Readable) as [RANGE2 |];
  destruct (Mem.can_access_block_dec m2 b2 (Some (gvar_comp gv))) as [BLOCK2 |];
  inv INJ2.
  (* (* we can use the first sub-characterization above *)
  (*    replacing the use of [Mem.range_perm_inj] *) *)
  (* assert (CHAR: *)
  (*          (forall ofs k p, Mem.perm m1 b1 ofs k p <-> Mem.perm m2 b2 ofs k p) -> *)
  (*          (forall lo hi k p, Mem.range_perm m1 b1 lo hi k p <-> Mem.range_perm m2 b2 lo hi k p)). { *)
  (*   unfold Mem.range_perm. split; intros. *)
  (*   - specialize (H ofs0 k p). apply H; auto. *)
  (*   - specialize (H ofs0 k p). apply H; auto. } *)
  (* assert (RANGE2: Mem.range_perm m2 b2 0 (0 + init_data_list_size (gvar_init gv)) Cur Readable) by admit. *)
  (* (* and the second sub-characterization in turn *)
  (*    replacing the use of [Mem.mi_own] *) *)
  (* assert (BLOCK2: Mem.can_access_block m2 b2 (Some (gvar_comp gv))) by admit. *)
  assert (MEMVAL: list_forall2 (memval_inject init_meminj)
                    (Mem.getN (Z.to_nat (init_data_list_size (gvar_init gv))) 0 (m1.(Mem.mem_contents) !! b1))
                    (Mem.getN (Z.to_nat (init_data_list_size (gvar_init gv))) 0 (m2.(Mem.mem_contents) !! b2))). {
    (* replicate the use of [Mem.getN_inj] *)
    rewrite H0, H1.
    specialize (W1_gvars gv b1 DEF1). specialize (W2_gvars gv b2 DEF2).
    assert (RIGHT: s (comp_of gv) = Right). {
      clear -W1_gvars SYM1 DEF1 b1_b2.
      unfold init_meminj, init_meminj_block in b1_b2.
      apply Genv.find_invert_symbol in SYM1. rewrite SYM1 in b1_b2.
      unfold Genv.find_comp_of_ident in b1_b2.
      apply Genv.invert_find_symbol in SYM1. rewrite SYM1 in b1_b2.
      unfold Genv.find_comp_of_block in b1_b2.
      apply Genv.find_var_info_iff in DEF1. rewrite DEF1 in b1_b2.
      destruct (s (comp_of (Gvar gv))) eqn:RIGHT; [discriminate |].
      exact RIGHT. }
    remember (gvar_init gv) as il eqn:INIT. clear -W1_gvars W2_gvars RIGHT.
    induction il as [| i il IHil].
    - constructor.
    - simpl.
      apply list_forall2_app.
      + destruct i; simpl;
          try (now apply inj_bytes_inject).
        * remember (Z.to_nat z) as n eqn:ZtoN. clear ZtoN.
          { clear.
            induction n as [| n IHn]. (* Lemma *)
            - constructor.
            - constructor.
              + constructor.
              + apply IHn. }
        * inv W1_gvars. inv W2_gvars.
          specialize (IHil H2 H4). clear H2 H4.
          specialize (H1 _ _ eq_refl). specialize (H3 _ _ eq_refl).
          unfold Genv.find_comp_of_ident in H1, H3.
          destruct (Genv.find_symbol ge1 i) as [b1' |] eqn:SYM1';
            destruct (Genv.find_symbol ge2 i) as [b2' |] eqn:SYM2';
            try congruence.
          setoid_rewrite SYM1'. setoid_rewrite SYM2'.
          apply inj_value_inject. econstructor.
          -- unfold init_meminj, init_meminj_block.
             erewrite Genv.find_invert_symbol; eauto.
             unfold Genv.find_comp_of_ident.
             rewrite SYM1', H1, RIGHT, SYM2'. reflexivity.
          -- rewrite Ptrofs.add_zero. reflexivity.
      + inv W1_gvars. inv W2_gvars.
        eapply IHil; eauto. }
  destruct (zle 0 (init_data_list_size (gvar_init gv))) as [LE | GT].
  - rewrite H0, H1 in MEMVAL. exact MEMVAL.
  - assert (CONTRA := init_data_list_size_pos (gvar_init gv)). lia.
      }
      clear -INJ1 INJ2 MEMVAL RANGE.
      unfold zle, zlt in RANGE.
      destruct Z_le_gt_dec; [| discriminate].
      destruct Z_lt_dec; [| discriminate].
      apply Mem_getN_forall2
        with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init gv)));
        try lia.
Local Transparent Mem.loadbytes.
      unfold Mem.loadbytes in *.
Local Opaque Mem.loadbytes.
      destruct andb in INJ1; [| discriminate].
      destruct andb in INJ2; [| discriminate].
      injection INJ1 as INJ1.
      injection INJ2 as INJ2.
      rewrite INJ1, INJ2.
      exact MEMVAL.
Qed.

Definition globdef_blocks p1 p2 '(id, gd) b1 b2 :=
  Genv.find_symbol (globalenv p1) id = Some b1 /\
  Genv.find_symbol (globalenv p2) id = Some b2 /\
  Genv.find_def (globalenv p1) b1 = Some gd /\
  Genv.find_def (globalenv p2) b2 = Some gd.

Lemma globdef_right id gd1 gd2 b1 b2 cp
      (COMP : Genv.find_comp_of_ident (Genv.globalenv W1) id = Some cp)
      (SIDE : s cp = Right)
      (SYM1 : Genv.find_symbol ge1 id = Some b1)
      (SYM2 : Genv.find_symbol ge2 id = Some b2)
      (DEF1 : Genv.find_def (Genv.globalenv W1) b1 = Some gd1)
      (DEF2 : Genv.find_def (Genv.globalenv W2) b2 = Some gd2):
  gd1 = gd2.
Proof.
  destruct (match_prog_globdefs _ _ _ match_W1_W2
              _ _ (or_introl COMP) (or_introl SIDE))
    as (b1' & b2' & SYM1' & SYM2' & GLOBDEFS).
  (* unfold globalenv, Genv.globalenv in *. simpl in *. *)
  rewrite SYM1 in SYM1'. injection SYM1' as <-.
  rewrite SYM2 in SYM2'. injection SYM2' as <-.
  rewrite SIDE in GLOBDEFS. simpl in GLOBDEFS.
  setoid_rewrite DEF1 in GLOBDEFS. setoid_rewrite DEF2 in GLOBDEFS.
  injection GLOBDEFS as <-. reflexivity.
Qed.

Lemma init_mem_characterization_rel' sp (pr1 pr2: program) id gd m1 m2
      (MATCH: match_prog sp pr1 pr2)
      (PROGDEFS1: In (id, gd) (prog_defs pr1))
      (PROGDEFS2: In (id, gd) (prog_defs pr2))
      (MEM1: Genv.init_mem pr1 = Some m1)
      (MEM2: Genv.init_mem pr2 = Some m2):
  (forall b1 b2 ofs k p,
     globdef_blocks pr1 pr2 (id, gd) b1 b2 ->
     Mem.perm m1 b1 ofs k p <-> Mem.perm m2 b2 ofs k p) /\
  (forall b1 b2 cp,
     globdef_blocks pr1 pr2 (id, gd) b1 b2 ->
     Mem.can_access_block m1 b1 cp <-> Mem.can_access_block m2 b2 cp) /\
  (* Any restrictions on gvar_init and init_data, esp. Init_addrof? *)
  (forall b1 b2 ofs,
     globdef_blocks pr1 pr2 (id, gd) b1 b2 ->
     Mem.perm m1 b1 ofs Cur Readable ->
     memval_inject init_meminj (ZMap.get ofs (Mem.mem_contents m1) !! b1)
                               (ZMap.get ofs (Mem.mem_contents m2) !! b2)).
Abort.

(* TODO: relocate *)
Lemma global_addresses_distinct_id
      {F V} (ge : Genv.t F V) (id1 id2 : ident) (b1 b2 : block):
  b1 <> b2 ->
  Genv.find_symbol ge id1 = Some b1 ->
  Genv.find_symbol ge id2 = Some b2 ->
  id1 <> id2.
Proof.
  clear. (* remove later *)
  intros b1_b2 SYM1 SYM2 <-.
  rewrite SYM1 in SYM2.
  injection SYM2 as <-.
  contradiction.
Qed.

(* Genv.initmem_inject *)
Lemma inject_init_meminj m1 m2
      (MEM1: Genv.init_mem W1 = Some m1)
      (MEM2: Genv.init_mem W2 = Some m2):
  Mem.inject init_meminj m1 m2.
Proof.
  constructor.
  - constructor.
    + unfold init_meminj, init_meminj_block.
      intros b1 b2 delta ofs k p INJ PERM.
      destruct (Genv.invert_symbol ge1 b1) as [id |] eqn:SYM1; [| discriminate].
      assert (NONE: Genv.find_symbol ge1 id <> None). {
        apply Genv.invert_find_symbol in SYM1. congruence. }
      destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
      setoid_rewrite COMP in INJ.
      destruct (s cp) eqn:SIDE.
      * apply Genv.invert_find_symbol in SYM1.
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
        setoid_rewrite DEF1 in INJ.
        destruct gd1 as [fd1 |]; [| discriminate].
        destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
        injection INJ as -> <-.
        (* Post standard processing *)
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
        assert (Gfun fd1 = gd2) as <- by admit. (* TODO: need globdef_left *)
        rename fd1 into fd.
        assert (INJ: init_meminj b1 = Some (b2, 0)). { (* inversion lemma? *)
          unfold init_meminj, init_meminj_block.
          apply Genv.find_invert_symbol in SYM1. rewrite SYM1.
          setoid_rewrite COMP.
          rewrite SIDE. rewrite SYM2. setoid_rewrite DEF1. reflexivity. }
        destruct (init_mem_characterization_rel
                    _ _ _ _ _ _
                    MEM1 MEM2 SYM1 SYM2 INJ DEF1 DEF2)
          as (PERMS & _).
        apply PERMS. rewrite Z.add_0_r. assumption.
      * destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
        injection INJ as -> <-.
        (* Post standard processing *)
        (* apply Genv.invert_find_symbol in SYM2. *)
        apply Genv.invert_find_symbol in SYM1.
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
        assert (gd1 = gd2) as <- by (eapply globdef_right; eassumption).
        rename gd1 into gd.
        assert (INJ: init_meminj b1 = Some (b2, 0)). { (* inversion lemma? *)
          unfold init_meminj, init_meminj_block.
          apply Genv.find_invert_symbol in SYM1. rewrite SYM1.
          setoid_rewrite COMP.
          rewrite SIDE. rewrite SYM2. reflexivity. }
        destruct (init_mem_characterization_rel
                    _ _ _ _ _ _
                    MEM1 MEM2 SYM1 SYM2 INJ DEF1 DEF2)
          as (PERMS & _).
        apply PERMS. rewrite Z.add_0_r. assumption.
    + unfold init_meminj, init_meminj_block.
      intros b1 b2 delta cp INJ BLOCK.
      destruct (Genv.invert_symbol ge1 b1) as [id |] eqn:SYM1; [| discriminate].
      assert (NONE: Genv.find_symbol ge1 id <> None). {
        apply Genv.invert_find_symbol in SYM1. congruence. }
      destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp' & COMP).
      setoid_rewrite COMP in INJ.
      destruct (s cp') eqn:SIDE.
      * (* Extended standard processing - very similar to Right case *)
        apply Genv.invert_find_symbol in SYM1.
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
        setoid_rewrite DEF1 in INJ.
        destruct gd1 as [fd1 |]; [| discriminate].
        destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
        injection INJ as -> <-.
        (* Post standard processing *)
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
        assert (Gfun fd1 = gd2) as <- by admit.
        rename fd1 into fd.
        assert (INJ: init_meminj b1 = Some (b2, 0)). { (* inversion lemma? *)
          unfold init_meminj, init_meminj_block.
          apply Genv.find_invert_symbol in SYM1. rewrite SYM1.
          setoid_rewrite COMP.
          rewrite SIDE. rewrite SYM2. setoid_rewrite DEF1. reflexivity. }
        destruct (init_mem_characterization_rel
                    _ _ _ _ _ _
                    MEM1 MEM2 SYM1 SYM2 INJ DEF1 DEF2)
          as (_ & BLOCKS & _).
        apply BLOCKS. assumption.
      * destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
        injection INJ as -> <-.
        (* Post standard processing *)
        apply Genv.invert_find_symbol in SYM1.
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
        assert (gd1 = gd2) as <- by (eapply globdef_right; eassumption).
        rename gd1 into gd.
        assert (INJ: init_meminj b1 = Some (b2, 0)). { (* inversion lemma? *)
          unfold init_meminj, init_meminj_block.
          apply Genv.find_invert_symbol in SYM1. rewrite SYM1.
          setoid_rewrite COMP.
          rewrite SIDE. rewrite SYM2. reflexivity. }
        destruct (init_mem_characterization_rel
                    _ _ _ _ _ _
                    MEM1 MEM2 SYM1 SYM2 INJ DEF1 DEF2)
          as (_ & BLOCKS & _).
        apply BLOCKS. assumption.
    + unfold init_meminj, init_meminj_block.
      intros b1 b2 delta chunk ofs p INJ RANGE.
      destruct (Genv.invert_symbol ge1 b1) as [id |] eqn:SYM1; [| discriminate].
      assert (NONE: Genv.find_symbol ge1 id <> None). {
        apply Genv.invert_find_symbol in SYM1. congruence. }
      destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
      setoid_rewrite COMP in INJ.
      destruct (s cp) eqn:SIDE.
      * (* Extended standard processing - very similar to Right case *)
        apply Genv.invert_find_symbol in SYM1.
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
        setoid_rewrite DEF1 in INJ.
        destruct gd1 as [fd1 |]; [| discriminate].
        destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
        injection INJ as -> <-.
        apply Z.divide_0_r.
      * destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
        injection INJ as -> <-.
        (* Post standard processing *)
        apply Z.divide_0_r.
    + unfold init_meminj, init_meminj_block.
      intros b1 ofs b2 delta INJ PERM.
      destruct (Genv.invert_symbol ge1 b1) as [id |] eqn:SYM1; [| discriminate].
      assert (NONE: Genv.find_symbol ge1 id <> None). {
        apply Genv.invert_find_symbol in SYM1. congruence. }
      destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
      setoid_rewrite COMP in INJ.
      destruct (s cp) eqn:SIDE.
      * (* Extended standard processing - very similar to Right case *)
        apply Genv.invert_find_symbol in SYM1.
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
        setoid_rewrite DEF1 in INJ.
        destruct gd1 as [fd1 |]; [| discriminate].
        destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
        injection INJ as -> <-.
        (* Post standard processing *)
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
        assert (Gfun fd1 = gd2) as <- by admit.
        rename fd1 into fd.
        assert (INJ: init_meminj b1 = Some (b2, 0)). { (* inversion lemma? *)
          unfold init_meminj, init_meminj_block.
          apply Genv.find_invert_symbol in SYM1. rewrite SYM1.
          setoid_rewrite COMP.
          rewrite SIDE. rewrite SYM2. setoid_rewrite DEF1. reflexivity. }
        destruct (init_mem_characterization_rel
                    _ _ _ _ _ _
                    MEM1 MEM2 SYM1 SYM2 INJ DEF1 DEF2)
          as (_ & _ & MEMVAL).
        rewrite Z.add_0_r. exact (MEMVAL ofs PERM).
      * destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
        injection INJ as -> <-.
        (* Post standard processing *)
        apply Genv.invert_find_symbol in SYM1.
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
        destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
        assert (gd1 = gd2) as <- by (eapply globdef_right; eassumption).
        rename gd1 into gd.
        assert (INJ: init_meminj b1 = Some (b2, 0)). { (* inversion lemma? *)
          unfold init_meminj, init_meminj_block.
          apply Genv.find_invert_symbol in SYM1. rewrite SYM1.
          setoid_rewrite COMP.
          rewrite SIDE. rewrite SYM2. reflexivity. }
        destruct (init_mem_characterization_rel
                    _ _ _ _ _ _
                    MEM1 MEM2 SYM1 SYM2 INJ DEF1 DEF2)
          as (_ & _ & MEMVAL).
        rewrite Z.add_0_r. exact (MEMVAL ofs PERM).
  - intros b VALID. unfold init_meminj, init_meminj_block.
    destruct Genv.invert_symbol as [id |] eqn:SYM; [| reflexivity].
    apply Genv.invert_find_symbol in SYM.
    assert (CONTRA := Genv.find_symbol_not_fresh _ _ MEM1 SYM).
    contradiction.
  - unfold init_meminj, init_meminj_block. intros b b' delta INJ.
    destruct (Genv.invert_symbol ge1 b) as [id |] eqn:SYM1; [| discriminate].
    assert (NONE: Genv.find_symbol ge1 id <> None). {
      apply Genv.invert_find_symbol in SYM1. congruence. }
    destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
    setoid_rewrite COMP in INJ.
    destruct (s cp) eqn:SIDE.
    + (* Extended standard processing - very similar to Right case *)
      apply Genv.invert_find_symbol in SYM1.
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
      setoid_rewrite DEF1 in INJ.
      destruct gd1 as [fd1 |]; [| discriminate].
      destruct (Genv.find_symbol ge2 id) as [b'' |] eqn:SYM2; [| discriminate].
      injection INJ as -> <-.
      exact (Genv.find_symbol_not_fresh _ _ MEM2 SYM2).
    + destruct (Genv.find_symbol ge2 id) as [b'' |] eqn:SYM2; [| discriminate].
      injection INJ as -> <-.
      exact (Genv.find_symbol_not_fresh _ _ MEM2 SYM2).
  - intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 INJ1 INJ2 PERM1 PERM2.
    left. intros <-. apply b1_b2.
    unfold init_meminj, init_meminj_block in INJ1, INJ2.
    destruct (Genv.invert_symbol ge1 b1) as [id1|] eqn:ge1_b1; try easy.
    destruct (Genv.invert_symbol ge1 b2) as [id2|] eqn:ge1_b2; try easy.
    destruct (Genv.find_comp_of_ident ge1 id1) as [cp1|] eqn:id1_cp1; try easy.
    destruct (Genv.find_comp_of_ident ge1 id2) as [cp2|] eqn:id2_cp2; try easy.
    destruct (s cp1).
    + apply Genv.invert_find_symbol in ge1_b1.
      destruct (Genv.find_symbol_find_def_inversion _ _ ge1_b1) as (gd1 & DEF1).
      setoid_rewrite DEF1 in INJ1.
      destruct gd1 as [fd1 |]; [| discriminate].
      destruct (Genv.find_symbol ge2 id1) as [b'|] eqn:ge2_id1; try easy.
      injection INJ1 as -> <-.
      (* Second injection *)
      apply Genv.invert_find_symbol in ge1_b2.
      destruct (Genv.find_symbol_find_def_inversion _ _ ge1_b2) as (gd2 & DEF2).
      setoid_rewrite DEF2 in INJ2.
      destruct (s cp2).
      * destruct (Genv.find_symbol ge2 id2) as [b'|] eqn:ge2_id2.
        -- destruct gd2 as [fd2 |]; [| discriminate].
           injection INJ2 as -> <-.
           assert (id1_id2 := global_addresses_distinct_id _ _ _ _ _ b1_b2 ge1_b1 ge1_b2).
           assert (b1'_b1' := Genv.global_addresses_distinct _ id1_id2 ge2_id1 ge2_id2).
           contradiction.
        -- destruct gd2 as [fd2 |]; discriminate.
      * destruct (Genv.find_symbol ge2 id2) as [b'|] eqn:ge2_id2; try easy.
        injection INJ2 as -> <-.
        apply Genv.find_invert_symbol in ge2_id1.
        apply Genv.find_invert_symbol in ge2_id2.
        assert (id2 = id1) as -> by congruence.
        congruence.
    + destruct (Genv.find_symbol ge2 id1) as [b2' |] eqn:ge2_id1; [| discriminate].
      injection INJ1 as -> <-.
      destruct (s cp2).
      * apply Genv.invert_find_symbol in ge1_b2.
        destruct (Genv.find_symbol_find_def_inversion _ _ ge1_b2) as (gd2 & DEF2).
        setoid_rewrite DEF2 in INJ2.
        destruct gd2 as [fd2 |]; [| discriminate].
        destruct (Genv.find_symbol ge2 id2) as [b2' |] eqn:ge2_id2; [| discriminate].
        injection INJ2 as -> <-.
        apply Genv.invert_find_symbol in ge1_b1.
        assert (id1_id2 := global_addresses_distinct_id _ _ _ _ _ b1_b2 ge1_b1 ge1_b2).
        assert (b1'_b1' := Genv.global_addresses_distinct _ id1_id2 ge2_id1 ge2_id2).
        contradiction.
  - unfold init_meminj, init_meminj_block.
    intros b1 b2 delta ofs INJ PERM.
    destruct (Genv.invert_symbol ge1 b1) as [id |] eqn:SYM1; [| discriminate].
    assert (NONE: Genv.find_symbol ge1 id <> None). {
      apply Genv.invert_find_symbol in SYM1. congruence. }
    destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
    setoid_rewrite COMP in INJ.
    destruct (s cp) eqn:SIDE.
    + apply Genv.invert_find_symbol in SYM1.
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
      setoid_rewrite DEF1 in INJ.
      destruct gd1 as [fd1 |]; [| discriminate].
      destruct (Genv.find_symbol ge2 id) as [b'' |] eqn:SYM2; [| discriminate].
      injection INJ as -> <-.
      (* Post standard processing *)
      split; [lia |]. rewrite Z.add_0_r. apply Ptrofs.unsigned_range_2.
    + destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
      injection INJ as -> <-.
      (* Post standard processing *)
      split; [lia |]. rewrite Z.add_0_r. apply Ptrofs.unsigned_range_2.
  - unfold init_meminj, init_meminj_block.
    intros b1 ofs b2 delta k p INJ PERM.
    destruct (Genv.invert_symbol ge1 b1) as [id |] eqn:SYM1; [| discriminate].
    assert (NONE: Genv.find_symbol ge1 id <> None). {
      apply Genv.invert_find_symbol in SYM1. congruence. }
    destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
    setoid_rewrite COMP in INJ.
    destruct (s cp) eqn:SIDE.
    + apply Genv.invert_find_symbol in SYM1.
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
      setoid_rewrite DEF1 in INJ.
      destruct gd1 as [fd1 |]; [| discriminate].
      destruct (Genv.find_symbol ge2 id) as [b'' |] eqn:SYM2; [| discriminate].
      injection INJ as -> <-.
      (* Post standard processing *)
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
      assert (Gfun fd1 = gd2) as <- by admit.
      rename fd1 into fd.
      assert (INJ: init_meminj b1 = Some (b2, 0)). { (* inversion lemma? *)
        unfold init_meminj, init_meminj_block.
        apply Genv.find_invert_symbol in SYM1. rewrite SYM1.
        setoid_rewrite COMP.
        rewrite SIDE. rewrite SYM2. setoid_rewrite DEF1. reflexivity. }
      destruct (init_mem_characterization_rel
                  _ _ _ _ _ _
                  MEM1 MEM2 SYM1 SYM2 INJ DEF1 DEF2)
        as (PERMS & _).
      left. apply PERMS. rewrite Z.add_0_r in PERM. assumption.
    + destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
      injection INJ as -> <-.
      (* Post standard processing *)
      apply Genv.invert_find_symbol in SYM1.
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
      assert (gd1 = gd2) as <- by (eapply globdef_right; eassumption).
      rename gd1 into gd.
      assert (INJ: init_meminj b1 = Some (b2, 0)). { (* inversion lemma? *)
        unfold init_meminj, init_meminj_block.
        apply Genv.find_invert_symbol in SYM1. rewrite SYM1.
        setoid_rewrite COMP.
        rewrite SIDE. rewrite SYM2. reflexivity. }
      destruct (init_mem_characterization_rel
                  _ _ _ _ _ _
                  MEM1 MEM2 SYM1 SYM2 INJ DEF1 DEF2)
        as (PERMS & _).
      left. apply PERMS. rewrite Z.add_0_r in PERM. assumption.
(* Qed. *)
Admitted.

Lemma symbols_inject_init_meminj cp'
  (RIGHT': s cp' = Right):
  symbols_inject init_meminj ge1 ge2 (Genv.find_comp_of_ident ge1) cp'.
Proof.
  split; [| split; [| split]].
  - intros id. simpl.
    rewrite public_symbol_preserved. reflexivity.
  - intros id b1 b2 ofs b1_b2 SYM1.
    unfold init_meminj, init_meminj_block in b1_b2.
    (* Slightly modified standard processing *)
    apply Genv.find_invert_symbol in SYM1. rewrite SYM1 in b1_b2.
    assert (NONE: Genv.find_symbol ge1 id <> None). {
      apply Genv.invert_find_symbol in SYM1. congruence. }
    destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
    setoid_rewrite COMP in b1_b2.
    destruct (s cp) eqn:SIDE.
    + apply Genv.invert_find_symbol in SYM1.
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
      setoid_rewrite DEF1 in b1_b2.
      destruct gd1 as [fd1 |]; [| discriminate].
      destruct (Genv.find_symbol ge2 id) as [b'' |] eqn:SYM2; [| discriminate].
      injection b1_b2 as -> <-.
      (* Done *)
      auto.
    + destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
      injection b1_b2 as -> <-.
      (* Done *)
      auto.
  - intros id b1 FIND PUB SYM1.
    assert (exists b2, Genv.find_symbol ge2 id = Some b2)
      as (b2 & SYM2). {
      assert (NONE1: Senv.find_symbol ge1 id <> None) by congruence.
      assert (NONE2 := find_symbol_right _ _ NONE1 FIND RIGHT').
      assert (exists b2, Genv.find_symbol ge2 id = Some b2)
        as (b2 & SYM2)
        by (destruct (Genv.find_symbol ge2 id) as [b |]; [now eauto | contradiction]).
      eauto. }
    unfold init_meminj, init_meminj_block.
    apply Genv.find_invert_symbol in SYM1.
    rewrite SYM1, FIND, RIGHT', SYM2.
    eauto.
  - intros b1 b2 ofs b1_b2.
    unfold init_meminj, init_meminj_block in b1_b2.
    (* Slightly modified standard processing *)
    destruct (Genv.invert_symbol ge1 b1) as [id |] eqn:SYM1; [| discriminate].
    assert (NONE: Genv.find_symbol ge1 id <> None). {
      apply Genv.invert_find_symbol in SYM1. congruence. }
    destruct (Genv.find_symbol_find_comp _ _ NONE) as (cp & COMP).
    setoid_rewrite COMP in b1_b2.
    destruct (s cp) eqn:SIDE.
    + apply Genv.invert_find_symbol in SYM1.
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
      setoid_rewrite DEF1 in b1_b2.
      destruct gd1 as [fd1 |]; [| discriminate].
      destruct (Genv.find_symbol ge2 id) as [b'' |] eqn:SYM2; [| discriminate].
      injection b1_b2 as -> <-.
      (* Continue *)
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
      (* TODO: Needs globdef_left as well *)
      admit.
    + destruct (Genv.find_symbol ge2 id) as [b' |] eqn:SYM2; [| discriminate].
      injection b1_b2 as -> <-.
      (* Continue *)
      apply Genv.invert_find_symbol in SYM1.
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM1) as (gd1 & DEF1).
      destruct (Genv.find_symbol_find_def_inversion _ _ SYM2) as (gd2 & DEF2).
      destruct (globdef_right _ _ _ _ _ _ COMP SIDE SYM1 SYM2 DEF1 DEF2).
      simpl. unfold Genv.block_is_volatile, Genv.find_var_info.
      setoid_rewrite DEF1. setoid_rewrite DEF2. reflexivity.
(* Qed. *)
Admitted.

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
  - apply symbols_inject_init_meminj.
  - apply init_mem_same_blocks; assumption.
  - apply init_mem_same_blocks; assumption.
Qed.

(* - Related to old [partialize_partition]
   - We may want to be more explicit about the initial injection *)
Lemma initial_state_injection s1 s2 :
  Smallstep.initial_state (semantics1 W1) s1 ->
  Smallstep.initial_state (semantics1 W2) s2 ->
  exists j,
    right_state_injection s j ge1 ge2 s1 s2.
Proof.
  intros [b1 main1 m1 ge1 MEM1 MAINSYM1 MAINBLOCK1 MAINTYPE1]
         [b2 main2 m2 ge2 MEM2 MAINSYM2 MAINBLOCK2 MAINTYPE2].
  exists init_meminj.
  assert (RMEMINJ := initial_mem_injection _ _ MEM1 MEM2).
  (* assert (exists j, *)
  (*           right_mem_injection s j Simulation.ge1 Simulation.ge2 m1 m2) *)
  (*   as (j & RMEMINJ). { *)
  (*   clear s1 s2 b1 b2 main1 main2 *)
  (*         MAINSYM1 MAINSYM2 MAINBLOCK1 MAINBLOCK2 MAINTYPE1 MAINTYPE2. *)
  (*   admit. } *)
  assert (RCONTINJ: right_cont_injection s init_meminj Kstop Kstop) by constructor.
  assert (VALINJ: Val.inject_list init_meminj nil nil) by constructor.
  rewrite (match_prog_main _ _ _ match_W1_W2) in MAINSYM2.
  assert (MAINSYM1': Genv.find_symbol ge1 (prog_main W1) <> None) by congruence.
  assert (COMP1 := Genv.find_funct_ptr_find_comp_of_block _ _ MAINBLOCK1).
  assert (COMP1': Genv.find_comp_of_ident ge1 (prog_main W1) =
                  Some (comp_of main1)). {
    unfold Genv.find_comp_of_ident. rewrite MAINSYM1. assumption. }
  exploit (@match_prog_globdefs _ _ _ match_W1_W2 (prog_main W1) (comp_of main1)); eauto.
  { right. left.
    unfold Genv.public_symbol. simpl.
    unfold ge1 in MAINSYM1. setoid_rewrite MAINSYM1.
    destruct in_dec as [IN | NOTIN]; [reflexivity |].
    exfalso. apply NOTIN. setoid_rewrite (Genv.globalenv_public W1).
    exact (main_is_public W1). }
  intros (b1' & b2' & MAINSYM1'' & MAINSYM2'' & MATCHDEFS).
  unfold Simulation.ge1 in MAINSYM1''. unfold ge1 in MAINSYM1.
  setoid_rewrite MAINSYM1 in MAINSYM1''.
  injection MAINSYM1'' as <-.
  unfold Simulation.ge2 in MAINSYM2''. unfold ge2 in MAINSYM2.
  setoid_rewrite MAINSYM2 in MAINSYM2''.
  injection MAINSYM2'' as <-.
  unfold match_opt_globdefs in MATCHDEFS. destruct (s (comp_of main1)) eqn:SIDE.
  - assert (COMP2: comp_of main1 = comp_of main2). {
      apply Genv.find_funct_ptr_iff in MAINBLOCK1, MAINBLOCK2.
      unfold Simulation.ge1 in MATCHDEFS. simpl in MATCHDEFS.
      unfold ge1 in MAINBLOCK1. unfold ge2 in MAINBLOCK2.
      setoid_rewrite MAINBLOCK1 in MATCHDEFS.
      setoid_rewrite MAINBLOCK2 in MATCHDEFS.
      inversion MATCHDEFS as [| f1 f2 MATCHGLOBS EQ1 EQ2];
        subst f1 f2; clear MATCHDEFS.
      inversion MATCHGLOBS as [f1 f2 MATCHDEFS EQ1 EQ2 |];
        subst f1 f2; clear MATCHGLOBS.
      inversion MATCHDEFS; reflexivity. }
    apply LeftControl; try easy.
    simpl. setoid_rewrite <- COMP2. assumption.
  - apply Genv.find_funct_ptr_iff in MAINBLOCK1, MAINBLOCK2.
    simpl in MATCHDEFS. unfold ge2 in MAINBLOCK2.
    setoid_rewrite <- MATCHDEFS in MAINBLOCK2.
    unfold ge1 in MAINBLOCK1. setoid_rewrite MAINBLOCK1 in MAINBLOCK2.
    injection MAINBLOCK2 as <-.
    apply RightControl; try assumption.
    constructor; assumption.
Qed.

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

End Simulation.
