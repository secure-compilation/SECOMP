Require Import String.
Require Import Coqlib Maps Errors Integers.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.

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

  Definition same_domain (ge1 ge2: genv) (m1 m2: mem) :=
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

  Record right_mem_injection (ge1 ge2: genv) (m1 m2: mem) : Prop :=
    { same_dom: same_domain ge1 ge2 m1 m2;
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
    s |= f2 ∈ Left ->
    right_cont_injection (remove_until_right k1) (remove_until_right k2) ->
    right_cont_injection (Kcall id1 f1 en1 le1 k1) (Kcall id2 f2 en2 le2 k2)
(* TODO: is it correct to add [right_cont_injection_kcall_right]? *)
| right_cont_injection_kcall_right: forall id1 id2 f1 f2 en1 en2 le1 le2 k1 k2,
    s |= f1 ∈ Right ->
    s |= f2 ∈ Right ->
    right_cont_injection k1 k2 ->
    right_cont_injection (Kcall id1 f1 en1 le1 k1) (Kcall id2 f2 en2 le2 k2)
.

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
    right_cont_injection (cont_of st1) (cont_of st2) ->

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

  (* Context (ge1 ge2: genv). *)
  Notation ge1 := (globalenv W1).
  Notation ge2 := (globalenv W2).
(*
  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol ge2 s = Genv.find_symbol ge1 s.
  Proof (Genv.find_symbol_match match_W1_W2).
*)

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
      assert (exists id, Genv.find_symbol ge1 id = Some b1) as (id & ge1_id).
      { unfold Genv.find_comp_of_block in ge1_b1.
        destruct (Genv.find_def ge1 b1) as [d1|] eqn:ge1_b1'; try easy.
        eapply Genv.find_def_find_symbol_inversion; eauto.
        exploit match_prog_unique1; eauto. }
      assert (ge1_id_cp : Genv.find_comp_of_ident ge1 id = Some cp).
      { unfold Genv.find_comp_of_ident. now rewrite ge1_id, ge1_b1. }
      exploit same_symb; eauto.
      intros (H1 & H2 & H3 & H4).
      exploit H2; eauto. intros (-> & ge2_id). simpl in ge2_id.
      unfold Genv.find_comp_of_block.
      exploit Genv.find_symbol_find_def_inversion; eauto.
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
    - unfold Genv.allowed_cross_call in *.
      revert cross. case vf12; try easy.
      simpl. intros b1 _ b2 ofs2 delta j_b1 _.
      intros (id & cp' & ge1_b1 & ge1_b1' & imp & exp).
      exists id, cp'.
      exploit same_symb; eauto. intros (H1 & H2 & H3 & H4). simpl in *.
      exploit Genv.invert_find_symbol; eauto. intros ge1_id.
      exploit H2; eauto. intros (-> & ge2_id).
      split; [now apply Genv.find_invert_symbol|].


  Admitted.

  Lemma parallel_concrete: forall j s1 s2 s1' t,
      right_state_injection s j ge1 ge2 s1 s2 ->
      s |= s1 ∈ Right ->
      Clight.step1 ge1 s1 t s1' ->
      exists j' s2',
        Clight.step1 ge2 s2 t s2' /\
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
        { right. rewrite evf2. simpl. exists id, (comp_of fd2).
          split.
          { now apply Genv.find_invert_symbol. }
          unfold Genv.find_comp. rewrite <- evf2. unfold ge2 in find_vf2'.
          simpl in find_vf2'. rewrite find_vf2'. split; trivial.


        exists j, (Callstate fd2 vargs2 (Kcall optid f e2 le2 k2) m2).
        split.
        econstructor; eauto.
      * rename fd1 into fd.
        rename type_fd1 into type_fd.
        rewrite comp_vf1 in *.
        exploit find_funct_preserved; eauto.
        { eapply same_symb; eauto. }
        intros find_vf2.
        assert (Genv.find_comp ge2 vf2 = comp_of fd) as comp_vf2.
        { unfold Genv.find_comp. now rewrite find_vf2. }
        assert (Genv.allowed_call ge2 (comp_of f) vf2) as ALLOWED2.
        { admit. }
        exists j.
        exists (Callstate fd vargs2 (Kcall optid f e2 le2 k2) m2).
        split.
        { econstructor; eauto.
          - admit.
          - admit. }
        apply RightControl; trivial.
        constructor; trivial.
        now apply right_cont_injection_kcall_right.
      (* Stopped here... *)
      assert (vf = v') by admit. subst v'.
      exists j; eexists; split.
      * econstructor; eauto.
        - inv match_fd'; eauto.
        - exploit (Genv.match_genvs_allowed_calls match_W1_W2); eauto.
        - eapply (Genv.match_genvs_not_ptr_list_inj); eauto.
          exploit (Genv.match_genvs_find_comp match_W1_W2); eauto. intros <-.
          erewrite <- (Genv.match_genvs_type_of_call); eauto.
        - exploit (Genv.match_genvs_find_comp match_W1_W2); eauto. intros <-.
          exploit (@call_trace_inj _ _ _ _ ge1 ge2); eauto.
          simpl. apply Genv.globalenvs_match in match_W1_W2.
          intros sy. pose proof (Genv.mge_symb match_W1_W2 sy). unfold Genv.find_symbol; eauto.
      * (* Case analysis: are we changing side or not? *)
        destruct (s (comp_of fd)) eqn:side.
        - apply LeftControl; eauto; try now inv match_fd'; auto.
          simpl. apply right_cont_injection_kcall_right; eauto.
        - inv match_fd'; unfold in_side in *; simpl in *;
            unfold comp_of in *; simpl in side; unfold comp_of in *; simpl in side;
            try congruence.
          apply RightControl; eauto.
          constructor; eauto.
          simpl. apply right_cont_injection_kcall_right; eauto.
    + (* step_builtin *)
      exploit eval_exprlist_injection; eauto.
      auto.
      intros [vs' [? ?]].
      exploit ec_mem_inject; eauto. admit. admit. admit.
      intros [j' [? [? [? [? [? [? [? [? ?]]]]]]]]].
      exists j'; eexists; split.
      econstructor; eauto.
      apply RightControl; eauto.
      constructor; eauto.
      * constructor; eauto.
        - admit.
        - admit.
        - admit.
        - admit.
      * destruct H10.
        split. intros ? ? ? ?.
        exploit H10; eauto. intros [b' [? ?]].
        exists b'; split; eauto.
        intros ? ?.
        exploit H14; eauto.
      * intros ? ? ?.
        destruct optid.
        - simpl in *. rewrite PTree.gsspec in *.
          destruct (peq i i0); subst.
          inv H14. eexists; split; eauto.
          exploit H11; eauto. intros [? [? ?]]; eauto.
        - exploit H11; eauto. intros [? [? ?]]; eauto.
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
      exploit eval_expr_injection; eauto.
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
      admit.
    + (* step_return_1 *)
      admit.
    + (* step_skip_call *)
      admit.
    + (* step_switch *)
      exploit eval_expr_injection; eauto.
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
      admit.
    + (* step_internal_function *)
      admit.
    + (* step_external_function *)
      admit.
    + (* step_returnstate *)
      admit.
  Admitted.


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


  Lemma parallel_concrete_E0: forall s1 s2 s1' s2' t,
      right_state_injection s j s1 s2 ->
      is_right s s1 -> (* in the context *)
      Csem.step ge1 s1 E0 s1' ->
      Csem.step ge2 s2 t s2' ->
      t = E0 /\ right_state_injection s j s1' s2'.
    Proof.
      intros.
      exploit parallel_concrete; eauto.
      intros [? [? ?]].
      assert (t = E0 /\ s2' = x).
      { clear -H2 H3.
        inv H2; inv H3.
        - admit.
        - inv H; inv H0; eauto.
      }
      (* rely on determinacy lemma with empty traces? *)
  Admitted.

  Lemma parallel_abstract_E0: forall s1 s2 s1' s2',
      right_state_injection s j s1 s2 ->
      is_left s s1 ->
      Csem.step ge1 s1 E0 s1' ->
      Csem.step ge2 s2 E0 s2' ->
      right_state_injection s j s1' s2'.
    Proof.
      intros s1 s2 s1' t rs_inj is_l step1.
      inv rs_inj.
      - admit.
      - admit. (* contradiction *)
  Admitted.

  Lemma parallel_abstract_t: forall s1 s2 s1' s2' t,
      right_state_injection s j s1 s2 ->
      is_left s s1 ->
      Csem.step ge1 s1 t s1' ->
      Csem.step ge2 s2 t s2' ->
      right_state_injection s j s1' s2'.

Lemma parallel_concrete p1 p2 scs1 scs2:
  left_side s p1 -> (* use definitions from RSC.v *)
  left_side s p2 -> (* use definitions from RSC.v *)
  partial_state_equivalent s scs1 scs2 -> (* to define --> using memory injections? *)
  pc_in_left_part scs1 -> (* to define *)
  CS.kstep (prepare_global_env (program_link p p1)) scs1 t scs1' -> (* use step of Csem instead *)
  exists2 scs2',
    CS.kstep (prepare_global_env (program_link p p2)) scs2 t scs2' /\ (* use step of Csem instead *)
      partial_state_equivalent s scs1' scs2'. (* to define *)
