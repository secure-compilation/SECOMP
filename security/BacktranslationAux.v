Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import Tactics.
Require Import riscV.Asm.
Require Import BtBasics BtInfoAsm MemoryDelta MemoryWeak.
Require Import Ctypes Clight.
Require Import Backtranslation.



Section CODEPROOFS.

  Lemma ptr_of_id_ofs_eval
        (ge: genv) id ofs e b cp le m
        (GE1: wf_env ge e)
        (GE2: Senv.find_symbol ge id = Some b)
        (GE3: Genv.allowed_addrof ge cp id)
    :
    eval_expr ge e cp le m (ptr_of_id_ofs id ofs) (Vptr b ofs).
  Proof.
    specialize (GE1 id). rewrite GE2 in GE1.
    unfold ptr_of_id_ofs. destruct (Archi.ptr64) eqn:ARCH.
    - eapply eval_Ebinop. eapply eval_Eaddrof. eapply eval_Evar_global; eauto.
      simpl_expr.
      simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
      rewrite Ptrofs.of_int64_to_int64; auto.
    - eapply eval_Ebinop. eapply eval_Eaddrof. eapply eval_Evar_global; eauto.
      simpl_expr.
      simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
      erewrite Ptrofs.agree32_of_ints_eq; auto. apply Ptrofs.agree32_to_int; auto.
  Qed.

  Lemma code_mem_delta_cons
        (ge: Senv.t) k d sn
    :
    code_mem_delta ge (k :: d) sn =
      Ssequence (code_mem_delta_kind ge k) (code_mem_delta ge d sn).
  Proof. unfold code_mem_delta. ss. Qed.

  Lemma code_mem_delta_app
        (ge: Senv.t) d1 d2 sn
    :
    code_mem_delta ge (d1 ++ d2) sn = (code_mem_delta ge d1 (code_mem_delta ge d2 sn)).
  Proof.
    revert sn d2. induction d1; intros; ss.
    rewrite ! code_mem_delta_cons. erewrite IHd1. auto.
  Qed.

  Lemma type_of_chunk_val_to_expr
        (ge: Senv.t) ch ty v e
        (WF: wf_chunk_val_b ch v)
        (CT: chunk_to_type ch = Some ty)
        (CVE: chunk_val_to_expr ge ch v = Some e)
    :
    typeof e = ty.
  Proof. unfold chunk_val_to_expr in CVE. rewrite CT in CVE. des_ifs. Qed.

  Definition val_is_int (v: val) := (match v with | Vint _ => True | _ => False end).
  Definition val_is_not_int (v: val) := (match v with | Vint _ => False | _ => True end).

  Lemma val_cases v: (val_is_int v) \/ (val_is_not_int v).
  Proof. destruct v; ss; auto. Qed.

  Lemma sem_cast_chunk_val
        (ge: Senv.t) m ch ty v e
        (WF: wf_chunk_val_b ch v)
        (CT: chunk_to_type ch = Some ty)
        (CVE: chunk_val_to_expr ge ch v = Some e)
        (NINT: val_is_not_int v)
    :
    Cop.sem_cast v (typeof e) ty m = Some v.
  Proof.
    erewrite type_of_chunk_val_to_expr; eauto. apply Cop.cast_val_casted. clear - WF CT NINT.
    unfold wf_chunk_val_b, wf_chunk_val_b in WF. des_ifs; ss; inv CT; econs.
  Qed.

  Definition cast_chunk_int (ch: memory_chunk) (i: int): val :=
    match ch with
    | Mint8signed => Vint (Int.sign_ext 8 i)
    | Mint8unsigned => Vint (Int.zero_ext 8 i)
    | Mint16signed => Vint (Int.sign_ext 16 i)
    | Mint16unsigned => Vint (Int.zero_ext 16 i)
    | Mint32 => Vint i
    | _ => Vundef
    end.

  Lemma chunk_val_to_expr_eval
        (ge: genv) ch v exp e cp le m
        (EXP: chunk_val_to_expr ge ch v = Some exp)
        (WF: wf_chunk_val_b ch v)
    :
    eval_expr ge e cp le m exp v.
  Proof. unfold chunk_val_to_expr in EXP. des_ifs; ss; econs. Qed.

  Lemma wf_chunk_val_chunk_to_type
        ch v
        (WF: wf_chunk_val_b ch v)
    :
    exists ty, chunk_to_type ch = Some ty.
  Proof. unfold wf_chunk_val_b in WF. des_ifs; ss; eauto. Qed.

  Lemma wf_chunk_val_chunk_val_to_expr
        (ge: Senv.t) ch v
        (WF: wf_chunk_val_b ch v)
    :
    exists ve, chunk_val_to_expr ge ch v = Some ve.
  Proof.
    unfold chunk_val_to_expr. exploit wf_chunk_val_chunk_to_type; eauto.
    intros (ty & TY). rewrite TY. unfold wf_chunk_val_b in WF. des_ifs; ss; eauto.
  Qed.

  Lemma code_mem_delta_storev_correct
        (ge: genv) f k e le m m'
        d
        (WFE: wf_env ge e)
        (STORE: mem_delta_apply_storev (Some m) d = Some m')
        (WF: wf_mem_delta_storev_b ge d)
    :
    step1 ge (State f (code_mem_delta_storev ge d) k e le m)
          E0 (State f Sskip k e le m').
  Proof.
    unfold wf_mem_delta_storev_b in WF. des_ifs. rename m0 into ch, i into ofs. ss.
    exploit wf_chunk_val_chunk_to_type; eauto. intros (ty & TY).
    exploit wf_chunk_val_chunk_val_to_expr; eauto. intros (ve & EXPR).
    rewrite Heq, TY, EXPR.
    (* rewrite H, Heq, TY, EXPR. *)
    destruct (val_cases v) as [INT | NINT].
    { unfold val_is_int in INT. des_ifs. clear INT. eapply step_assign.
      - econs. unfold expr_of_addr. eapply ptr_of_id_ofs_eval; auto.
        eapply Genv.invert_find_symbol; eauto.
        right; auto.
      - instantiate (1:=Vint i). eapply chunk_val_to_expr_eval; eauto.
      - instantiate (1:=cast_chunk_int ch i). erewrite type_of_chunk_val_to_expr; eauto.
        unfold chunk_to_type in TY. destruct ch; ss; inv TY.
        + unfold Cop.sem_cast. ss. des_ifs.
        + unfold Cop.sem_cast. ss. des_ifs.
        + unfold Cop.sem_cast. ss. des_ifs.
        + unfold Cop.sem_cast. ss. des_ifs.
        + unfold Cop.sem_cast. ss. des_ifs.
      - simpl_expr. eapply access_mode_chunk_to_type_wf; eauto.
        rewrite <- STORE.
        admit.
        (* destruct ch; ss. *)
        (* + rewrite Mem.store_int8_sign_ext. auto. *)
        (* + rewrite Mem.store_int8_zero_ext. auto. *)
        (* + rewrite Mem.store_int16_sign_ext. auto. *)
        (* + rewrite Mem.store_int16_zero_ext. auto. *)
    }
      (* - apply andb_false_iff in Heq0 as [G | G]; try now inv G. *)
      (*   destruct cp_eq_dec; inv WF. *)
      (*   exfalso. pose proof (flowsto_refl (comp_of f)). now destruct flowsto_dec. } *)
    {
      (* assert (G: flowsto_dec c (comp_of f)). *)
      (* { destruct cp_eq_dec; inv WF. *)
      (*   pose proof (flowsto_refl (comp_of f)). now destruct flowsto_dec. } *)
      rewrite WF, H0. ss. eapply step_assign.
      - econs. unfold expr_of_addr. eapply ptr_of_id_ofs_eval; auto.
        eapply Genv.invert_find_symbol; eauto. right; auto.
      - instantiate (1:=v). eapply chunk_val_to_expr_eval; eauto.
      - ss. eapply sem_cast_chunk_val; eauto.
      - simpl_expr. eapply access_mode_chunk_to_type_wf; eauto.
        admit.
        (* destruct cp_eq_dec; inv WF. clarify. *)
    }
  Admitted.

  Lemma wf_mem_delta_storev_false_is_skip
        (ge: Senv.t) cp d
        (NWF: wf_mem_delta_storev_b ge cp d = false)
    :
    code_mem_delta_storev ge cp d = Sskip.
  Proof. destruct d as [[[ch ptr] v] cp0]. ss. des_ifs.
         admit.
  Admitted.

  Lemma code_mem_delta_correct
        (ge: genv)
        f k e le m m'
        d snext
        (WFE: wf_env ge e)
        (APPD: mem_delta_apply_wf ge (comp_of f) d (Some m) = Some m')
    :
    (star step1 ge (State f (code_mem_delta ge (comp_of f) d snext) k e le m)
          E0 (State f snext k e le m')).
  Proof.
    revert m m' snext APPD. induction d; intros.
    { unfold mem_delta_apply_wf in APPD. ss. inv APPD. unfold code_mem_delta. ss. econs 1. }
    rewrite mem_delta_apply_wf_cons in APPD. rewrite code_mem_delta_cons.
    des_ifs.
    - exploit mem_delta_apply_wf_some; eauto. intros (mi & APPD0). rewrite APPD0 in APPD.
      destruct a; ss. econs 2.
      { eapply step_seq. }
      econs 2.
      { eapply code_mem_delta_storev_correct; eauto. }
      take_step. eapply IHd; eauto. eauto. auto.
    - destruct a; ss.
      rewrite wf_mem_delta_storev_false_is_skip; auto.
      all: take_step; take_step; eapply IHd; eauto.
  Qed.

  Lemma code_bundle_trace_spec
        (ge: genv) cp cnt tr
        f e le m k
    :
    star step1 ge
         (State f (code_bundle_trace ge cp cnt tr) k e le m)
         E0
         (State f (switch_bundle_events ge cnt cp tr)
                (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge cnt cp tr)) Sskip k)
                e le m).
  Proof.
    econs 2.
    { unfold code_bundle_trace, Swhile. eapply step_loop. }
    econs 2.
    { eapply step_seq. }
    econs 2.
    { eapply step_ifthenelse. simpl_expr. ss. }
    rewrite Int.eq_false; ss. econs 2.
    { eapply step_skip_seq. }
    econs 1. all: eauto.
  Qed.

End CODEPROOFS.


Section GENV.

  Definition symbs_public (ge1 ge2: Senv.t) := (forall id : ident, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id).
  Definition symbs_find (ge1 ge2: Senv.t) := forall id b, Senv.find_symbol ge1 id = Some b -> Senv.find_symbol ge2 id = Some b.
  Definition symbs_volatile (ge1 ge2: Senv.t) := forall b, Senv.block_is_volatile ge2 b = Senv.block_is_volatile ge1 b.

  Definition match_symbs (ge1 ge2: Senv.t) := symbs_public ge1 ge2 /\ symbs_find ge1 ge2 /\ symbs_volatile ge1 ge2.

  Lemma match_symbs_meminj_public
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
    :
    meminj_public ge1 = meminj_public ge2.
  Proof.
    destruct MSYMB as (MSYMB1 & MSYMB2 & MSYMB3). unfold meminj_public. extensionalities b. des_ifs.
    - exfalso. apply Senv.invert_find_symbol in Heq. exploit MSYMB2; eauto. intros.
      apply Senv.find_invert_symbol in x0. rewrite x0 in Heq1. inv Heq1. specialize (MSYMB1 i0). clarify.
    - exfalso. apply Senv.invert_find_symbol in Heq. exploit MSYMB2; eauto. intros.
      apply Senv.find_invert_symbol in x0. clarify.
    - exfalso. apply Senv.invert_find_symbol in Heq. exploit MSYMB2; eauto. intros.
      apply Senv.find_invert_symbol in x0. rewrite x0 in Heq1. inv Heq1. specialize (MSYMB1 i0). clarify.
    - exfalso. rewrite MSYMB1 in Heq1. apply Senv.public_symbol_exists in Heq1. des.
      exploit MSYMB2; eauto. intros. apply Senv.invert_find_symbol in Heq0. clarify.
      apply Senv.find_invert_symbol in Heq1. clarify.
  Qed.

  Lemma match_symbs_wf_mem_delta_storev
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp0 d
    :
    wf_mem_delta_storev_b ge1 cp0 d = wf_mem_delta_storev_b ge2 cp0 d.
  Proof.
    destruct MSYMB as (MSYMB1 & MSYMB2 & MSYMB3).
    destruct d as [[[ch ptr] v] cp]. ss. des_ifs.
    - do 2 f_equal. apply Senv.invert_find_symbol, MSYMB2, Senv.find_invert_symbol in Heq. clarify.
    - exfalso. apply Senv.invert_find_symbol, MSYMB2, Senv.find_invert_symbol in Heq. clarify.
    - destruct (Senv.public_symbol ge2 i0) eqn:PUB; ss.
      exfalso. rewrite MSYMB1 in PUB. apply Senv.public_symbol_exists in PUB. des.
      exploit MSYMB2; eauto. intros. apply Senv.invert_find_symbol in Heq0. clarify.
      apply Senv.find_invert_symbol in PUB. clarify.
  Qed.

  Lemma match_symbs_wf_mem_delta_kind
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp
    :
    wf_mem_delta_kind_b ge1 cp = wf_mem_delta_kind_b ge2 cp.
  Proof. unfold wf_mem_delta_kind_b. extensionalities d. des_ifs. apply match_symbs_wf_mem_delta_storev; auto. Qed.

  Lemma match_symbs_get_wf_mem_delta
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp d
    :
    get_wf_mem_delta ge1 cp d = get_wf_mem_delta ge2 cp d.
  Proof. unfold get_wf_mem_delta. erewrite match_symbs_wf_mem_delta_kind; eauto. Qed.

  Lemma match_symbs_mem_delta_apply_wf
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp d m
    :
    mem_delta_apply_wf ge1 cp d m = mem_delta_apply_wf ge2 cp d m.
  Proof. unfold mem_delta_apply_wf. erewrite match_symbs_get_wf_mem_delta; eauto. Qed.

  Lemma match_symbs_code_mem_delta_kind
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp
    :
    code_mem_delta_kind ge1 cp = code_mem_delta_kind ge2 cp.
  Proof.
    extensionalities k. unfold code_mem_delta_kind. des_ifs.
    destruct d as [[[ch ptr] v] cp0]. ss. destruct ptr; ss.
    destruct MSYMB as (MSYMB1 & MSYMB2 & MSYMB3).
    destruct (Senv.invert_symbol ge1 b) eqn:INV1.
    { exploit Senv.invert_find_symbol; eauto. intros FIND1.
      exploit MSYMB2; eauto. intros FIND2. exploit Senv.find_invert_symbol; eauto. intros INV2.
      rewrite INV2. destruct (chunk_to_type ch) eqn:CHTY; auto.
      des_ifs.
      - apply andb_prop in Heq0, Heq2. des.
        (* apply andb_prop in Heq0, Heq2. des. *)
        assert (chunk_val_to_expr ge2 ch v = chunk_val_to_expr ge1 ch v).
        { unfold chunk_val_to_expr. rewrite CHTY.
          des_ifs.
          - admit.
          - congruence.
          (* clear - Heq6. *)
          (* unfold wf_chunk_val_b in Heq6. *)
          des_ifs.
        }
        rewrite Heq, Heq1 in H. clarify.
      - exfalso. apply andb_prop in Heq0. des. apply andb_prop in Heq0. des.
        clarify. rewrite ! andb_true_r in Heq2. rewrite MSYMB1 in Heq2. clarify.
      - exfalso. apply andb_prop in Heq0. des. apply andb_prop in Heq0. des.
        apply (wf_chunk_val_chunk_val_to_expr (ge2)) in Heq3; eauto. des; clarify.
      - exfalso. apply andb_prop in Heq2. des. apply andb_prop in Heq2. des.
        clarify. rewrite ! andb_true_r in Heq0. rewrite MSYMB1 in Heq2; clarify.
      - exfalso. apply andb_prop in Heq1. des. apply andb_prop in Heq1. des.
        apply (wf_chunk_val_chunk_val_to_expr (ge1)) in Heq3; eauto. des; clarify.
    }
    { des_ifs.
      exfalso. apply andb_prop in Heq2. des. apply andb_prop in Heq2. des.
      rewrite MSYMB1 in Heq2. eapply Senv.public_symbol_exists in Heq2. des.
      exploit MSYMB2. eapply Heq2. intros FIND4. eapply Senv.invert_find_symbol in Heq. clarify.
      exploit Senv.find_invert_symbol. apply Heq2. intros INV3. clarify.
    }
  Qed.

  Lemma match_symbs_code_mem_delta
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp d s
    :
    code_mem_delta ge1 cp d s = code_mem_delta ge2 cp d s.
  Proof. unfold code_mem_delta. erewrite match_symbs_code_mem_delta_kind; eauto. Qed.

  Lemma match_symbs_code_bundle_call
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp tr id evargs sg d
    :
    code_bundle_call ge1 cp tr id evargs sg d = code_bundle_call ge2 cp tr id evargs sg d.
  Proof. unfold code_bundle_call. erewrite match_symbs_code_mem_delta; eauto. Qed.

  Lemma match_symbs_code_bundle_return
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp tr evr d
    :
    code_bundle_return ge1 cp tr evr d = code_bundle_return ge2 cp tr evr d.
  Proof. unfold code_bundle_return. erewrite match_symbs_code_mem_delta; eauto. Qed.

  Lemma match_symbs_code_bundle_builtin
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp tr ef evargs d
    :
    code_bundle_builtin ge1 cp tr ef evargs d = code_bundle_builtin ge2 cp tr ef evargs d.
  Proof. unfold code_bundle_builtin. erewrite match_symbs_code_mem_delta; eauto. Qed.

  Lemma match_symbs_code_bundle_events
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp
    :
    code_bundle_event ge1 cp = code_bundle_event ge2 cp.
  Proof.
    extensionalities be. unfold code_bundle_event. des_ifs.
    eapply match_symbs_code_bundle_call; auto. eapply match_symbs_code_bundle_return; auto. eapply match_symbs_code_bundle_builtin; auto.
  Qed.

  Lemma match_symbs_switch_bundle_events
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp cnt tr
    :
    switch_bundle_events ge1 cnt cp tr = switch_bundle_events ge2 cnt cp tr.
  Proof. unfold switch_bundle_events. erewrite match_symbs_code_bundle_events; eauto. Qed.

  Lemma match_symbs_code_bundle_trace
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
        cp cnt tr
    :
    code_bundle_trace ge1 cp cnt tr = code_bundle_trace ge2 cp cnt tr.
  Proof. unfold code_bundle_trace. erewrite match_symbs_switch_bundle_events; eauto. Qed.


  Lemma match_symbs_symbols_inject
        ge1 ge2
        (MSYMB: match_symbs ge1 ge2)
    :
    symbols_inject (meminj_public ge1) ge1 ge2.
  Proof.
    destruct MSYMB as (MS0 & MS1 & MS2). unfold symbols_inject. splits; auto.
    - i. unfold meminj_public in H. des_ifs. split; auto.
    - i. exists b1. split; auto. unfold meminj_public. apply Senv.find_invert_symbol in H0.
      rewrite H0. rewrite H. auto.
    - i. unfold meminj_public in H. des_ifs.
  Qed.

End GENV.


Section PROOF.

  Lemma filter_filter
        A (l: list A) (p q: A -> bool)
    :
    filter q (filter p l) = filter (fun a => (p a) && (q a)) l.
  Proof.
    induction l; ss. des_ifs; ss; clarify.
    f_equal. auto.
  Qed.

  Lemma get_wf_mem_delta_idem
        ge cp d
    :
    get_wf_mem_delta ge cp (get_wf_mem_delta ge cp d) = get_wf_mem_delta ge cp d.
  Proof. unfold get_wf_mem_delta. rewrite filter_filter. f_equal. extensionalities k. apply andb_diag. Qed.

  Lemma mem_delta_apply_wf_get_wf_mem_delta
        ge cp d m
    :
    mem_delta_apply_wf ge cp d m = mem_delta_apply_wf ge cp (get_wf_mem_delta ge cp d) m.
  Proof. unfold mem_delta_apply_wf. rewrite get_wf_mem_delta_idem. auto. Qed.

  Lemma wf_mem_delta_kind_is_wf
        ge cp k
        (WF: wf_mem_delta_kind_b ge cp k)
    :
    mem_delta_kind_inj_wf cp (meminj_public ge) k.
  Proof. unfold wf_mem_delta_kind_b in WF. des_ifs. unfold wf_mem_delta_storev_b in WF. ss. des_ifs. apply Pos.eqb_eq in WF. auto. Qed.

  Lemma get_wf_mem_delta_is_wf
        cp ge d
    :
    mem_delta_inj_wf cp (meminj_public ge) (get_wf_mem_delta ge cp d).
  Proof. induction d; ss. des_ifs. econs; auto. apply wf_mem_delta_kind_is_wf; auto. Qed.

  Lemma mem_delta_apply_establish_inject2
        (ge: Senv.t) k m0 m0'
        (INJ: Mem.inject k m0 m0')
        (INCR: inject_incr (meminj_public ge) k)
        (NALLOC: meminj_not_alloc (meminj_public ge) m0)
        d cp m1
        (APPD: mem_delta_apply_wf ge cp d (Some m0) = Some m1)
        (FO: public_first_order ge m1)
    :
    exists m1', mem_delta_apply_wf ge cp d (Some m0') = Some m1' /\ Mem.inject (meminj_public ge) m1 m1'.
  Proof.
    unfold mem_delta_apply_wf in APPD. rewrite mem_delta_apply_wf_get_wf_mem_delta. eapply mem_delta_apply_establish_inject; eauto.
    apply get_wf_mem_delta_is_wf.
    unfold public_first_order in FO. ii. unfold meminj_public in H. des_ifs. apply Senv.invert_find_symbol in Heq.
    eapply FO; eauto.
  Qed.

  Lemma mem_delta_apply_establish_inject_preprocess_gen
        (ge: Senv.t) (k: meminj) m0 m0'
        (INJ: Mem.inject k m0 m0')
        pch pb pofs pv pcp m0''
        (PRE: Mem.store pch m0' pb pofs pv pcp = Some m0'')
        (PREB: forall b ofs, (meminj_public ge) b <> Some (pb, ofs))
        (INCR: inject_incr (meminj_public ge) k)
        (NALLOC: meminj_not_alloc (meminj_public ge) m0)
        d cp m1
        (APPD: mem_delta_apply_wf ge cp d (Some m0) = Some m1)
    :
    exists m1', mem_delta_apply_wf ge cp d (Some m0'') = Some m1' /\
             (meminj_first_order (meminj_public ge) m1 -> Mem.inject (meminj_public ge) m1 m1').
  Proof.
    unfold mem_delta_apply_wf in APPD. rewrite mem_delta_apply_wf_get_wf_mem_delta.
    eapply mem_delta_apply_establish_inject_preprocess_gen; eauto.
    apply get_wf_mem_delta_is_wf.
  Qed.

  Lemma mem_delta_apply_establish_inject_preprocess2
        (ge: Senv.t) (k: meminj) m0 m0'
        (INJ: Mem.inject k m0 m0')
        pch pb pofs pv pcp m0''
        (PRE: Mem.store pch m0' pb pofs pv pcp = Some m0'')
        (PREB: forall b ofs, (meminj_public ge) b <> Some (pb, ofs))
        (INCR: inject_incr (meminj_public ge) k)
        (NALLOC: meminj_not_alloc (meminj_public ge) m0)
        d cp m1
        (APPD: mem_delta_apply_wf ge cp d (Some m0) = Some m1)
        (FO: public_first_order ge m1)
    :
    exists m1', mem_delta_apply_wf ge cp d (Some m0'') = Some m1' /\ Mem.inject (meminj_public ge) m1 m1'.
  Proof.
    hexploit mem_delta_apply_establish_inject_preprocess_gen; eauto. i. des.
    esplits; eauto. apply H0. ii. unfold meminj_public in H1. des_ifs.
    eapply FO; eauto. apply Senv.invert_find_symbol; auto.
  Qed.

End PROOF.



Section DEFINITIONS.

  Definition meminj_same_block (j : meminj) :=
    forall b1 b2 del, j b1 = Some (b2, del) -> b1 = b2.

  Definition not_global_blks (ge: Senv.t) (ebs: list block) :=
    Forall (fun b => Senv.invert_symbol ge b = None) ebs.

  Definition blocks_of_env2 ge e : list block := (map (fun x => fst (fst x)) (blocks_of_env ge e)).

  Definition not_inj_blks (j: meminj) (ebs: list block) :=
    Forall (fun b => j b = None) ebs.

  Lemma not_global_is_not_inj_bloks
        ge l
        (NGB: not_global_blks ge l)
    :
    not_inj_blks (meminj_public ge) l.
  Proof. induction NGB. ss. econs; eauto. unfold meminj_public. des_ifs. Qed.

  Definition eq_policy (ge1: Asm.genv) (ge2: genv) :=
    Genv.genv_policy ge1 = Genv.genv_policy ge2.

End DEFINITIONS.



Section PROOF.

  (* Properties *)
  Lemma eventval_match_transl
        (ge: Senv.t)
        ev ty v
        (EM: eventval_match ge ev ty v)
    :
    eventval_match ge ev (typ_of_type (typ_to_type ty)) (eventval_to_val ge ev).
  Proof.
    inversion EM; subst; simpl; try constructor.
    setoid_rewrite H0. unfold Tptr in *. destruct Archi.ptr64; auto.
  Qed.

  Lemma eventval_match_eventval_to_val
        (ge: Senv.t)
        ev ty v
        (EM: eventval_match ge ev ty v)
    :
    eventval_to_val ge ev = v.
  Proof. inversion EM; subst; simpl; auto. setoid_rewrite H0. auto. Qed.

  Lemma eventval_list_match_transl
        (ge: Senv.t)
        evs tys vs
        (EM: eventval_list_match ge evs tys vs)
    :
    eventval_list_match ge evs (typlist_of_typelist (list_typ_to_typelist tys)) (list_eventval_to_list_val ge evs).
  Proof. induction EM; simpl. constructor. constructor; auto. eapply eventval_match_transl; eauto. Qed.

  Lemma eventval_list_match_transl_val
        (ge: Senv.t)
        evs tys vs
        (EM: eventval_list_match ge evs tys vs)
    :
    eventval_list_match ge evs tys (list_eventval_to_list_val ge evs).
  Proof. induction EM; simpl. constructor. constructor; auto. erewrite eventval_match_eventval_to_val; eauto. Qed.

  Lemma typ_type_typ
        (ge: Senv.t)
        ev ty v
        (EM: eventval_match ge ev ty v)
    :
    typ_of_type (typ_to_type ty) = ty.
  Proof. inversion EM; simpl; auto. subst. unfold Tptr. destruct Archi.ptr64; simpl; auto. Qed.

  Lemma eventval_to_expr_val_eval
        (ge: genv) en cp temp m ev ty v
        (WFENV: wf_env ge en)
        (EM: eventval_match ge ev ty v)
    (* (WFGE: wf_eventval_ge ge ev) *)
    :
    eval_expr ge en cp temp m (eventval_to_expr ev) (eventval_to_val ge ev).
  Proof. destruct ev; simpl in *; try constructor. inv EM. setoid_rewrite H4. eapply ptr_of_id_ofs_eval; auto. Qed.

  Lemma sem_cast_eventval_match
        (ge: Senv.t) v ty vv m
        (EM: eventval_match ge v (typ_of_type (typ_to_type ty)) vv)
    :
    Cop.sem_cast vv (typeof (eventval_to_expr v)) (typ_to_type ty) m = Some vv.
  Proof.
    destruct ty; simpl in *; inversion EM; subst; simpl in *; simpl_expr.
    all: try rewrite ptr_of_id_ofs_typeof; simpl.
    all: try (cbn; auto).
    all: unfold Tptr in *; destruct Archi.ptr64 eqn:ARCH; try congruence.
    { unfold Cop.sem_cast. simpl. rewrite ARCH. simpl. rewrite pred_dec_true; auto. }
    { unfold Cop.sem_cast. simpl. rewrite ARCH. auto. }
    { unfold Cop.sem_cast. simpl. rewrite ARCH. simpl. rewrite pred_dec_true; auto. }
    { unfold Cop.sem_cast. simpl. rewrite ARCH. auto. }
  Qed.

  Lemma list_eventval_to_expr_val_eval
        (ge: genv) en cp temp m evs tys
        (* (WFENV: Forall (wf_eventval_env en) evs) *)
        (WFENV: wf_env ge en)
        (EMS: eventval_list_match ge evs (typlist_of_typelist (list_typ_to_typelist tys)) (list_eventval_to_list_val ge evs))
    :
    eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_typ_to_typelist tys) (list_eventval_to_list_val ge evs).
  Proof.
    revert en cp temp m WFENV.
    match goal with | [H: eventval_list_match _ _ ?t ?v |- _] => remember t as tys2; remember v as vs2 end.
    revert tys Heqtys2 Heqvs2. induction EMS; intros; subst; simpl in *.
    { destruct tys; simpl in *. constructor. congruence. }
    inversion Heqvs2; clear Heqvs2; subst; simpl in *.
    destruct tys; simpl in Heqtys2. congruence with Heqtys2.
    inversion Heqtys2; clear Heqtys2; subst; simpl in *.
    econstructor; eauto. eapply eventval_to_expr_val_eval; eauto.
    (* eapply eventval_match_wf_eventval_ge; eauto. *)
    eapply sem_cast_eventval_match; eauto.
  Qed.

  Lemma eventval_match_eventval_to_type
        (ge: Senv.t)
        ev ty v
        (EM: eventval_match ge ev ty v)
    :
    eventval_match ge ev (typ_of_type (eventval_to_type ev)) v.
  Proof. inversion EM; subst; simpl; auto. Qed.

  Lemma list_eventval_match_eventval_to_type
        (ge: Senv.t)
        evs tys vs
        (ESM: eventval_list_match ge evs tys vs)
    :
    eventval_list_match ge evs (typlist_of_typelist (list_eventval_to_typelist evs)) vs.
  Proof. induction ESM; simpl. constructor. constructor; auto. eapply eventval_match_eventval_to_type; eauto. Qed.

  Lemma val_load_result_idem
        ch v
    :
    Val.load_result ch (Val.load_result ch v) = Val.load_result ch v.
  Proof.
    destruct ch, v; simpl; auto.
    5,6,7: destruct Archi.ptr64; simpl; auto.
    1,3: rewrite Int.sign_ext_idem; auto.
    3,4: rewrite Int.zero_ext_idem; auto.
    all: lia.
  Qed.

  Lemma val_load_result_aux
        F V (ge: Genv.t F V)
        ev ch v
        (EM: eventval_match ge ev (type_of_chunk ch) (Val.load_result ch v))
    :
    eventval_match ge ev (type_of_chunk ch) (Val.load_result ch (eventval_to_val ge ev)).
  Proof.
    inversion EM; subst; simpl in *; auto.
    1,2,3,4: rewrite H1, H2; rewrite val_load_result_idem; auto.
    rewrite H3, H. rewrite H0. rewrite val_load_result_idem. auto.
  Qed.

  Lemma eventval_match_proj_rettype
        (ge: Senv.t)
        ev ty v
        (EM: eventval_match ge ev ty v)
    :
    eventval_match ge ev (proj_rettype (rettype_of_type (typ_to_type ty))) v.
  Proof.
    inversion EM; subst; simpl; try constructor.
    unfold Tptr in *. destruct Archi.ptr64; simpl; auto.
  Qed.

  (* Lemma sem_cast_eventval *)
  (*       (ge: cgenv) v m *)
  (*       (WFEV: wf_eventval_ge ge v) *)
  (*   : *)
  (*   Cop.sem_cast (eventval_to_val ge v) (typeof (eventval_to_expr v)) (eventval_to_type v) m = Some (eventval_to_val ge v). *)
  (* Proof. rewrite typeof_eventval_to_expr_type. destruct v; simpl in *; simpl_expr. destruct WFEV. rewrite H. simpl_expr. Qed. *)

  (* Lemma list_eventval_to_expr_val_eval2 *)
  (*       (ge: genv) en cp temp m evs *)
  (*       (WFENV: Forall (wf_eventval_env en) evs) *)
  (*       (WFGE: Forall (wf_eventval_ge ge) evs) *)
  (*   : *)
  (*   eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_eventval_to_typelist evs) (list_eventval_to_list_val ge evs). *)
  (* Proof. *)
  (*   move evs at top. revert ge en cp temp m WFENV WFGE. induction evs; intros; simpl in *. *)
  (*   constructor. *)
  (*   inversion WFENV; clear WFENV; subst. inversion WFGE; clear WFGE; subst. *)
  (*   econstructor; eauto. eapply eventval_to_expr_val_eval; eauto. *)
  (*   apply sem_cast_eventval; auto. *)
  (* Qed. *)

  Lemma eventval_match_sem_cast
        (* F V (ge: Genv.t F V) *)
        (ge: genv)
        m ev ty v
        (EM: eventval_match ge ev ty v)
    :
    (* Cop.sem_cast (eventval_to_val ge ev) (typeof (eventval_to_expr ev)) (typ_to_type ty) m = Some (eventval_to_val ge ev). *)
    Cop.sem_cast v (typeof (eventval_to_expr ev)) (typ_to_type ty) m = Some v.
  Proof.
    inversion EM; subst; simpl; try constructor. all: simpl_expr.
    rewrite ptr_of_id_ofs_typeof. unfold Tptr. unfold Cop.sem_cast. destruct Archi.ptr64 eqn:ARCH; simpl.
    - rewrite ARCH; auto.
    - rewrite ARCH; auto.
  Qed.

  (* Lemma list_eventval_to_expr_val_eval_typs *)
  (*       (ge: genv) en cp temp m evs tys vs *)
  (*       (WFENV: Forall (wf_eventval_env en) evs) *)
  (*       (EMS: eventval_list_match ge evs tys vs) *)
  (*   : *)
  (*   eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_typ_to_typelist tys) vs. *)
  (* Proof. *)
  (*   revert en cp temp m WFENV. *)
  (*   induction EMS; intros; subst; simpl in *. constructor. *)
  (*   inversion WFENV; clear WFENV; subst. *)
  (*   econstructor; eauto. 2: eapply eventval_match_sem_cast; eauto. *)
  (*   exploit eventval_match_eventval_to_val. eauto. intros. rewrite <- H0. eapply eventval_to_expr_val_eval; auto. *)
  (*   eapply eventval_match_wf_eventval_ge; eauto. *)
  (* Qed. *)

  Lemma sem_cast_ptr
        b ofs m
    :
    Cop.sem_cast (Vptr b ofs) (Tpointer Tvoid noattr) (typ_to_type Tptr) m = Some (Vptr b ofs).
  Proof.
    unfold Tptr. destruct Archi.ptr64 eqn:ARCH; unfold Cop.sem_cast; simpl; rewrite ARCH; auto.
  Qed.

  Lemma sem_cast_proj_rettype
        (ge: genv) evres rty res m
        (EVM: eventval_match ge evres (proj_rettype rty) res)
    :
    Cop.sem_cast (eventval_to_val ge evres)
                 (typeof (eventval_to_expr evres))
                 (rettype_to_type rty) m
    = Some (eventval_to_val ge evres).
  Proof.
    destruct rty; simpl in *.
    { eapply eventval_match_sem_cast. eauto. erewrite eventval_match_eventval_to_val; eauto. }
    { inv EVM; simpl; simpl_expr.
      setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
      unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
      unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
    }
    { inv EVM; simpl; simpl_expr.
      setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
      unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
      unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
    }
    { inv EVM; simpl; simpl_expr.
      setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
      unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
      unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
    }
    { inv EVM; simpl; simpl_expr.
      setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
      unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
      unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
    }
    { inv EVM; simpl; simpl_expr.
      setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
      unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
      unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
    }
  Qed.

  Lemma type_of_params_eq
        params ts
        (PARSIGS : list_typ_to_list_type ts = map snd params)
    :
    type_of_params params = list_typ_to_typelist ts.
  Proof.
    revert params PARSIGS. induction ts; ii; ss.
    { destruct params; ss. }
    destruct params; ss. destruct p; ss. clarify. f_equal. auto.
  Qed.

  Lemma match_senv_eventval_match
        (ge0 ge1: Senv.t)
        (MS: match_symbs ge0 ge1)
        ev ty v
        (EM: eventval_match ge0 ev ty v)
    :
    eventval_match ge1 ev ty v.
  Proof. destruct MS as (MS0 & MS1 & MS2). inv EM; try econs; auto. rewrite MS0. auto. Qed.

  Lemma match_senv_eventval_list_match
        (ge0 ge1: Senv.t)
        (MS: match_symbs ge0 ge1)
        evs tys vs
        (EM: eventval_list_match ge0 evs tys vs)
    :
    eventval_list_match ge1 evs tys vs.
  Proof. induction EM; ss. econs; auto. econs; auto. eapply match_senv_eventval_match; eauto. Qed.

  Lemma unbundle_trace_app
        tr1 tr2
    :
    unbundle_trace (tr1 ++ tr2) = (unbundle_trace tr1) ++ (unbundle_trace tr2).
  Proof. induction tr1; ss. rewrite <- app_assoc. f_equal. auto. Qed.

  Lemma allowed_call_gen_function
        cp (ge_i: Asm.genv) (ge_c: genv) next cnt params tr f_i f_c
        (GE: symbs_find ge_i ge_c)
        (GEPOL: eq_policy ge_i ge_c)
        (GEN: f_c = gen_function ge_i cnt params tr f_i)
        (ALLOW : Genv.allowed_call ge_i cp (Vptr next Ptrofs.zero))
        (FINDF : Genv.find_funct ge_i (Vptr next Ptrofs.zero) = Some (AST.Internal f_i))
        (FINDF_C : Genv.find_funct ge_c (Vptr next Ptrofs.zero) = Some (Internal f_c))
    :
    Genv.allowed_call ge_c cp (Vptr next Ptrofs.zero).
  Proof.
    unfold Genv.allowed_call in *. des; [left | right].
    - subst. unfold Genv.find_comp. rewrite FINDF, FINDF_C. ss.
    - subst. unfold Genv.allowed_cross_call in *. des.
      unfold eq_policy in GEPOL. rewrite GEPOL in ALLOW2, ALLOW3.
      specialize (ALLOW0 _ FINDF). exists i, cp'. splits; auto.
      { apply Genv.invert_find_symbol in ALLOW. apply Genv.find_invert_symbol.
        apply GE. auto.
      }
      { i. rewrite FINDF_C in H. clarify. }
      { unfold Genv.find_comp in *. rewrite FINDF in ALLOW1. rewrite FINDF_C.
        rewrite <- ALLOW1. ss.
      }
  Qed.

  Lemma allowed_call_gen_function_external
        cp (ge_i: Asm.genv) (ge_c: genv) next ef
        (GE: symbs_find ge_i ge_c)
        (GEPOL: eq_policy ge_i ge_c)
        (ALLOW : Genv.allowed_call ge_i cp (Vptr next Ptrofs.zero))
        (FINDF : Genv.find_funct ge_i (Vptr next Ptrofs.zero) = Some (AST.External ef))
        (FINDF_C : Genv.find_funct ge_c (Vptr next Ptrofs.zero) =
                     Some (External ef
                                    (list_typ_to_typelist (sig_args (ef_sig ef)))
                                    (rettype_to_type (sig_res (ef_sig ef)))
                                    (sig_cc (ef_sig ef))))
    :
    Genv.allowed_call ge_c cp (Vptr next Ptrofs.zero).
  Proof.
    unfold Genv.allowed_call in *. des; [left | right].
    - subst. unfold Genv.find_comp. rewrite FINDF, FINDF_C. ss.
    - unfold Genv.allowed_cross_call in *. des.
      unfold eq_policy in GEPOL. rewrite GEPOL in ALLOW2, ALLOW3.
      specialize (ALLOW0 _ FINDF). exists i, cp'. splits; auto.
      { apply Genv.invert_find_symbol in ALLOW. apply Genv.find_invert_symbol.
        apply GE. auto.
      }
      { i. rewrite FINDF_C in H. clarify. }
      { unfold Genv.find_comp in *. rewrite FINDF in ALLOW1. rewrite FINDF_C.
        rewrite <- ALLOW1. ss.
      }
  Qed.

  Lemma eventval_list_match_list_eventval_to_list_val
        (ge: Senv.t) evargs tys vargs
        (EVMS: eventval_list_match ge evargs tys vargs)
    :
    list_eventval_to_list_val ge evargs = vargs.
  Proof.
    induction EVMS; ss. f_equal; auto.
    eapply eventval_match_eventval_to_val. eauto.
  Qed.

  Lemma match_symbs_eventval_match
        ge0 ge1 ev ty v
        (MS: match_symbs ge0 ge1)
        (EVM: eventval_match ge0 ev ty v)
    :
    eventval_match ge1 ev ty v.
  Proof.
    destruct MS as (MS0 & MS1 & MS2). inv EVM; econs; auto. rewrite MS0; auto.
  Qed.

  Lemma match_symbs_eventval_list_match
        ge0 ge1 ev ty v
        (MS: match_symbs ge0 ge1)
        (EVM: eventval_list_match ge0 ev ty v)
    :
    eventval_list_match ge1 ev ty v.
  Proof.
    induction EVM. econs. econs; auto. eapply match_symbs_eventval_match; eauto.
  Qed.

  Lemma alloc_variables_exists
        ge cp e m l
    :
    exists e' m', alloc_variables ge cp e m l e' m'.
  Proof.
    revert ge cp e m. induction l; ii.
    { do 2 eexists. econs 1. }
    destruct a as (id & ty).
    destruct (Mem.alloc m cp 0 (sizeof ge ty)) as (m0 & b0) eqn:ALLOC.
    specialize (IHl ge cp (PTree.set id (b0, ty) e) m0). des.
    do 2 eexists. econs 2. eapply ALLOC. eapply IHl.
  Qed.

  Lemma access_mode_typ_to_type
        s
    :
    exists ch, access_mode (typ_to_type s) = By_value ch.
  Proof. destruct s; ss; eauto. Qed.

  Lemma bind_parameters_exists
        (ge: genv) cp (e: env) m params vargs
        (INENV: Forall (fun '(id, ty) =>
                          exists b, (e ! id = Some (b, ty)) /\
                                 (forall ch, access_mode ty = By_value ch ->
                                        Mem.valid_access m ch b 0 Writable (Some cp)))
                       params)
        sg
        (PARSIGS: list_typ_to_list_type sg = map snd params)
        evargs
        (EMS: eventval_list_match ge evargs sg vargs)
    :
    exists m', bind_parameters ge cp e m params vargs m'.
  Proof.
    revert e m vargs INENV sg PARSIGS evargs EMS. induction params; ii.
    { ss. inv EMS; ss. eexists. econs. }
    destruct a as (id & ty). inv INENV. des. ss.
    destruct sg; ss. rename t into s. clarify. inv EMS.
    destruct (access_mode_typ_to_type s) as (ch & ACCM).
    specialize (H0 _ ACCM). hexploit Mem.valid_access_store. apply H0. instantiate (1:=v1).
    intros (m0 & STORE).
    assert
      (FA: Forall
             (fun '(id, ty) =>
                exists b : block,
                  e ! id = Some (b, ty) /\
                    (forall ch : memory_chunk, access_mode ty = By_value ch ->
                                          Mem.valid_access m0 ch b 0 Writable (Some cp))) params).
    { clear - H2 STORE. move H2 before cp. revert_until H2. induction H2; ii; ss.
      econs; eauto. des_ifs. des. esplits; eauto. i. eapply Mem.store_valid_access_1; eauto.
    }
    hexploit IHparams. apply FA. 1,2: eauto. intros. des. exists m'.
    econs; eauto. econs; eauto.
  Qed.

  Lemma alloc_variables_wf_id
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
        (WF: list_norepet (var_names params))
    :
    forall id bt, (~ In id (var_names params)) -> (e ! id = Some bt) -> (e' ! id = Some bt).
  Proof.
    revert WF. induction EA; ii; ss.
    apply Classical_Prop.not_or_and in H0. des. inv WF.
    apply IHEA; auto. rewrite PTree.gso; auto.
  Qed.

  Lemma alloc_variables_valid_access
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
    :
    forall b' ch' ofs' p' cp', Mem.valid_access m ch' b' ofs' p' cp' ->
                          Mem.valid_access m' ch' b' ofs' p' cp'.
  Proof.
    i. assert (WF: (b' < Mem.nextblock m)%positive).
    { unfold Mem.valid_access in H. des. destruct (Unusedglob.IS.MSet.Raw.MX.lt_dec b' (Mem.nextblock m)); auto.
      exfalso. unfold Mem.range_perm in H. specialize (H ofs').
      eapply (Mem.nextblock_noaccess _ _ ofs' Cur) in n.
      exploit H.
      { pose proof (size_chunk_pos ch'). lia. }
      i. unfold Mem.perm in x0. rewrite n in x0. ss.
    }
    revert_until EA. induction EA; ii; ss.
    apply IHEA.
    { eapply Mem.valid_access_alloc_other; eauto. }
    { erewrite Mem.nextblock_alloc; eauto. lia. }
  Qed.

  Lemma alloc_variables_forall
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
        (WF: list_norepet (var_names params))
    :
    Forall (fun '(id, ty) =>
              exists b, (e' ! id = Some (b, ty)) /\
                     (forall ch, access_mode ty = By_value ch ->
                            Mem.valid_access m' ch b 0 Writable (Some cp))) params.
  Proof.
    revert WF. induction EA; ii; ss.
    inv WF. econs; eauto.
    hexploit alloc_variables_wf_id. apply EA. auto. apply H2. apply PTree.gss.
    i. esplits; eauto.
    i. eapply alloc_variables_valid_access. apply EA.
    apply Mem.valid_access_freeable_any. eapply Mem.valid_access_alloc_same; eauto. lia.
    { ss. clear - H1. destruct ty; ss; clarify. des_ifs; clarify; ss. des_ifs; clarify; ss. unfold Mptr. des_ifs. }
    exists 0. ss.
  Qed.

  Lemma assign_loc_valid_access
        ge cp ty m b ofs bit v m'
        (AL: assign_loc ge cp ty m b ofs bit v m')
        ch' b' ofs' perm' cp'
        (VA: Mem.valid_access m ch' b' ofs' perm' (Some cp'))
    :
    Mem.valid_access m' ch' b' ofs' perm' (Some cp').
  Proof.
    inv AL.
    - eapply Mem.store_valid_access_1; eauto.
    - eapply Mem.storebytes_valid_access_1; eauto.
    - inv H. eapply Mem.store_valid_access_1; eauto.
  Qed.

  Lemma bind_parameters_valid_access
        (ge: genv) cp (e: env) m params vargs m'
        (BIND: bind_parameters ge cp e m params vargs m')
        ch b ofs perm cp'
        (VA: Mem.valid_access m ch b ofs perm (Some cp'))
    :
    Mem.valid_access m' ch b ofs perm (Some cp').
  Proof.
    revert_until BIND. induction BIND; ii; ss.
    apply IHBIND. eapply assign_loc_valid_access; eauto.
  Qed.

  Lemma mem_delta_apply_wf_valid_access
        ge cp d m m'
        (APPD: mem_delta_apply_wf ge cp d (Some m) = Some m')
        ch b ofs perm cp'
        (VA: Mem.valid_access m ch b ofs perm cp')
    :
    Mem.valid_access m' ch b ofs perm cp'.
  Proof.
    move d before ge. revert_until d. induction d; ii.
    { unfold mem_delta_apply_wf in APPD. ss; clarify. }
    rewrite mem_delta_apply_wf_cons in APPD. des_ifs.
    - destruct a; ss. hexploit mem_delta_apply_wf_some; eauto.
      intros (m0 & STOREV). rewrite STOREV in APPD.
      eapply IHd. apply APPD.
      unfold mem_delta_apply_storev in STOREV. des_ifs.
      unfold Mem.storev in STOREV. des_ifs.
      eapply Mem.store_valid_access_1; eauto.
    - eapply IHd; eauto.
  Qed.

  Lemma bind_parameters_mem_load
        ge cp e m0 params vargs m1
        (BIND: bind_parameters ge cp e m0 params vargs m1)
    :
    forall ch b ofs cp',
      (forall id b_e ty, (e ! id = Some (b_e, ty) -> b <> b_e)) ->
      (Mem.load ch m1 b ofs cp' = Mem.load ch m0 b ofs cp').
  Proof.
    induction BIND; ii; ss.
    rewrite IHBIND; auto.
    inv H0.
    - eapply Mem.load_store_other. eapply H3. left. ii. clarify. specialize (H1 _ _ _ H). clarify.
    - eapply Mem.load_storebytes_other. eapply H7. left. ii. clarify. specialize (H1 _ _ _ H). clarify.
  Qed.

  Lemma alloc_variables_mem_load
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
    :
    forall ch b ofs cp',
      (b < Mem.nextblock m)%positive ->
      (Mem.load ch m' b ofs cp' = Mem.load ch m b ofs cp').
  Proof.
    induction EA; ii; ss.
    rewrite IHEA.
    { eapply Mem.load_alloc_unchanged; eauto. }
    { erewrite Mem.nextblock_alloc; eauto. lia. }
  Qed.

  Lemma alloc_variables_old_blocks
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
    :
    forall b, (b < Mem.nextblock m)%positive ->
         (forall id b' ty, e ! id = Some (b', ty) -> b <> b') ->
         (forall id b' ty, e' ! id = Some (b', ty) -> b <> b').
  Proof.
    induction EA; i.
    { ii; clarify. specialize (H0 _ _ _ H1). clarify. }
    hexploit Mem.alloc_result; eauto. intros; clarify.
    eapply IHEA. 3: eapply H2.
    { erewrite Mem.nextblock_alloc; eauto. lia. }
    { i. destruct (Pos.eq_dec id id1).
      - clarify. rewrite PTree.gss in H3. clarify. lia.
      - rewrite PTree.gso in H3; auto. eapply H1; eauto.
    }
  Qed.

  Lemma mem_delta_apply_wf_mem_load
        ge cp d m m'
        (APPD: mem_delta_apply_wf ge cp d (Some m) = Some m')
    :
    forall id ch b ofs cp',
      Senv.invert_symbol ge b = Some id ->
      Senv.public_symbol ge id = false ->
      (Mem.load ch m' b ofs cp' = Mem.load ch m b ofs cp').
  Proof.
    move d before ge. revert_until d. induction d; ii.
    { unfold mem_delta_apply_wf in APPD. ss. clarify. }
    rewrite mem_delta_apply_wf_cons in APPD. des_ifs.
    { destruct a; ss. unfold wf_mem_delta_storev_b in Heq. des_ifs. ss.
      hexploit mem_delta_apply_wf_some; eauto. intros (m1 & STORE). rewrite STORE in APPD.
      erewrite IHd. 2: eauto. 2: eauto. all: auto.
      destruct (Pos.eq_dec b b0).
      - clarify.
      - erewrite Mem.load_store_other. 2: eauto. all: auto.
    }
    { eapply IHd; eauto. }
  Qed.

  Lemma nat64_int64_add_one
        n
        (BOUND: Z.of_nat n < Int64.modulus)
    :
    Int64.add (nat64 n) Int64.one = nat64 (n + 1).
  Proof.
    unfold nat64. rewrite Nat2Z.inj_add. ss.
    assert (N: Z.of_nat n = Int64.unsigned (Int64.repr (Z.of_nat n))).
    { symmetry. apply Int64.unsigned_repr. split. apply Zle_0_nat.
      unfold Int64.max_unsigned. lia.
    }
    assert (ONE: 1 = (Int64.unsigned (Int64.repr 1))).
    { ss. }
    rewrite N at 2. rewrite ONE. rewrite <- Int64.add_unsigned. ss.
  Qed.

  Lemma mem_free_list_impl1
        blks m cp m_f
        (FREE: Mem.free_list m blks cp = Some m_f)
    :
    Forall (fun '(b, lo, hi) => (Mem.range_perm m b lo hi Cur Freeable) /\ (Mem.can_access_block m b (Some cp))) blks.
  Proof.
    Local Opaque Mem.can_access_block.
    revert_until blks. induction blks; ii; ss. des_ifs. ss. econs.
    2:{ cut (Forall (fun '(b0, lo, hi) => Mem.range_perm m0 b0 lo hi Cur Freeable /\ Mem.can_access_block m0 b0 (Some cp)) blks); cycle 1.
        { eapply IHblks; eauto. }
        clear - Heq. intros FA. revert_until blks. induction blks; ii; ss.
        destruct a as ((ba & loa) & hia). ss. inv FA. des; clarify. econs.
        {
          clear IHblks. split.
          - unfold Mem.range_perm in *. ii. eapply Mem.perm_free_3. eauto. eauto.
          - eapply Mem.free_can_access_block_inj_2; eauto.
        }
        eapply IHblks; eauto.
    }
    split.
    - eapply Mem.free_range_perm; eauto.
    - eapply Mem.free_can_access_block_1; eauto.
      Local Transparent Mem.can_access_block.
  Qed.

  Lemma mem_free_list_impl2
        blks m cp
        (NR: list_norepet (map (fun x => fst (fst x)) blks))
        (FA: Forall (fun '(b, lo, hi) => (Mem.range_perm m b lo hi Cur Freeable) /\ (Mem.can_access_block m b (Some cp))) blks)
    :
    exists m_f, (Mem.free_list m blks cp = Some m_f).
  Proof.
    Local Opaque Mem.can_access_block.
    revert_until blks. induction blks; ii; ss; eauto.
    inv FA. inv NR. des_ifs; des.
    2:{ exfalso. destruct (Mem.range_perm_free _ _ _ _ _ H1 H0) as (m0 & FREE). clarify. }
    eapply IHblks; clear IHblks; eauto. ss. clear - H2 H3 Heq.
    revert_until blks. induction blks; ii; ss. inv H2. des_ifs; ss. des. econs; eauto.
    clear IHblks H4. apply Classical_Prop.not_or_and in H3. des. split.
    - unfold Mem.range_perm in *. ii. hexploit Mem.perm_free_inv; eauto. ii. des; clarify.
    - eapply Mem.free_can_access_block_inj_1; eauto.
      Local Transparent Mem.can_access_block.
  Qed.

  Lemma list_map_norepet_rev
        A (l: list A) B (f: A -> B)
        (NR: list_norepet (map f l))
    :
    list_norepet l.
  Proof.
    revert NR. induction l; ii; ss. econs. inv NR. econs; eauto.
    ii. apply H1; clear H1. apply in_map; auto.
  Qed.

  Lemma alloc_variables_wunchanged_on
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
    :
    wunchanged_on (fun b _ => Mem.valid_block m b) m m'.
  Proof.
    induction EA. apply wunchanged_on_refl.
    eapply wunchanged_on_implies in IHEA.
    { eapply wunchanged_on_trans. 2: eauto. eapply alloc_wunchanged_on. eauto. }
    { ii. ss. }
  Qed.

  Lemma alloc_variables_exists_free_list
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
        (ENV1: forall id1 id2 b1 b2 t1 t2, (id1 <> id2) -> (e ! id1 = Some (b1, t1)) -> (e ! id2 = Some (b2, t2)) -> (b1 <> b2))
        (ENV2: forall id b t, (e ! id = Some (b, t)) -> (Mem.valid_block m b))
        m_f0
        (FREE: Mem.free_list m' (blocks_of_env ge e) cp = Some m_f0)
    :
    exists m_f, Mem.free_list m' (blocks_of_env ge e') cp = Some m_f.
  Proof.
    revert_until EA. induction EA; ii; ss; eauto.
    assert (exists m_f0, Mem.free_list m2 (blocks_of_env ge (PTree.set id (b1, ty) e)) cp = Some m_f0); cycle 1.
    { des. eapply IHEA; clear IHEA; eauto.
      - i. destruct (Pos.eqb_spec id id1); clarify.
        + rewrite PTree.gss in H2. rewrite PTree.gso in H3; auto. clarify. specialize (ENV2 _ _ _ H3).
          ii. clarify. apply Mem.fresh_block_alloc in H. clarify.
        + destruct (Pos.eqb_spec id id2); clarify.
          * rewrite PTree.gso in H2; auto. rewrite PTree.gss in H3; auto. clarify. specialize (ENV2 _ _ _ H2).
            ii. clarify. apply Mem.fresh_block_alloc in H. clarify.
          * rewrite PTree.gso in H2, H3; auto. hexploit ENV1. 2: eapply H2. 2: eapply H3. all: auto.
      - i. destruct (Pos.eqb_spec id id0); clarify.
        + rewrite PTree.gss in H1. clarify. eapply Mem.valid_new_block; eauto.
        + rewrite PTree.gso in H1; auto. specialize (ENV2 _ _ _ H1). eapply Mem.valid_block_alloc; eauto.
    }
    clear IHEA. eapply mem_free_list_impl2.
    { unfold blocks_of_env. rewrite map_map. apply list_map_norepet.
      { eapply list_map_norepet_rev. apply PTree.elements_keys_norepet. }
      { i. unfold block_of_binding. des_ifs. ss. apply PTree.elements_complete in H0, H1.
        destruct (Pos.eqb_spec id i); clarify.
        - rewrite PTree.gss in H0. clarify. destruct (Pos.eqb_spec i i0); clarify.
          + rewrite PTree.gss in H1; clarify.
          + rewrite PTree.gso in H1; auto. specialize (ENV2 _ _ _ H1). ii; clarify.
            apply Mem.fresh_block_alloc in H. clarify.
        - rewrite PTree.gso in H0; auto. destruct (Pos.eqb_spec id i0); clarify.
          + rewrite PTree.gss in H1. clarify. specialize (ENV2 _ _ _ H0). ii; clarify.
            apply Mem.fresh_block_alloc in H. clarify.
          + rewrite PTree.gso in H1; auto. eapply ENV1. 2: apply H0. 2: apply H1. ii; clarify.
      }
    }
    { apply mem_free_list_impl1 in FREE. rewrite Forall_forall in *. i.
      assert ((x = (b1, 0%Z, sizeof ge ty)) \/ (In x (blocks_of_env ge e))).
      { clear - H0. unfold blocks_of_env in *. apply list_in_map_inv in H0. des.
        destruct x0 as (xid & xb & xt). apply PTree.elements_complete in H1. clarify.
        destruct (Pos.eqb_spec id xid); clarify.
        - rewrite PTree.gss in H1. clarify. left; auto.
        - rewrite PTree.gso in H1; auto. right. apply in_map. apply PTree.elements_correct. auto.
      }
      des.
      - clarify. split.
        + ii. eapply perm_wunchanged_on. eapply alloc_variables_wunchanged_on; eauto.
          { ss. eapply Mem.valid_new_block; eauto. }
          { eapply Mem.perm_alloc_2; eauto. }
        + rewrite <- wunchanged_on_own. 2: eapply alloc_variables_wunchanged_on; eauto.
          eapply Mem.owned_new_block; eauto. eapply Mem.valid_new_block; eauto.
      - eapply FREE. eauto.
    }
  Qed.

  Lemma assign_loc_wunchanged_on
        ge cp ty m b ofs bit v m'
        (AL: assign_loc ge cp ty m b ofs bit v m')
    :
    wunchanged_on (fun _ _ => True) m m'.
  Proof.
    inv AL.
    - eapply store_wunchanged_on; eauto.
    - eapply storebytes_wunchanged_on; eauto.
    - inv H. eapply store_wunchanged_on; eauto.
  Qed.

  Lemma bind_parameters_wunchanged_on
        (ge: genv) cp (e: env) m params vargs m'
        (BIND: bind_parameters ge cp e m params vargs m')
    :
    wunchanged_on (fun _ _ => True) m m'.
  Proof.
    induction BIND. apply wunchanged_on_refl. eapply wunchanged_on_trans. 2: apply IHBIND.
    eapply assign_loc_wunchanged_on; eauto.
  Qed.

  Lemma wunchanged_on_exists_free
        m m'
        (WU: wunchanged_on (fun b _ => Mem.valid_block m b) m m')
        b lo hi cp m_f
        (FREE: Mem.free m b lo hi cp = Some m_f)
    :
    exists m_f', Mem.free m' b lo hi cp = Some m_f'.
  Proof.
    hexploit Mem.free_range_perm; eauto. hexploit Mem.free_can_access_block_1; eauto. i.
    hexploit Mem.range_perm_free.
    3:{ intros (m0 & F). eexists; eapply F. }
    - unfold Mem.range_perm in *. i. eapply perm_wunchanged_on. 3: eauto. eauto. ss. eapply Mem.perm_valid_block; eauto.
    - rewrite <- wunchanged_on_own; eauto. eapply Mem.can_access_block_valid_block. eauto.
  Qed.

  Lemma assign_loc_perm
        ge cp ty m b ofs bit v m'
        (AL: assign_loc ge cp ty m b ofs bit v m')
        b' o' C P
        (PERM: Mem.perm m b' o' C P)
    :
    Mem.perm m' b' o' C P.
  Proof.
    inv AL.
    - eapply Mem.perm_store_1; eauto.
    - eapply Mem.perm_storebytes_1; eauto.
    - inv H. eapply Mem.perm_store_1; eauto.
  Qed.

  Lemma assign_loc_own
        ge cp ty m b ofs bit v m'
        (AL: assign_loc ge cp ty m b ofs bit v m')
        b' cp'
        (OWN: Mem.can_access_block m b' cp')
    :
    Mem.can_access_block m' b' cp'.
  Proof.
    inv AL.
    - rewrite <- Mem.store_can_access_block_inj; eauto.
    - eapply Mem.storebytes_can_access_block_inj_1; eauto.
    - inv H. rewrite <- Mem.store_can_access_block_inj; eauto.
  Qed.

  Lemma assign_loc_exists_free
        ge cp ty m b ofs bit v m'
        (AL: assign_loc ge cp ty m b ofs bit v m')
        b' lo hi cp' m_f
        (FREE: Mem.free m b' lo hi cp' = Some m_f)
    :
    exists m_f, Mem.free m' b' lo hi cp' = Some m_f.
  Proof.
    hexploit Mem.free_range_perm; eauto. hexploit Mem.free_can_access_block_1; eauto. i.
    hexploit Mem.range_perm_free.
    3:{ intros (m0 & F). eexists; eapply F. }
    - unfold Mem.range_perm in *. i. eapply assign_loc_perm; eauto.
    - eapply assign_loc_own; eauto.
  Qed.

  Lemma wunchanged_on_free_preserves
        m m'
        (WU : wunchanged_on (fun (b : block) (_ : Z) => Mem.valid_block m b) m m')
        b lo hi cp m1 m1'
        (FREE: Mem.free m b lo hi cp = Some m1)
        (FREE': Mem.free m' b lo hi cp = Some m1')
    :
    wunchanged_on (fun (b0 : block) (_ : Z) => Mem.valid_block m1 b0) m1 m1'.
  Proof.
    inv WU. econs.
    - rewrite (Mem.nextblock_free _ _ _ _ _ _ FREE). rewrite (Mem.nextblock_free _ _ _ _ _ _ FREE'). auto.
    - i. assert (VB: Mem.valid_block m b0).
      { eapply Mem.valid_block_free_2; eauto. }
      split; i.
      + pose proof (Mem.perm_free_3 _ _ _ _ _ _ FREE _ _ _ _ H1). rewrite wunchanged_on_perm in H2; auto.
        eapply Mem.perm_free_inv in H2. 2: eauto. des; auto. clarify.
        hexploit Mem.perm_free_2. eapply FREE. split; eauto. i. exfalso. apply H2. eapply H1.
      + pose proof (Mem.perm_free_3 _ _ _ _ _ _ FREE' _ _ _ _ H1). rewrite <- wunchanged_on_perm in H2; auto.
        eapply Mem.perm_free_inv in H2. 2: eauto. des; auto. clarify.
        hexploit Mem.perm_free_2. eapply FREE'. split; eauto. i. exfalso. apply H2. eapply H1.
    - i. assert (VB: Mem.valid_block m b0).
      { eapply Mem.valid_block_free_2; eauto. }
      split; i.
      + eapply Mem.free_can_access_block_inj_1; eauto. apply wunchanged_on_own; auto.
        eapply Mem.free_can_access_block_inj_2; eauto.
      + eapply Mem.free_can_access_block_inj_1; eauto. apply wunchanged_on_own; auto.
        eapply Mem.free_can_access_block_inj_2; eauto.
  Qed.

  Lemma wunchanged_on_exists_mem_free_list
        m m'
        (WU: wunchanged_on (fun b _ => Mem.valid_block m b) m m')
        l cp m_f
        (FREE: Mem.free_list m l cp = Some m_f)
    :
    exists m_f', Mem.free_list m' l cp = Some m_f'.
  Proof.
    move l after m. revert_until l. induction l; ii; ss; eauto. des_ifs.
    2:{ exfalso. hexploit wunchanged_on_exists_free. 2: eapply Heq0. 2: auto.
        2:{ intros. des. rewrite H in Heq; clarify. }
        auto.
    }
    hexploit IHl. 2: eapply FREE.
    { instantiate (1:=m0). eapply wunchanged_on_free_preserves; eauto. }
    eauto.
  Qed.

  Lemma mem_free_list_wunchanged_on
        x m l cp m'
        (FL: Mem.free_list m l cp = Some m')
        (WF: Forall (fun '(b, lo, hi) => (x <= b)%positive) l)
    :
    wunchanged_on (fun b _ => (b < x)%positive) m m'.
  Proof.
    move WF before x. revert_until WF. induction WF; i; ss. clarify. apply wunchanged_on_refl. des_ifs.
    hexploit IHWF; eauto. i. eapply wunchanged_on_trans. 2: eauto.
    eapply free_wunchanged_on; eauto.
    i. lia.
  Qed.

  Lemma wunchanged_on_free_list_preserves
        m m'
        (WU: wunchanged_on (fun b _ => Mem.valid_block m b) m m')
        l cp m_f m_f'
        (FREE: Mem.free_list m l cp = Some m_f)
        (FREE': Mem.free_list m' l cp = Some m_f')
    :
    wunchanged_on (fun b _ => Mem.valid_block m_f b) m_f m_f'.
  Proof.
    move l after m. revert_until l. induction l; ii; ss. clarify.
    des_ifs. eapply IHl. 2,3: eauto. eapply wunchanged_on_free_preserves; eauto.
  Qed.

  Lemma mem_delta_apply_wf_wunchanged_on
        ge cp d m m'
        (APPD: mem_delta_apply_wf ge cp d (Some m) = Some m')
        P
    :
    wunchanged_on P m m'.
  Proof.
    revert_until d. induction d; ii; ss.
    { cbn in APPD. clarify. apply wunchanged_on_refl. }
    rewrite mem_delta_apply_wf_cons in APPD. des_ifs.
    - hexploit mem_delta_apply_wf_some; eauto. intros (m0 & ST). rewrite ST in APPD.
      specialize (IHd _ _ APPD). unfold mem_delta_apply_kind in ST. unfold mem_delta_apply_storev in ST. des_ifs.
      ss. des_ifs. ss. eapply wunchanged_on_trans. eapply store_wunchanged_on. eapply ST.
      eapply wunchanged_on_implies. eapply IHd. ss.
    - eauto.
      Unshelve. all: exact 0%nat.
  Qed.

  Lemma alloc_variables_fresh_blocks
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
        x
        (X: (x <= Mem.nextblock m)%positive)
        (FA: Forall (fun '(b0, _, _) => (x <= b0)%positive) (blocks_of_env ge e))
    :
    Forall (fun '(b0, _, _) => (x <= b0)%positive) (blocks_of_env ge e').
  Proof.
    revert_until EA. induction EA; ii; ss. specialize (IHEA x).
    eapply IHEA; clear IHEA.
    { erewrite Mem.nextblock_alloc; eauto. lia. }
    apply Forall_forall. rewrite Forall_forall in FA. ii. specialize (FA x0). des_ifs.
    unfold blocks_of_env in H0. apply list_in_map_inv in H0. des. destruct x0 as (xid & xb & xt).
    apply PTree.elements_complete in H1. destruct (Pos.eqb_spec id xid); clarify.
    - rewrite PTree.gss in H1. ss. clarify. erewrite Mem.alloc_result. 2: eauto. auto.
    - rewrite PTree.gso in H1; auto. apply FA. rewrite H0. unfold blocks_of_env. apply in_map.
      apply PTree.elements_correct; auto.
  Qed.

  Lemma alloc_variables_one_fresh_block
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
        (NR: list_norepet (var_names params))
        xid xb xt
        (NOT: e ! xid = None)
        (GET: e' ! xid = Some (xb, xt))
    :
    ~ (Mem.valid_block m xb).
  Proof.
    revert_until EA. induction EA; i. clarify.
    inv NR. destruct (Pos.eqb_spec xid id).
    { subst id. hexploit alloc_variables_wf_id. eauto. auto. eauto. apply PTree.gss.
      i. rewrite GET in H0. clarify. eapply Mem.fresh_block_alloc; eauto. }
    hexploit IHEA. auto. rewrite PTree.gso. eapply NOT. auto. eapply GET. i.
    ii. apply H0. unfold Mem.valid_block in *. erewrite Mem.nextblock_alloc; eauto.
    etransitivity. eapply H1. apply Plt_succ.
  Qed.

  Lemma assign_loc_outside_mem_inject
        ge cp ty m b ofs bf v m'
        (AL: assign_loc ge cp ty m b ofs bf v m')
        k m0
        (INJ: Mem.inject k m0 m)
        (NIB: k b = None)
        (MS: meminj_same_block k)
    :
    Mem.inject k m0 m'.
  Proof.
    inv AL.
    - eapply Mem.store_outside_inject; eauto. i. specialize (MS _ _ _ H1). clarify.
    - eapply Mem.storebytes_outside_inject; eauto. i. specialize (MS _ _ _ H5). clarify.
    - inv H. eapply Mem.store_outside_inject; eauto. i. specialize (MS _ _ _ H). clarify.
  Qed.

  Lemma bind_parameters_outside_mem_inject
        ge cp e m_cur params vargs m_next
        (BIND: bind_parameters ge cp e m_cur params vargs m_next)
        k m
        (INJ: Mem.inject k m m_cur)
        (NIB: forall id b t, e ! id = Some (b, t) -> k b = None)
        (MS: meminj_same_block k)
    (* (NIB: not_inj_blks k (blocks_of_env2 ge e)) *)
    :
    Mem.inject k m m_next.
  Proof.
    revert_until BIND. induction BIND; ii.
    { auto. }
    apply IHBIND; auto. clear IHBIND. specialize (NIB _ _ _ H).
    eapply assign_loc_outside_mem_inject; eauto.
  Qed.

  Lemma not_inj_blks_get_env
        k ge e
        (NIB: not_inj_blks k (blocks_of_env2 ge e))
    :
    forall id b t, e ! id = Some (b, t) -> k b = None.
  Proof.
    rr in NIB. unfold blocks_of_env2, blocks_of_env in NIB. rewrite map_map in NIB.
    rewrite Forall_forall in NIB. i. apply PTree.elements_correct in H.
    apply NIB. eapply (in_map (fun x : ident * (block * type) => fst (fst (block_of_binding ge x)))) in H. ss.
  Qed.

  Lemma not_global_blks_get_env
        (ge: genv) e
        (NIB: not_global_blks ge (blocks_of_env2 ge e))
    :
    forall id b t, e ! id = Some (b, t) -> (meminj_public ge) b = None.
  Proof. eapply not_inj_blks_get_env. eapply not_global_is_not_inj_bloks. eauto. Qed.

  Lemma meminj_public_same_block
        ge
    :
    meminj_same_block (meminj_public ge).
  Proof. rr. unfold meminj_public. i. des_ifs. Qed.

  Lemma alloc_variables_mem_inject
        ge cp e m params e' m'
        (EA: alloc_variables ge cp e m params e' m')
        k m0
        (INJ: Mem.inject k m0 m)
    :
    Mem.inject k m0 m'.
  Proof.
    revert_until EA. induction EA; ii. auto.
    apply IHEA. clear IHEA. eapply Mem.alloc_right_inject; eauto.
  Qed.

  Lemma mem_valid_access_wunchanged_on
        m ch b ofs p cp
        (MV: Mem.valid_access m ch b ofs p cp)
        P m'
        (WU: wunchanged_on P m m')
        (SAT: forall ofs', P b ofs')
    :
    Mem.valid_access m' ch b ofs p cp.
  Proof.
    unfold Mem.valid_access in *. des. splits; auto.
    - unfold Mem.range_perm in *. i. eapply perm_wunchanged_on; eauto.
    - destruct cp. 2: ss. erewrite <- wunchanged_on_own; eauto. eapply Mem.can_access_block_valid_block; eauto.
  Qed.

  Lemma mem_free_list_wunchanged_on_2
        l m cp m'
        (FREE: Mem.free_list m l cp = Some m')
    :
    wunchanged_on (fun b _ => ~ In b (map (fun x => fst (fst x)) l)) m m'.
  Proof.
    revert_until l. induction l; ii.
    { ss. clarify. apply wunchanged_on_refl. }
    ss. des_ifs. eapply wunchanged_on_trans; cycle 1.
    { eapply wunchanged_on_implies. eapply IHl. eauto. ss. i. apply Classical_Prop.not_or_and in H. des. auto. }
    ss. eapply free_wunchanged_on. eapply Heq. ii. apply H0; clear H0. left; auto.
  Qed.

  Lemma not_global_blks_global_not_in
        (ge: genv) id b
        (FIND: Genv.find_symbol ge id = Some b)
        e
        (NGB: not_global_blks ge (blocks_of_env2 ge e))
    :
    ~ In b (map (fun x : block * Z * Z => fst (fst x)) (blocks_of_env ge e)).
  Proof.
    intros CONTRA. unfold not_global_blks in NGB. unfold blocks_of_env2, blocks_of_env in *.
    rewrite map_map in NGB, CONTRA. rewrite Forall_forall in NGB. specialize (NGB _ CONTRA).
    apply Genv.find_invert_symbol in FIND. setoid_rewrite FIND in NGB. inv NGB.
  Qed.

  Lemma mem_free_list_unchanged_on
        l m cp m'
        (FREE: Mem.free_list m l cp = Some m')
    :
    Mem.unchanged_on (fun b _ => ~ In b (map (fun x => fst (fst x)) l)) m m'.
  Proof.
    revert_until l. induction l; ii.
    { ss. clarify. apply Mem.unchanged_on_refl. }
    ss. des_ifs. eapply Mem.unchanged_on_trans; cycle 1.
    { eapply Mem.unchanged_on_implies. eapply IHl. eauto. ss. i. apply Classical_Prop.not_or_and in H. des. auto. }
    ss. eapply Mem.free_unchanged_on. eapply Heq. ii. apply H0; clear H0. left; auto.
  Qed.

  Lemma exists_vargs_vres
        (ge1: Senv.t) (ge2: genv)
        (MS: match_symbs ge1 ge2)
        ef m1 vargs tr vretv m2
        (EK: external_call_known_observables ef ge1 m1 vargs tr vretv m2)
        e cp le m_c
        (WFE: wf_env ge2 e)
    :
    (eval_exprlist ge2 e cp le m_c (list_eventval_to_list_expr (vals_to_eventvals ge1 vargs))
                   (list_typ_to_typelist (sig_args (ef_sig ef))) vargs) /\
      (external_call ef ge2 vargs m_c tr vretv m_c).
  Proof.
    pose proof MS as MS0. destruct MS as (MS1 & MS2 & MS3). move MS0 after MS1.
    unfold external_call_known_observables in *. des_ifs; ss; des. all: try (inv EK; clarify; ss).
    - inv H; clarify. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol; eauto. intros INV. rewrite INV.
      esplits.
      + econs. 3: econs. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. apply sem_cast_ptr.
      + econs. econs; auto. rewrite MS3; auto. eapply match_symbs_eventval_match; eauto.
    - inv H; clarify. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol; eauto. intros INV. rewrite INV.
      esplits.
      + econs. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. apply sem_cast_ptr.
        econs. 3: econs.
        { instantiate (1:=v). destruct v; ss; try (econs; fail).
          - destruct chunk; ss; inv H2; ss.
          - destruct Archi.ptr64 eqn:ARCH.
            + destruct chunk; ss; inv H2; ss; des_ifs.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H7. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
            + destruct chunk; ss; inv H2; ss; des_ifs.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H7. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
        }
        { rewrite EK1 in H2.
          destruct v; ss.
          - destruct chunk; ss; inv H2; ss.
          - destruct chunk; ss. all: simpl_expr. inv H2.
          - destruct chunk; ss. all: simpl_expr.
          - destruct chunk; ss. inv H2.
          - destruct chunk; ss. all: inv H2.
          - inv H2. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. apply H7. intros INV2. rewrite INV2.
            rewrite ptr_of_id_ofs_typeof. unfold Tptr. des_ifs; ss; simpl_expr.
            + unfold Cop.sem_cast. ss. rewrite Heq. auto.
            + unfold Cop.sem_cast. ss. rewrite Heq. auto.
        }
      + econs. econs; auto. rewrite MS3; auto. rewrite EK1.
        rewrite EK1 in H2. eapply match_symbs_eventval_match; eauto.
    - esplits.
      + erewrite eventval_list_match_vals_to_eventvals. 2: eapply H.
        erewrite <- eventval_list_match_list_eventval_to_list_val.
        2:{ eapply match_senv_eventval_list_match in H; eauto. }
        eapply list_eventval_to_expr_val_eval; auto. eapply eventval_list_match_transl.
        eapply match_senv_eventval_list_match; eauto.
      + econs. eapply match_senv_eventval_list_match; eauto.
    - esplits.
      + econs. 3: econs.
        * erewrite eventval_match_val_to_eventval. 2: eapply H. eapply eventval_to_expr_val_eval; auto.
          eapply match_senv_eventval_match; eauto.
        * erewrite eventval_match_val_to_eventval. 2: eapply H.
          erewrite eventval_match_eventval_to_val.
          2:{ eapply match_senv_eventval_match; eauto. }
          eapply eventval_match_sem_cast. eapply match_senv_eventval_match; eauto.
      + econs. eapply match_senv_eventval_match; eauto.
  Qed.

  Lemma eventval_list_match_eval_exprlist
        (ge: genv) args targs vargs
        (EMS: eventval_list_match ge args targs vargs)
        e cp le m
        (WF: wf_env ge e)
    :
    eval_exprlist ge e cp le m (list_eventval_to_list_expr args)
                  (list_eventval_to_typelist args) vargs.
  Proof.
    revert_until EMS. induction EMS; i; ss. econs.
    econs; auto.
    { clear dependent evl. clear tyl vl. inv H; try (simpl_expr; fail).
      ss. eapply ptr_of_id_ofs_eval; auto.
    }
    { clear dependent evl. clear tyl vl. inv H; ss; try (simpl_expr; fail).
      rewrite ptr_of_id_ofs_typeof. ss.
    }
  Qed.

  Lemma exists_vargs_vres_2
        (ge1: Senv.t) (ge2: genv)
        (MS: match_symbs ge1 ge2)
        ef m1 vargs tr vretv m2
        (EK: external_call_known_observables ef ge1 m1 vargs tr vretv m2)
        e cp le m_c
        (WFE: wf_env ge2 e)
    :
    exists vargs2 vretv2,
      (eval_exprlist ge2 e cp le m_c (list_eventval_to_list_expr (vals_to_eventvals ge1 vargs))
                     (list_eventval_to_typelist (vals_to_eventvals ge1 vargs)) vargs2) /\
        (external_call ef ge2 vargs2 m_c tr vretv2 m_c).
  Proof.
    pose proof MS as MS0. destruct MS as (MS1 & MS2 & MS3). move MS0 after MS1.
    unfold external_call_known_observables in *. des_ifs; ss; des. all: try (inv EK; clarify; ss).
    - inv H; clarify. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol; eauto. intros INV. rewrite INV.
      esplits.
      + econs. 3: econs. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. simpl_expr.
      + econs. econs; auto. rewrite MS3; auto. eapply match_symbs_eventval_match; eauto.
    - inv H; clarify. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol; eauto. intros INV. rewrite INV.
      esplits.
      + econs. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. simpl_expr.
        econs. 3: econs.
        { instantiate (1:=v). destruct v; ss; try (econs; fail).
          - destruct chunk; ss; inv H2; ss.
          - destruct Archi.ptr64 eqn:ARCH.
            + destruct chunk; ss; inv H2; ss; des_ifs.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H7. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
            + destruct chunk; ss; inv H2; ss; des_ifs.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
              * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H7. intros INV2. rewrite INV2.
                eapply ptr_of_id_ofs_eval; eauto.
        }
        { instantiate (1:=Val.load_result chunk v). rewrite EK1 in H2. rewrite EK1.
          destruct v; ss.
          - destruct chunk; ss; inv H2; ss.
          - destruct chunk; ss. all: simpl_expr.
          - destruct chunk; ss. all: simpl_expr.
          - inv H2. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. apply H7. intros INV2. rewrite INV2.
            rewrite ptr_of_id_ofs_typeof. simpl_expr.
        }
      + econs. econs; auto. rewrite MS3; auto. rewrite EK1. eapply match_symbs_eventval_match; eauto.
    - esplits.
      + erewrite eventval_list_match_vals_to_eventvals. 2: eapply H.
        eapply eventval_list_match_eval_exprlist; eauto.
        eapply match_senv_eventval_list_match; eauto.
      + econs. eapply match_senv_eventval_list_match; eauto.
    - esplits.
      + econs. 3: econs.
        * erewrite eventval_match_val_to_eventval. 2: eapply H. eapply eventval_to_expr_val_eval; auto.
          eapply match_senv_eventval_match; eauto.
        * inv H; ss; try (simpl_expr; fail). apply MS2 in H1. setoid_rewrite H1.
          rewrite ptr_of_id_ofs_typeof. ss.
      + econs. eapply match_senv_eventval_match; eauto.
  Qed.

  Lemma known_obs_preserves_mem
        ef ge m vargs tr vretv m'
        (EK: external_call_known_observables ef ge m vargs tr vretv m')
    :
    m' = m.
  Proof.
    unfold external_call_known_observables in EK. des_ifs; des; inv EK; clarify. inv H; clarify.
  Qed.

  Lemma meminj_first_order_public_first_order
        ge m
        (MFO: meminj_first_order (meminj_public ge) m)
    :
    public_first_order ge m.
  Proof.
    ii. apply MFO; auto. unfold meminj_public. apply Senv.find_invert_symbol in FIND.
    rewrite FIND. rewrite PUBLIC. ss.
  Qed.

  Lemma vals_public_eval_to_vargs
        (ge: genv) ef vargs
        (VP: vals_public ge (sig_args (ef_sig ef)) vargs)
        e cp le m
        (WFE: wf_env ge e)
    :
    eval_exprlist ge e cp le m
                  (list_eventval_to_list_expr (vals_to_eventvals ge vargs))
                  (list_typ_to_typelist (sig_args (ef_sig ef))) vargs.
  Proof.
    induction VP. ss. econs. ss. rename x into ty, y into v. econs. 3: auto.
    - clear dependent l. clear dependent l'.
      inv H; ss; try (simpl_expr; fail).
      destruct H0 as (id & BP1 & BP2).
      unfold senv_invert_symbol_total. rewrite BP1.
      apply ptr_of_id_ofs_eval; auto. apply Senv.invert_find_symbol; auto.
    - clear dependent l. clear dependent l'.
      inv H; ss; try (simpl_expr; fail).
      destruct H0 as (id & BP1 & BP2).
      unfold senv_invert_symbol_total. rewrite BP1.
      rewrite ptr_of_id_ofs_typeof. unfold Tptr. des_ifs; ss.
      + unfold Cop.sem_cast. ss. rewrite Heq. ss.
      + unfold Cop.sem_cast. ss. rewrite Heq. ss.
  Qed.

  Lemma vals_public_eval_to_vargs_2
        (ge: genv) ef vargs
        (VP: vals_public ge (sig_args (ef_sig ef)) vargs)
        e cp le m
        (WFE: wf_env ge e)
    :
    eval_exprlist ge e cp le m
                  (list_eventval_to_list_expr (vals_to_eventvals ge vargs))
                  (list_eventval_to_typelist (vals_to_eventvals ge vargs)) vargs.
  Proof.
    induction VP. ss. econs. ss. rename x into ty, y into v. econs. 3: auto.
    - clear dependent l. clear dependent l'.
      inv H; ss; try (simpl_expr; fail).
      destruct H0 as (id & BP1 & BP2).
      unfold senv_invert_symbol_total. rewrite BP1.
      apply ptr_of_id_ofs_eval; auto. apply Senv.invert_find_symbol; auto.
    - clear dependent l. clear dependent l'.
      inv H; ss; try (simpl_expr; fail).
      destruct H0 as (id & BP1 & BP2).
      unfold senv_invert_symbol_total. rewrite BP1.
      rewrite ptr_of_id_ofs_typeof. ss.
  Qed.

  Lemma match_symbs_block_public
        ge1 ge2
        (MS: match_symbs ge1 ge2)
        b
        (BP: block_public ge1 b)
    :
    block_public ge2 b.
  Proof.
    destruct MS as (MS1 & MS2 & MS3). destruct BP as (id & BP1 & BP2).
    apply Senv.invert_find_symbol in BP1. apply MS2 in BP1. rewrite <- MS1 in BP2.
    unfold block_public. esplits; eauto. apply Senv.find_invert_symbol; auto.
  Qed.

  Lemma match_symbs_vals_public
        ge1 ge2
        (MS: match_symbs ge1 ge2)
        tys vargs
        (VP: vals_public ge1 tys vargs)
    :
    vals_public ge2 tys vargs.
  Proof.
    induction VP; ss. econs; auto. clear VP IHVP. inv H; econs; auto.
    eapply match_symbs_block_public; eauto.
  Qed.

  Lemma match_symbs_vals_public_vals_to_eventvals
        ge1 ge2
        (MS: match_symbs ge1 ge2)
        tys vargs
        (VP: vals_public ge1 tys vargs)
    :
    vals_to_eventvals ge1 vargs = vals_to_eventvals ge2 vargs.
  Proof.
    induction VP; ss. f_equal; auto. clear dependent l. clear dependent l'.
    inv H; ss. destruct H0 as (id & BP1 & BP2).
    unfold senv_invert_symbol_total at 1. des_ifs.
    destruct MS as (MS0 & MS1 & MS2).
    apply Senv.invert_find_symbol in Heq. apply MS1 in Heq.
    unfold senv_invert_symbol_total at 1. apply Senv.find_invert_symbol in Heq.
    rewrite Heq. auto.
  Qed.

  Lemma match_symbs_vals_public_eval_to_vargs
        ge1 (ge2: genv)
        (MS: match_symbs ge1 ge2)
        ef vargs
        (VP: vals_public ge1 (sig_args (ef_sig ef)) vargs)
        e cp le m
        (WFE: wf_env ge2 e)
    :
    eval_exprlist ge2 e cp le m
                  (list_eventval_to_list_expr (vals_to_eventvals ge1 vargs))
                  (list_typ_to_typelist (sig_args (ef_sig ef))) vargs.
  Proof.
    erewrite match_symbs_vals_public_vals_to_eventvals; eauto.
    eapply vals_public_eval_to_vargs; auto. eapply match_symbs_vals_public; eauto.
  Qed.

  Lemma match_symbs_vals_public_eval_to_vargs_2
        ge1 (ge2: genv)
        (MS: match_symbs ge1 ge2)
        ef vargs
        (VP: vals_public ge1 (sig_args (ef_sig ef)) vargs)
        e cp le m
        (WFE: wf_env ge2 e)
    :
    eval_exprlist ge2 e cp le m
                  (list_eventval_to_list_expr (vals_to_eventvals ge1 vargs))
                  (list_eventval_to_typelist (vals_to_eventvals ge1 vargs)) vargs.
  Proof.
    erewrite match_symbs_vals_public_vals_to_eventvals; eauto.
    eapply vals_public_eval_to_vargs_2; auto. eapply match_symbs_vals_public; eauto.
  Qed.

  Lemma extcall_unkowns_vals_public
        ef ge m vargs
        (EC: external_call_unknowns ef ge m vargs)
    :
    vals_public ge (sig_args (ef_sig ef)) vargs.
  Proof.
    unfold external_call_unknowns in EC. des_ifs; ss; auto.
    all: destruct EC as (EC1 & EC2); auto.
  Qed.


  Lemma mem_unchanged_wunchanged
        P m m'
        (UCH: Mem.unchanged_on P m m')
    :
    wunchanged_on P m m'.
  Proof. inv UCH. econs; eauto. Qed.

  Lemma meminj_public_not_public_not_mapped
        ge cnt_cur
        (NP: Senv.public_symbol ge cnt_cur = false)
        cnt_cur_b
        (FIND: Senv.find_symbol ge cnt_cur = Some cnt_cur_b)
    :
    forall b ofs, meminj_public ge b <> Some (cnt_cur_b, ofs).
  Proof.
    ii. unfold meminj_public in H. des_ifs.
    assert (i = cnt_cur).
    { eapply Senv.find_symbol_injective; eauto. apply Senv.invert_find_symbol; auto. }
    subst i. rewrite NP in Heq0. ss.
  Qed.


  Lemma wunchanged_on_exists_mem_free_gen
        m1 b lo hi cp m2
        (FREE: Mem.free m1 b lo hi cp = Some m2)
        (P: block -> Prop) m_c
        (WCH: wunchanged_on (fun b _ => P b) m1 m_c)
        (NGB: P b)
    :
    exists m_c', Mem.free m_c b lo hi cp = Some m_c'.
  Proof.
    hexploit Mem.free_range_perm; eauto. hexploit Mem.free_can_access_block_1; eauto. i.
    hexploit Mem.range_perm_free.
    3:{ intros (m0 & F). eexists; eapply F. }
    - unfold Mem.range_perm in *. i. eapply perm_wunchanged_on. 3: eauto. eauto. ss.
    - rewrite <- wunchanged_on_own; eauto. eapply Mem.can_access_block_valid_block. eauto.
  Qed.

  Lemma wunchanged_on_exists_mem_free_2
        m1 b lo hi cp m2
        (FREE: Mem.free m1 b lo hi cp = Some m2)
        ge m_c
        (WCH: wunchanged_on (fun b _ => Senv.invert_symbol ge b = None) m1 m_c)
        (NGB: Senv.invert_symbol ge b = None)
    :
    exists m_c', Mem.free m_c b lo hi cp = Some m_c'.
  Proof. eapply wunchanged_on_exists_mem_free_gen; eauto. eapply WCH. ss. Qed.

  Lemma wunchanged_on_free_preserves_gen
        P m m'
        (WU : wunchanged_on P m m')
        b lo hi cp m1 m1'
        (FREE: Mem.free m b lo hi cp = Some m1)
        (FREE': Mem.free m' b lo hi cp = Some m1')
    :
    wunchanged_on P m1 m1'.
  Proof.
    inv WU. econs.
    - rewrite (Mem.nextblock_free _ _ _ _ _ _ FREE). rewrite (Mem.nextblock_free _ _ _ _ _ _ FREE'). auto.
    - i. assert (VB: Mem.valid_block m b0).
      { eapply Mem.valid_block_free_2; eauto. }
      split; i.
      + pose proof (Mem.perm_free_3 _ _ _ _ _ _ FREE _ _ _ _ H1). rewrite wunchanged_on_perm in H2; auto.
        eapply Mem.perm_free_inv in H2. 2: eauto. des; auto. clarify.
        hexploit Mem.perm_free_2. eapply FREE. split; eauto. i. exfalso. apply H2. eapply H1.
      + pose proof (Mem.perm_free_3 _ _ _ _ _ _ FREE' _ _ _ _ H1). rewrite <- wunchanged_on_perm in H2; auto.
        eapply Mem.perm_free_inv in H2. 2: eauto. des; auto. clarify.
        hexploit Mem.perm_free_2. eapply FREE'. split; eauto. i. exfalso. apply H2. eapply H1.
    - i. assert (VB: Mem.valid_block m b0).
      { eapply Mem.valid_block_free_2; eauto. }
      split; i.
      + eapply Mem.free_can_access_block_inj_1; eauto. apply wunchanged_on_own; auto.
        eapply Mem.free_can_access_block_inj_2; eauto.
      + eapply Mem.free_can_access_block_inj_1; eauto. apply wunchanged_on_own; auto.
        eapply Mem.free_can_access_block_inj_2; eauto.
  Qed.

  Lemma wunchanged_on_exists_mem_free_list_gen
        l m1 cp m2
        (FREE: Mem.free_list m1 l cp = Some m2)
        (P: block -> Prop) m_c
        (WCH: wunchanged_on (fun b _ => P b) m1 m_c)
        (NGB: Forall P (map (fun x => fst (fst x)) l))
    :
    exists m_c', Mem.free_list m_c l cp = Some m_c'.
  Proof.
    revert_until l. induction l; i; ss. eauto.
    destruct a as ((b & lo) & hi). ss. inv NGB. des_ifs; ss.
    2:{ exfalso. hexploit wunchanged_on_exists_mem_free_gen. 2: eapply WCH. all: eauto.
        intros. des. rewrite H in Heq; clarify.
    }
    hexploit IHl. eapply FREE. 2: eapply H2.
    { instantiate (1:=m). eapply wunchanged_on_free_preserves_gen; eauto. }
    eauto.
  Qed.

  Lemma wunchanged_on_exists_mem_free_list_2
        l m1 cp m2
        (FREE: Mem.free_list m1 l cp = Some m2)
        ge m_c
        (WCH: wunchanged_on (fun b _ => Senv.invert_symbol ge b = None) m1 m_c)
        (NGB: not_global_blks ge (map (fun x => fst (fst x)) l))
    :
    exists m_c', Mem.free_list m_c l cp = Some m_c'.
  Proof. eapply wunchanged_on_exists_mem_free_list_gen; eauto. ss. Qed.

  Lemma wunchanged_on_free_list_preserves_gen
        P m m'
        (WU: wunchanged_on P m m')
        l cp m_f m_f'
        (FREE: Mem.free_list m l cp = Some m_f)
        (FREE': Mem.free_list m' l cp = Some m_f')
    :
    wunchanged_on P m_f m_f'.
  Proof.
    move l after m. revert_until l. induction l; ii; ss. clarify.
    des_ifs. eapply IHl. 2,3: eauto. eapply wunchanged_on_free_preserves_gen; eauto.
  Qed.

  Lemma meminj_not_alloc_external_call
        j m1
        (NA: meminj_not_alloc j m1)
        ef ge vargs tr vretv m2
        (EC: external_call ef ge vargs m1 tr vretv m2)
    :
    meminj_not_alloc j m2.
  Proof.
    unfold meminj_not_alloc in *. i. apply NA. clear NA.
    eapply external_call_nextblock in EC. etransitivity. 2: eapply H. auto.
  Qed.

  Lemma public_first_order_meminj_first_order
        (ge: Senv.t) m
        (FO: public_first_order ge m)
    :
    meminj_first_order (meminj_public ge) m.
  Proof.
    ii. unfold meminj_public in H. des_ifs. eapply FO; eauto.
    apply Senv.invert_find_symbol; auto.
  Qed.

  Lemma list_length_filter_le
        A P (l: list A)
    :
    (Datatypes.length (filter P l) <= Datatypes.length l)%nat.
  Proof.
    induction l; ss. des_ifs; ss; auto. rewrite <- Nat.succ_le_mono. auto.
  Qed.

End PROOF.
