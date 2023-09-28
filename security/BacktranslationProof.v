Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import Tactics.
Require Import riscV.Asm.
Require Import BtBasics BtInfoAsm MemoryDelta MemoryWeak.
Require Import Ctypes Clight.
Require Import Backtranslation BacktranslationAux.



Section INVS.

  Definition cnt_ids := PTree.t ident.

  Definition wf_counter (ge: Senv.t) (m: mem) cp (n: nat) (cnt: ident): Prop :=
    (Senv.public_symbol ge cnt = false) /\
      exists b, (Senv.find_symbol ge cnt = Some b) /\
             (Mem.valid_access m Mint64 b 0 Writable (Some cp)) /\
             (Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (nat64 n))).

  Definition wf_counters (ge_a: Asm.genv) (ge: Clight.genv) (m: mem) (tr: bundle_trace) (cnts: cnt_ids) :=
    (forall id0 id1 cnt, (cnts ! id0 = Some cnt) -> (cnts ! id1 = Some cnt) -> (id0 = id1)) /\
      (forall id b gd,
          (Genv.find_symbol ge_a id = Some b) ->
          (Genv.find_def ge_a b = Some gd) ->
          (exists cnt, (cnts ! id = Some cnt) /\
                    (wf_counter ge m (comp_of gd) (length (get_id_tr tr id)) cnt))).
  (* Definition wf_counters (ge: Clight.genv) (m: mem) (tr: bundle_trace) (cnts: cnt_ids) := *)
  (*   (forall id0 id1 cnt, (cnts ! id0 = Some cnt) -> (cnts ! id1 = Some cnt) -> (id0 = id1)) /\ *)
  (*     (forall id b (f: function), *)
  (*         (Genv.find_symbol ge id = Some b) -> (Genv.find_funct_ptr ge b = Some (Internal f)) -> *)
  (*         (exists cnt, (cnts ! id = Some cnt) /\ (wf_counter ge m (comp_of f) (length (get_id_tr tr id)) cnt))). *)

  Inductive wf_c_cont (ge: Clight.genv) : mem -> cont -> Prop :=
  | wf_c_cont_nil
      m
    :
    wf_c_cont ge m Kstop
  | wf_c_cont_cons
      m ck
      f e le s1 s2 m' ck'
      (WFENV: wf_env ge e)
      (NINJ: not_global_blks (ge) (blocks_of_env2 ge e))
      (CK: ck = Kcall None f e le (Kloop1 s1 s2 ck'))
      (FREE: Mem.free_list m (blocks_of_env ge e) (comp_of f) = Some m')
      (IND: wf_c_cont ge m' ck')
    :
    wf_c_cont ge m ck.

  Definition wf_c_stmt (ge: Senv.t) cp cnts id tr stmt :=
    forall cnt, (cnts ! id = Some cnt) -> stmt = code_bundle_trace ge cp cnt (get_id_tr tr id).

  Definition wf_c_nb (ge: Clight.genv) (m: mem) :=
    (Genv.genv_next ge <= Mem.nextblock m)%positive.

  Definition wf_c_state ge_a (ge: Clight.genv) (tr ttr: bundle_trace) (cnts: cnt_ids) id (cst: Clight.state) :=
    match cst with
    | State f stmt k_c e le m_c =>
        wf_counters ge_a ge m_c tr cnts /\
          (exists m_c', Mem.free_list m_c (blocks_of_env ge e) (comp_of f) = Some m_c' /\ wf_c_cont ge m_c' k_c) /\
          wf_c_stmt ge (comp_of f) cnts id ttr stmt /\
          (wf_env ge e /\ (not_global_blks (ge) (blocks_of_env2 ge e)) /\ (wf_c_nb ge m_c))
    | _ => False
    end.
  (* Definition wf_c_state (ge: Clight.genv) (tr ttr: bundle_trace) (cnts: cnt_ids) id (cst: Clight.state) := *)
  (*   match cst with *)
  (*   | State f stmt k_c e le m_c => *)
  (*       wf_counters ge m_c tr cnts /\ *)
  (*         (exists m_c', Mem.free_list m_c (blocks_of_env ge e) (comp_of f) = Some m_c' /\ wf_c_cont ge m_c' k_c) /\ *)
  (*         wf_c_stmt ge (comp_of f) cnts id ttr stmt /\ *)
  (*         (wf_env ge e /\ (not_global_blks (ge) (blocks_of_env2 ge e)) /\ (wf_c_nb ge m_c)) *)
  (*   | _ => False *)
  (*   end. *)

  Definition match_genv (ge: Asm.genv) (ge': genv) :=
    (match_symbs ge ge') /\ (eq_policy ge ge').

  Definition match_mem (ge: Senv.t) (k: meminj) (m_i m_c: mem): Prop :=
    let j := meminj_public ge in
    (Mem.inject k m_i m_c) /\ (inject_incr j k) /\ (meminj_not_alloc j m_i).

  Definition match_cur_fun (ge_i: Asm.genv) (ge_c: genv) (cur: block) f (id: ident): Prop :=
    (Genv.find_funct_ptr ge_c cur = Some (Internal f)) /\
      (exists f_i, Genv.find_funct_ptr ge_i cur = Some (AST.Internal f_i)) /\
      (Genv.invert_symbol ge_i cur = Some id).

  Definition match_find_def (ge_i: Asm.genv) (ge_c: Clight.genv) (cnts: cnt_ids) (pars: params_of) tr :=
    forall b gd_i id,
      Genv.find_def ge_i b = Some gd_i ->
      Senv.invert_symbol ge_i b = Some id ->
      match (cnts ! id), (pars ! id) with
      | Some cnt, Some params =>
          Genv.find_def ge_c b = Some (gen_globdef ge_i cnt params (get_id_tr tr id) gd_i)
      | _, _ => False
      end.

  Inductive match_cont (ge: Clight.genv) (tr: bundle_trace) (cnts: cnt_ids) : (cont) -> (ir_conts) -> Prop :=
  | match_cont_nil
      ck ik
      (CK: ck = Kstop)
      (IK: ik = nil)
    :
    match_cont ge tr cnts ck ik
  | match_cont_cons
      ck ik
      f e le cnt id ck'
      b ik'
      (FUN: Genv.find_funct_ptr ge b = Some (Internal f))
      (ID: Genv.invert_symbol ge b = Some id)
      (CNT: cnts ! id = Some cnt)
      (CK: ck = Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge cnt (comp_of f) (get_id_tr tr id))) Sskip ck'))
      (IK: ik = (ir_cont b) :: ik')
      (IND: match_cont ge tr cnts ck' ik')
    :
    match_cont ge tr cnts ck ik.

  Definition match_params pars (ge_c: genv) (ge_i: Asm.genv) :=
    (wf_params_of pars) /\ (wf_params_of_sig pars ge_i) /\ (wf_params_of_symb pars ge_c).

  Definition match_cnts cnts (ge_c: genv) (k: meminj) :=
    forall id cnt cnt_b, (cnts ! id = Some cnt) -> (Genv.find_symbol ge_c cnt = Some cnt_b) ->
                    (forall b ofs, k b <> Some (cnt_b, ofs)).

  Definition match_state (ge_i: Asm.genv) (ge_c: Clight.genv) (k: meminj) tr cnts pars id (ist: ir_state) (cst: Clight.state) :=
    match ist, cst with
    | Some (cur, m_i, k_i), State f _ k_c e le m_c =>
        (match_genv ge_i ge_c) /\ (match_mem ge_i k m_i m_c) /\
          (match_cur_fun ge_i ge_c cur f id) /\ (match_find_def ge_i ge_c cnts pars tr) /\
          (match_cont ge_c tr cnts k_c k_i) /\
          (match_params pars ge_c ge_i) /\
          (match_cnts cnts ge_c k)
    | _, _ => False
    end.

End INVS.



Section PROOF.

  Lemma cur_fun_def
        ge_i (ge_c: genv) cur f (f_i_cur : Asm.function) id_cur cnts pars ttr
        (FINDF_C_CUR : Genv.find_funct_ptr ge_c cur = Some (Internal f))
        (FINDF_I_CUR : Genv.find_funct_ptr ge_i cur = Some (AST.Internal f_i_cur))
        (INV_CUR : Genv.invert_symbol ge_i cur = Some id_cur)
        (MS3 : match_find_def ge_i ge_c cnts pars ttr)
    :
    exists cnt_cur params_cur,
      (cnts ! id_cur = Some cnt_cur) /\ (pars ! id_cur = Some params_cur) /\
        (f = gen_function ge_i cnt_cur params_cur (get_id_tr ttr id_cur) f_i_cur).
  Proof.
    exploit MS3. eapply Genv.find_funct_ptr_iff. eauto. eapply INV_CUR. intros. des_ifs.
    esplits; eauto. apply Genv.find_funct_ptr_iff in FINDF_C_CUR.
    setoid_rewrite FINDF_C_CUR in x0. unfold gen_globdef in x0. clarify.
  Qed.

  Lemma wf_c_cont_wunchanged_on
        ge m k
        (WFC: wf_c_cont ge m k)
        m'
        (WU: wunchanged_on (fun b _ => Mem.valid_block m b) m m')
    :
    wf_c_cont ge m' k.
  Proof.
    revert_until WFC. induction WFC; ii. econs.
    clarify.
    hexploit wunchanged_on_exists_mem_free_list. eapply WU. eapply FREE. intros (m_f & FREE2).
    econs. 1,2,3: eauto. eapply FREE2. eapply IHWFC.
    eapply wunchanged_on_free_list_preserves. eapply WU. all: eauto.
  Qed.

  Lemma star_cut_middle
        stepk ge_a ge_c cst1 ev pretr ttr cnts ge_i pars ist2
        (CUT: exists tr1 cst',
            (star stepk ge_c cst1 tr1 cst') /\
              exists tr2 cst2,
                (star stepk ge_c cst' tr2 cst2) /\
                  ((exists id', (wf_c_state ge_a ge_c (pretr ++ [ev]) ttr cnts id' cst2) /\
                             exists k, (match_state ge_i ge_c k ttr cnts pars id' ist2 cst2))
                   \/ (ist2 = None)) /\
                  (unbundle ev = tr1 ++ tr2))
    :
    exists cst2, (star stepk ge_c cst1 (unbundle ev) cst2) /\
              ((exists id', (wf_c_state ge_a ge_c (pretr ++ [ev]) ttr cnts id' cst2) /\
                         exists k, (match_state ge_i ge_c k ttr cnts pars id' ist2 cst2))
               \/ (ist2 = None)).
  Proof.
    destruct CUT as (tr1 & cts' & STAR1 & tr2 & cst2 & STAR2 & PROP & TR).
    exists cst2. split; auto. eapply star_trans. eapply STAR1. eapply STAR2. auto.
  Qed.

  Lemma mem_inject_incr_match_cnts_rev
        k1 k2
        (INCR: inject_incr k1 k2)
        cnts ge
        (MC: match_cnts cnts ge k2)
    :
    match_cnts cnts ge k1.
  Proof.
    unfold match_cnts in *. i. specialize (MC _ _ _ H H0 b ofs). ii. apply MC; clear MC. apply INCR. auto.
  Qed.

  Lemma wf_c_cont_wunchanged_on_2
        ge m k
        (WF: wf_c_cont ge m k)
        m'
        (WCH: wunchanged_on (fun b _ => Senv.invert_symbol ge b = None) m m')
    :
    wf_c_cont ge m' k.
  Proof.
    revert_until WF. induction WF; i; ss. econs.
    clarify. hexploit wunchanged_on_exists_mem_free_list_2.
    eapply FREE. instantiate (2:=ge). eapply WCH. auto.
    intros (m_c' & FREE2).
    econs. eauto. auto. eauto. eapply FREE2. eapply IHWF.
    eapply wunchanged_on_free_list_preserves_gen. 2,3: eauto. auto.
  Qed.

  Lemma wf_c_nb_wunchanged_on
        P m1 m2
        (WCH: wunchanged_on P m1 m2)
        ge
        (WFNB: wf_c_nb ge m1)
    :
    wf_c_nb ge m2.
  Proof.
    unfold wf_c_nb in *. hexploit wunchanged_on_nextblock. eapply WCH.
    intros. etransitivity. eapply WFNB. auto.
  Qed.



  Lemma ir_to_clight_step_cce_1
        (ge_i: Asm.genv) (ge_c: genv)
        (WFGE : wf_ge ge_i)
        cnts pars k_i cur m_i pretr btr (tr tr' : trace) id0 evargs ef id_cur d
        (BOUND : Z.of_nat
                   (Datatypes.length
                      (pretr ++ (id_cur, Bundle_call tr' id0 evargs (ef_sig ef) d) :: btr)) <
                   Int64.modulus)
        k_c id f stmt k0 e le m_c
        (MS0 : match_genv ge_i ge_c)
        (MS1 : match_mem ge_i k_c m_i m_c)
        (MS2 : match_cur_fun ge_i ge_c cur f id)
        (MS4 : match_cont ge_c (pretr ++ (id_cur, Bundle_call tr' id0 evargs (ef_sig ef) d) :: btr) cnts
                          k0 k_i)
        (MS3 : match_find_def ge_i ge_c cnts pars
                              (pretr ++ (id_cur, Bundle_call tr' id0 evargs (ef_sig ef) d) :: btr))
        (MS5 : match_params pars ge_c ge_i)
        (MCNTS : match_cnts cnts ge_c k_c)
        (CNT_INJ : forall (id0 id1 : positive) (cnt : ident),
            cnts ! id0 = Some cnt -> cnts ! id1 = Some cnt -> id0 = id1)
        (WFC0 : forall (id : ident) (b : block) gd,
            Genv.find_symbol ge_i id = Some b ->
            Genv.find_def ge_i b = Some gd ->
            exists cnt : ident,
              cnts ! id = Some cnt /\
                wf_counter ge_c m_c (comp_of gd) (Datatypes.length (get_id_tr pretr id)) cnt)
        m_freeenv
        (FREEENV : Mem.free_list m_c (blocks_of_env ge_c e) (comp_of f) = Some m_freeenv)
        (WFC1 : wf_c_cont ge_c m_freeenv k0)
        (WFC2 : wf_c_stmt ge_c (comp_of f) cnts id
                          (pretr ++ (id_cur, Bundle_call tr' id0 evargs (ef_sig ef) d) :: btr) stmt)
        (WFC3 : wf_env ge_c e)
        (WFC4 : not_global_blks ge_c (blocks_of_env2 ge_c e))
        (WFNB : wf_c_nb ge_c m_c)
        vargs b
        (FINDB : Genv.find_symbol ge_i id0 = Some b)
        (FINDF : Genv.find_funct ge_i (Vptr b Ptrofs.zero) = Some (AST.External ef))
        (NPTR : crossing_comp ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) (comp_of ef) ->
                Forall not_ptr vargs)
        (ALLOW : Genv.allowed_call ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))
                                   (Vptr b Ptrofs.zero))
        (TR : call_trace_cross ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) 
                               (comp_of ef) b vargs (sig_args (ef_sig ef)) tr id0 evargs)
        (IDCUR : Genv.invert_symbol ge_i cur = Some id_cur)
        m2
        (DELTA: mem_delta_apply_wf ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) d (Some m_i) = Some m2)
        (DELTA_CASES: (public_first_order ge_i m2) \/ (d = []))
        (TR_APP: exists tr0, tr' = tr ++ tr0)
    :
    exists cnt_cur cnt_cur_b,
      (cnts ! id_cur = Some cnt_cur /\ Senv.find_symbol ge_c cnt_cur = Some cnt_cur_b /\ Senv.public_symbol ge_c cnt_cur = false) /\
        let dsg := from_sig_fun_data (ef_sig ef) in
        let fd_next := (External ef (dargs dsg) (dret dsg) (dcc dsg)) in
        exists m_c',
          (star step1 ge_c (State f stmt k0 e le m_c)
                (tr)
                (Callstate fd_next vargs
                           (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr (pretr ++ (id_cur, Bundle_call tr' id0 evargs (ef_sig ef) d) :: btr) id_cur))) Sskip k0)) m_c'))
          /\
            (exists m_cu,
                (Mem.storev Mint64 m_c (Vptr cnt_cur_b Ptrofs.zero) (Vlong (Int64.add (nat64 (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr pretr id_cur)))) Int64.one)) (comp_of f) = Some m_cu) /\
                  (d = [] -> m_c' = m_cu) /\
                  ((public_first_order ge_i m2) ->
                   (mem_delta_apply_wf ge_i (comp_of f) d (Some m_cu) = Some m_c') /\
                     (Mem.inject (meminj_public ge_i) m2 m_c')))
  .
  Proof.
    assert (id = id_cur).
    { unfold match_cur_fun in MS2. desH MS2. rewrite MS7 in IDCUR. clarify. }
    subst id.
    destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).

    exploit MS3.
    { eapply Genv.find_funct_ptr_iff. erewrite <- Genv.find_funct_find_funct_ptr. eapply FINDF. }
    { eapply Genv.find_invert_symbol; eauto. }
    intros FINDF_C. des_ifs. rename id0 into id_next, i into cnt_next, Heq into CNTS_NEXT, l into params_next, Heq0 into PARS_NEXT. simpl in FINDF_C.
    set (pretr ++ (id_cur, Bundle_call tr' id_next evargs (ef_sig ef) d) :: btr) as ttr in *.
    assert (FIND_CUR_I: Genv.find_symbol ge_i id_cur = Some cur).
    { apply Genv.invert_find_symbol in IDCUR. auto. }
    assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
    { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1 in FIND_CUR_I. auto. }
    assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
    { auto. }

    exploit WFC0. eapply FIND_CUR_I. rewrite <- Genv.find_funct_ptr_iff; eapply FINDF_I_CUR.
    intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
    destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).
    exists cnt_cur, cnt_cur_b. split. auto.
    set (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)) as kc_next.
    assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_call tr' id_next evargs (ef_sig ef) d) :: (get_id_tr btr id_cur)).
    { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
    assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
    { rewrite map_length. eapply Z.le_lt_trans. 2: eauto. unfold get_id_tr.
      apply inj_le. apply list_length_filter_le.
    }

    hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply IDCUR. eauto.
    intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
    rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
    assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
    { unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss. }
    assert (COMP_CUR_EQ: comp_of (@Gfun _ unit (AST.Internal f_i_cur)) = comp_of f).
    { subst f. ss. }
    setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_VA. setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_LOAD.

    hexploit switch_spec.
    { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
    { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3. }
    eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
    { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
    instantiate (1:=le).
    instantiate (1:=(Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)).
    instantiate (1:=Sreturn None).
    intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).

    assert (DELTA_C: exists m_c',
               (mem_delta_apply_wf ge_i (comp_of f) d (Some m_cu) = Some m_c') /\
                 (((public_first_order ge_i m2) -> (Mem.inject (meminj_public ge_i) m2 m_c')))).
    { move MS1 after CUR_SWITCH_STAR. destruct MS1 as (MINJ & INJINCR & NALLOC).
      move DELTA after NALLOC.
      hexploit mem_delta_apply_establish_inject_preprocess_gen.
      apply MINJ. eapply CNT_CUR_STORE.
      { instantiate (1:=ge_i). erewrite match_symbs_meminj_public. 2: destruct MS0 as (MS & _); apply MS.
        ii. eapply meminj_public_not_public_not_mapped. 3: apply H. 2: eauto. auto.
      }
      apply INJINCR. apply NALLOC. apply DELTA.
      intros (m_c' & DELTA' & INJ'). exists m_c'. splits; auto.
      rewrite CP_CUR. auto. i. apply INJ'. apply public_first_order_meminj_first_order; auto.
    }
    desH DELTA_C. rename DELTA_C0 into MEMINJ_CNT.

    exists m_c'. split; cycle 1.
    { exists m_cu. split; auto. split.
      - i. subst d. unfold mem_delta_apply_wf in DELTA_C. ss. clarify.
      - i. split; auto.
    }

    unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
    eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
    unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
    rewrite ! (match_symbs_code_bundle_call ge_i ge_c) in CUR_SWITCH_STAR.
    rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
    eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: apply MS0.
    clear BOUND2 CUR_SWITCH_STAR.
    unfold code_bundle_call. eapply star_trans. eapply code_mem_delta_correct. auto.
    { erewrite <- match_symbs_mem_delta_apply_wf. eapply DELTA_C. apply MS0. }
    2: ss.
    unfold unbundle. simpl. rename b into next.

    assert (CP_NEXT: (Genv.find_comp ge_c (Vptr next Ptrofs.zero)) = (comp_of ef)).
    { unfold Genv.find_comp. apply Genv.find_funct_ptr_iff in FINDF_C. setoid_rewrite FINDF_C. ss. }
    assert (EVARGS: list_eventval_to_list_val ge_c evargs = vargs).
    { destruct MS0 as (MSENV & MGENV). inv TR.
      eapply eventval_list_match_list_eventval_to_list_val. eapply match_symbs_eventval_list_match; eauto.
    }

    econs 2.
    { eapply step_call. ss.
      { econs. assert (FSN_C: Senv.find_symbol ge_c id_next = Some next).
        { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1. auto. }
        eapply eval_Evar_global.
        - unfold wf_env in WFC3. specialize (WFC3 id_next). rewrite FSN_C in WFC3. apply WFC3.
        - eapply FSN_C.
        - econs 2. ss.
      }
      { eapply list_eventval_to_expr_val_eval. auto. inv TR. eapply eventval_list_match_transl. eapply match_senv_eventval_list_match; eauto. destruct MS0 as (MSENV & _); auto. }
      { unfold match_find_def in MS3. hexploit MS3.
        unfold Genv.find_funct in FINDF. rewrite pred_dec_true in FINDF; auto. unfold Genv.find_funct_ptr in FINDF. des_ifs. eapply Heq.
        eapply Senv.find_invert_symbol; eapply FINDB.
        rewrite CNTS_NEXT, PARS_NEXT. intros. unfold Genv.find_funct. rewrite pred_dec_true. unfold Genv.find_funct_ptr. rewrite H. ss. ss.
      }
      { ss. }
      { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV).
        subst f. setoid_rewrite CP_CUR. move ALLOW after EVARGS.
        eapply allowed_call_gen_function_external; eauto.
        setoid_rewrite Genv.find_funct_ptr_iff. auto.
      }
      { move NPTR after EVARGS. move TR after NPTR. i.
        rewrite EVARGS. apply NPTR. unfold crossing_comp. rewrite <- H.
        setoid_rewrite CP_CUR. rewrite CP_NEXT. auto.
      }
      { move TR after EVARGS. instantiate (1:=tr). inv TR.
        setoid_rewrite CP_CUR. rewrite CP_NEXT.
        econs 2.
        { rewrite <- H. ss. }
        eauto.
        { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.find_invert_symbol. apply MSENV1. auto. }
        { eapply eventval_list_match_transl. eapply match_senv_eventval_list_match; eauto. destruct MS0 as (MSENV & _); auto. }
      }
    }
    { rewrite EVARGS. subst kc_next. econs 1. }
    traceEq.
  Qed.

  Lemma ir_to_clight_step_cce_2
        (ge_i: Asm.genv) (ge_c: genv)
        (WFGE : wf_ge ge_i)
        cnts pars k_i cur m_i pretr btr (tr1 tr2 tr' : trace) id0 vargs ef id_cur d
        (BOUND : Z.of_nat
                   (Datatypes.length
                      (pretr ++ (id_cur, Bundle_call tr' id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr)) <
                   Int64.modulus)
        k_c id f stmt k0 e le m_c
        (MS0 : match_genv ge_i ge_c)
        (MS1 : match_mem ge_i k_c m_i m_c)
        (MS2 : match_cur_fun ge_i ge_c cur f id)
        (MS4 : match_cont ge_c (pretr ++ (id_cur, Bundle_call tr' id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr) cnts k0 k_i)
        (MS3 : match_find_def ge_i ge_c cnts pars (pretr ++ (id_cur, Bundle_call tr' id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr))
        (MS5 : match_params pars ge_c ge_i)
        (MCNTS : match_cnts cnts ge_c k_c)
        (CNT_INJ : forall (id0 id1 : positive) (cnt : ident),
            cnts ! id0 = Some cnt -> cnts ! id1 = Some cnt -> id0 = id1)
        (WFC0 : forall (id : ident) (b : block) gd,
            Genv.find_symbol ge_i id = Some b ->
            Genv.find_def ge_i b = Some gd ->
            exists cnt : ident,
              cnts ! id = Some cnt /\
                wf_counter ge_c m_c (comp_of gd) (Datatypes.length (get_id_tr pretr id)) cnt)
        m_freeenv
        (FREEENV : Mem.free_list m_c (blocks_of_env ge_c e) (comp_of f) = Some m_freeenv)
        (WFC1 : wf_c_cont ge_c m_freeenv k0)
        (WFC2 : wf_c_stmt ge_c (comp_of f) cnts id
                          (pretr ++ (id_cur, Bundle_call tr' id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr) stmt)
        (WFC3 : wf_env ge_c e)
        (WFC4 : not_global_blks ge_c (blocks_of_env2 ge_c e))
        (WFNB : wf_c_nb ge_c m_c)
        b
        (FINDB : Genv.find_symbol ge_i id0 = Some b)
        (FINDF : Genv.find_funct ge_i (Vptr b Ptrofs.zero) = Some (AST.External ef))
        (NPTR : crossing_comp ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) (comp_of ef) ->
                Forall not_ptr vargs)
        (ALLOW : Genv.allowed_call ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))
                                   (Vptr b Ptrofs.zero))
        (m1' m2 : mem)
        (vretv : val)
        (DELTA : mem_delta_apply_wf ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) d (Some m_i) = Some m1')
        (TR1 : call_trace_cross ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))
                                (comp_of ef) b vargs (sig_args (ef_sig ef)) tr1 id0 (vals_to_eventvals ge_i vargs))
        (TR2 : external_call ef ge_i vargs m1' tr2 vretv m2)
        (ECCASES : external_call_unknowns ef ge_i m1' vargs \/
                     external_call_known_observables ef ge_i m1' vargs tr2 vretv m2 /\ d = [])
        (IDCUR : Genv.invert_symbol ge_i cur = Some id_cur)
        (TR_APP: exists tr0, tr' = tr1 ++ tr2 ++ tr0)
    :
    exists cnt_cur cnt_cur_b,
      (cnts ! id_cur = Some cnt_cur /\ Senv.find_symbol ge_c cnt_cur = Some cnt_cur_b /\ Senv.public_symbol ge_c cnt_cur = false) /\
        let dsg := from_sig_fun_data (ef_sig ef) in
        exists m_c',
          (exists vres m_next,
              (star step1 ge_c (State f stmt k0 e le m_c)
                    (tr1 ++ tr2)
                    (Returnstate vres (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr (pretr ++ (id_cur, Bundle_call tr' id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr) id_cur))) Sskip k0)) m_next (rettype_of_type (dret dsg)) (comp_of ef))) /\
                (external_call ef ge_c vargs m_c' tr2 vres m_next))
          /\
            (exists m_cu,
                (Mem.storev Mint64 m_c (Vptr cnt_cur_b Ptrofs.zero) (Vlong (Int64.add (nat64 (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr pretr id_cur)))) Int64.one)) (comp_of f) = Some m_cu) /\
                  (d = [] -> m_c' = m_cu) /\
                  ((public_first_order ge_i m1') ->
                   (mem_delta_apply_wf ge_i (comp_of f) d (Some m_cu) = Some m_c') /\
                     (Mem.inject (meminj_public ge_i) m1' m_c')))
  .
  Proof.
    hexploit ir_to_clight_step_cce_1; eauto.
    { desH ECCASES; [left | right; auto]. apply external_call_unknowns_fo in ECCASES.
      apply meminj_first_order_public_first_order; auto.
    }
    { desH TR_APP. eauto. }
    instantiate (1:=le).
    intros (cnt_cur & cnt_cur_b & (CNT_CUR & FIND_CNT & CNT_CUR_NP) & m_c' & STAR & MEM).
    destruct MEM as (m_cu & CNT_CUR_STORE & DELTA_NIL & DELTA_PUB).
    exists cnt_cur, cnt_cur_b. split; auto. ss. exists m_c'. split.
    2:{ exists m_cu. splits; auto. }
    desH ECCASES; cycle 1.

    (* Case 1: observable defined external calls *)
    { clear DELTA_PUB. subst d. specialize (DELTA_NIL eq_refl). subst m_c'.
      unfold mem_delta_apply_wf in DELTA. simpl in DELTA. inversion DELTA; clear DELTA. subst m1'.
      hexploit exists_vargs_vres. eapply MS0. eapply ECCASES. eauto. intros (EVALS & EXT2).
      esplits. 2: eapply EXT2.
      eapply star_trans. eapply STAR.
      { econs 2. eapply step_external_function. eapply EXT2. econs 1. ss. }
      { traceEq. }
    }

    (* Case 2: observable defined external calls *)
    { clear DELTA_NIL.
      hexploit external_call_unknowns_fo. eapply ECCASES. intros FO_I.
      hexploit external_call_unknowns_val_inject_list. eapply ECCASES. intros ARGS_INJ.
      hexploit meminj_first_order_public_first_order. apply FO_I. intros PFO.
      specialize (DELTA_PUB PFO). desH DELTA_PUB.
      move MS1 after ARGS_INJ. destruct MS1 as (MM0 & MM1 & MM2).
      hexploit external_call_mem_inject_gen.
      { eapply match_symbs_symbols_inject. apply MS0. }
      apply TR2. apply DELTA_PUB0. apply ARGS_INJ.
      intros (j2 & vres2 & m_next & EC2 & RET_INJ & INJ2 & UCH0 & UCH1 & INCR2 & INJ_SEP).
      exists vres2, m_next. split; [|auto]. eapply star_trans. eapply STAR.
      { econs 2. eapply step_external_function. eapply EC2. econs 1. ss. }
      traceEq.
      Unshelve. exact 1%positive. exact le.
    }
  Qed.

  Lemma val_inject_not_ptr
        k v1 v2
        (VI: Val.inject k v1 v2)
        (NPTR: not_ptr v1)
    :
    not_ptr v2.
  Proof. inv VI; auto. ss. Qed.

  Lemma not_ptr_val_inject_eq
        j v1 v2
        (VI: Val.inject j v1 v2)
        (NPTR: not_ptr v1)
    :
    v1 = v2.
  Proof. inv VI; ss. Qed.

  Lemma ir_to_clight_step_1
        ge_i ge_c
        (WFGE : wf_ge ge_i)
        cnts pars k_i cur m_i
        pretr btr
        tr id0 evargs f_next d id_cur
        (BOUND : Z.of_nat
                   (Datatypes.length
                      (pretr ++ (id_cur, Bundle_call tr id0 evargs (fn_sig f_next) d) :: btr)) <
                   Int64.modulus)
        k_c id f stmt k0 e le m_c
        (MS0 : match_genv ge_i ge_c)
        (MS1 : match_mem ge_i k_c m_i m_c)
        (MS2 : match_cur_fun ge_i ge_c cur f id)
        (MS4 : match_cont ge_c (pretr ++ (id_cur, Bundle_call tr id0 evargs (fn_sig f_next) d) :: btr)
                          cnts k0 k_i)
        (MS3 : match_find_def ge_i ge_c cnts pars
                              (pretr ++ (id_cur, Bundle_call tr id0 evargs (fn_sig f_next) d) :: btr))
        (MS5 : match_params pars ge_c ge_i)
        (MCNTS : match_cnts cnts ge_c k_c)
        (CNT_INJ : forall (id0 id1 : positive) (cnt : ident),
            cnts ! id0 = Some cnt -> cnts ! id1 = Some cnt -> id0 = id1)
        (WFC0 : forall (id : ident) (b : block) gd,
            Genv.find_symbol ge_i id = Some b ->
            Genv.find_def ge_i b = Some gd ->
            exists cnt : ident,
              cnts ! id = Some cnt /\
                wf_counter ge_c m_c (comp_of gd) (Datatypes.length (get_id_tr pretr id)) cnt)
        m_freeenv
        (FREEENV : Mem.free_list m_c (blocks_of_env ge_c e) (comp_of f) = Some m_freeenv)
        (WFC1 : wf_c_cont ge_c m_freeenv k0)
        (WFC2 : wf_c_stmt ge_c (comp_of f) cnts id
                          (pretr ++ (id_cur, Bundle_call tr id0 evargs (fn_sig f_next) d) :: btr) stmt)
        (WFC3 : wf_env ge_c e)
        (WFC4 : not_global_blks ge_c (blocks_of_env2 ge_c e))
        (WFNB : wf_c_nb ge_c m_c)
        vargs b m2
        (FINDB : Genv.find_symbol ge_i id0 = Some b)
        (FINDF : Genv.find_funct ge_i (Vptr b Ptrofs.zero) = Some (AST.Internal f_next))
        (NPTR : crossing_comp ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) (comp_of f_next) ->
                Forall not_ptr vargs)
        (ALLOW : Genv.allowed_call ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))
                                   (Vptr b Ptrofs.zero))
        (DELTA : mem_delta_apply_wf ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) d (Some m_i) =
                   Some m2)
        (TR : call_trace_cross ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) 
                               (comp_of f_next) b vargs (sig_args (fn_sig f_next)) tr id0 evargs)
        (PUB : public_first_order ge_i m2)
        (IDCUR : Genv.invert_symbol ge_i cur = Some id_cur)
    :
    exists cst2 : state,
      star step1 ge_c (State f stmt k0 e le m_c)
           (unbundle (id_cur, Bundle_call tr id0 evargs (fn_sig f_next) d)) cst2 /\
        ((exists id' : positive,
             wf_c_state ge_i ge_c (pretr ++ [(id_cur, Bundle_call tr id0 evargs (fn_sig f_next) d)])
                        (pretr ++ (id_cur, Bundle_call tr id0 evargs (fn_sig f_next) d) :: btr) cnts id' cst2 /\
               (exists k : meminj,
                   match_state ge_i ge_c k
                               (pretr ++ (id_cur, Bundle_call tr id0 evargs (fn_sig f_next) d) :: btr) cnts pars
                               id' (Some (b, m2, ir_cont cur :: k_i)) cst2)) \/
           Some (b, m2, ir_cont cur :: k_i) = None).
  Proof.
    assert (id = id_cur).
    { unfold match_cur_fun in MS2. des. rewrite MS7 in IDCUR. clarify. }
    subst id.
    rename f_next into fi_next.

    exploit MS3.
    { eapply Genv.find_funct_ptr_iff. erewrite <- Genv.find_funct_find_funct_ptr. eapply FINDF. }
    { eapply Genv.find_invert_symbol; eauto. }
    intros FINDF_C. des_ifs. rename id0 into id_next, i into cnt_next, Heq into CNTS_NEXT, l into params_next, Heq0 into PARS_NEXT. simpl in FINDF_C.
    set (pretr ++ (id_cur, Bundle_call tr id_next evargs (fn_sig fi_next) d) :: btr) as ttr in *.
    set (gen_function ge_i cnt_next params_next (get_id_tr ttr id_next) fi_next) as f_next in *.
    set (fn_body f_next) as stmt_next.
    hexploit Genv.invert_find_symbol. eapply IDCUR. intros FIND_CUR_I.
    destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).
    assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
    { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1 in FIND_CUR_I. auto. }
    assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
    { auto. }

    exploit WFC0. apply FIND_CUR_I. rewrite <- Genv.find_funct_ptr_iff. apply FINDF_I_CUR.
    intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
    set (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)) as kc_next.
    assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_call tr id_next evargs (fn_sig fi_next) d) :: (get_id_tr btr id_cur)).
    { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
    assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
    { rewrite map_length. eapply Z.le_lt_trans. 2: eauto. unfold get_id_tr.
      apply inj_le. apply list_length_filter_le.
    }
    destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).
    assert (PARSIGS: list_typ_to_list_type (sig_args (fn_sig fi_next)) = map snd params_next).
    { destruct MS5 as (_ & WFP1 & _). exploit WFP1. apply FINDF. apply FINDB. apply PARS_NEXT. ss. }

    hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply INV_CUR. eauto.
    intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
    rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
    assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
    { unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss. }
    assert (COMP_CUR_EQ: comp_of (@Gfun _ unit (AST.Internal f_i_cur)) = comp_of f).
    { subst f. ss. }
    setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_VA. setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_LOAD.

    hexploit switch_spec.
    { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
    { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3. }
    eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
    { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
    instantiate (1:=le).
    instantiate (1:=(Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)).
    instantiate (1:=Sreturn None).
    intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).

    assert (DELTA_C: exists m_c', (mem_delta_apply_wf ge_i (comp_of f) d (Some m_cu) = Some m_c') /\
                               (Mem.inject (meminj_public ge_i) m2 m_c')).
    { move MS1 after CUR_SWITCH_STAR. destruct MS1 as (MINJ & INJINCR & NALLOC).
      move DELTA after NALLOC. move PUB after NALLOC.
      hexploit mem_delta_apply_establish_inject_preprocess2.
      apply MINJ. eapply CNT_CUR_STORE.
      { instantiate (1:=ge_i). erewrite match_symbs_meminj_public. 2: destruct MS0 as (MS & _); apply MS.
        ii. unfold meminj_public in H. des_ifs. apply Senv.find_invert_symbol in FIND_CNT_CUR.
        rewrite FIND_CNT_CUR in Heq. clarify.
      }
      apply INJINCR. apply NALLOC. apply DELTA. apply PUB.
      intros (m_c' & DELTA' & INJ'). exists m_c'. splits; auto.
      rewrite CP_CUR. auto.
    }
    des. rename DELTA_C0 into MEMINJ_CNT.
    assert (ENV_ALLOC: exists e_next m_c_next0, alloc_variables ge_c (comp_of f_next) empty_env m_c' (fn_params f_next ++ fn_vars f_next) e_next m_c_next0).
    { eapply alloc_variables_exists. }
    des.
    assert (ENV_BIND: exists m_c_next, bind_parameters ge_c (comp_of f_next) e_next m_c_next0 (fn_params f_next) vargs m_c_next).
    { move PARSIGS after ENV_ALLOC. inv TR; ss.
      eapply bind_parameters_exists. 2: apply PARSIGS.
      2:{ eapply match_senv_eventval_list_match. 2: apply H1. destruct MS0 as (MS0 & _); auto. }
      rewrite app_nil_r in ENV_ALLOC. eapply alloc_variables_forall. apply ENV_ALLOC.
      { move MS5 after H1. destruct MS5. specialize (H2 _ _ PARS_NEXT). auto. }
    }
    des.
    set (create_undef_temps (fn_temps f_next)) as le_next.
    set (State f_next (fn_body f_next)
               (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0))
               e_next le_next m_c_next) as cst2.

    assert (ENV_NGLOB: not_global_blks (ge_c) (blocks_of_env2 ge_c e_next)).
    { clear CUR_SWITCH_STAR. move MS5 after le_next. destruct MS5 as (MP1 & MP2 & MP3).
      apply Forall_forall. i.
      unfold blocks_of_env2, blocks_of_env in H. rewrite map_map in H.
      apply list_in_map_inv in H. des. destruct x0 as (xid & xb & xt).
      apply PTree.elements_complete in H0. move WFNB after H0.
      destruct (Senv.invert_symbol ge_c x) eqn:CASES; auto. exfalso.
      unfold wf_c_nb in WFNB. apply Senv.invert_find_symbol in CASES. apply Senv.find_symbol_below in CASES.
      hexploit alloc_variables_one_fresh_block. eapply ENV_ALLOC.
      { ss. rewrite app_nil_r. eapply MP1. eauto. }
      { ss. }
      eapply H0. intros. apply H1; clear H1. ss. clarify. unfold Mem.valid_block.
      eapply mem_delta_apply_wf_wunchanged_on in DELTA_C. eapply store_wunchanged_on in CNT_CUR_STORE.
      eapply wunchanged_on_nextblock in CNT_CUR_STORE, DELTA_C. revert_until H0. clear; i.
      eapply Plt_Ple_trans. eapply CASES. etransitivity. eapply WFNB. etransitivity; eauto.
      Unshelve. all: exact (fun _ _ => True).
    }
    assert (ENV_NINJ: not_inj_blks (meminj_public ge_c) (blocks_of_env2 ge_c e_next)).
    { eapply not_global_is_not_inj_bloks. auto. }

    assert (WFC_NEXT: wf_c_state ge_i ge_c (pretr ++ [(id_cur, Bundle_call tr id_next evargs (fn_sig fi_next) d)]) ttr cnts id_next cst2).
    { subst cst2; ss. splits; auto.
      - unfold wf_counters. splits; auto.
        clear CUR_SWITCH_STAR. move WFC0 after le_next.
        ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
        unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
        exists b1. splits; auto.
        + eapply bind_parameters_valid_access. eapply ENV_BIND.
          eapply alloc_variables_valid_access. eapply ENV_ALLOC.
          eapply mem_delta_apply_wf_valid_access. eapply DELTA_C.
          eapply Mem.store_valid_access_1. eapply CNT_CUR_STORE.
          auto.
        + assert (MNB: (b1 < Mem.nextblock m_c')%positive).
          { eapply Mem.valid_access_implies in WFC7.
            apply Mem.valid_access_valid_block in WFC7. 2: apply perm_any_N.
            unfold Mem.valid_block in WFC7.
            hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros UCH1.
            hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros UCH2.
            apply wunchanged_on_nextblock in UCH1, UCH2.
            eapply Pos.lt_le_trans; eauto. etransitivity; eauto.
          }
          destruct (Pos.eq_dec id id_cur).
          * subst id. clarify. ss. rewrite FIND_CNT_CUR in WFC6. clarify.
            replace (comp_of gd) with 
                    (comp_of
                       (gen_function ge_i cnt_cur params_cur (get_id_tr ttr id_cur) f_i_cur)).
            2:{ rewrite Genv.find_funct_ptr_iff in FINDF_I_CUR. rewrite FINDF_I_CUR in H0.
                clarify.
            }
            erewrite bind_parameters_mem_load. 2: eapply ENV_BIND.
            2:{ eapply alloc_variables_old_blocks. eapply ENV_ALLOC. 2: ii; ss. auto. }
            erewrite alloc_variables_mem_load. 2: eapply ENV_ALLOC.
            2:{ auto. }
            erewrite mem_delta_apply_wf_mem_load.
            2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. apply DELTA_C. destruct MS0 as (MS & _). eauto. }
            2:{ eapply Genv.find_invert_symbol. eapply FIND_CNT_CUR. }
            2:{ auto. }
            erewrite Mem.load_store_same. 2: eapply CNT_CUR_STORE.
            ss. rewrite map_length. rewrite get_id_tr_app. ss.
            rewrite Pos.eqb_refl. rewrite app_length. ss.
            do 2 f_equal. apply nat64_int64_add_one.
            subst ttr. clear - BOUND. unfold get_id_tr. eapply Z.le_lt_trans; eauto.
            eapply inj_le. rewrite app_length. etransitivity. eapply list_length_filter_le.
            apply Nat.le_add_r.
          * ss. erewrite bind_parameters_mem_load. 2: eapply ENV_BIND.
            2:{ eapply alloc_variables_old_blocks. eapply ENV_ALLOC. 2: ii; ss. auto. }
            erewrite alloc_variables_mem_load. 2: eapply ENV_ALLOC.
            2:{ auto. }
            erewrite mem_delta_apply_wf_mem_load.
            2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. apply DELTA_C. destruct MS0 as (MS & _). eauto. }
            2:{ eapply Genv.find_invert_symbol. eapply WFC6. }
            2:{ auto. }
            erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
            2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
            }
            rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r.
            rewrite WFC8. auto.

      - clear CUR_SWITCH_STAR. move WFC1 after le_next. move WFC4 after WFC1. move FREEENV after WFC4.
        hexploit alloc_variables_exists_free_list. eapply ENV_ALLOC. ss. ss. ss. intros; des.
        hexploit wunchanged_on_exists_mem_free_list. 2: eapply H.
        { eapply wunchanged_on_implies. eapply bind_parameters_wunchanged_on. apply ENV_BIND. ss. }
        intros (m_f' & FREE).
        assert (WU: wunchanged_on (fun b _ => Mem.valid_block m_c b) m_c m_f').
        { eapply wunchanged_on_trans. eapply store_wunchanged_on. eapply CNT_CUR_STORE.
          eapply wunchanged_on_trans. eapply wunchanged_on_implies. eapply mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. ss.
          eapply wunchanged_on_trans. eapply wunchanged_on_implies. eapply alloc_variables_wunchanged_on. eapply ENV_ALLOC. ss.
          eapply wunchanged_on_trans. eapply wunchanged_on_implies. eapply bind_parameters_wunchanged_on. eapply ENV_BIND. ss.
          eapply mem_free_list_wunchanged_on. eapply FREE.
          eapply alloc_variables_fresh_blocks. eapply ENV_ALLOC.
          2:{ unfold blocks_of_env, empty_env. ss. }
          hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. i. eapply wunchanged_on_nextblock in H0.
          etransitivity. 2: eapply H0. erewrite <- Mem.nextblock_store. 2: eapply CNT_CUR_STORE. lia.
        }
        hexploit wunchanged_on_exists_mem_free_list. eapply WU. eapply FREEENV. intros (m_freeenv' & FREEENV').
        exists m_f'. splits; auto. econs. 1,2,3: eauto. eapply FREEENV'.
        hexploit wunchanged_on_free_list_preserves. eapply WU. eapply FREEENV. eapply FREEENV'. intros WUFREE.
        move WFC1 after FREEENV'.
        eapply wf_c_cont_wunchanged_on. eapply WFC1. apply WUFREE.

      - move WFC2 after le_next. unfold wf_c_stmt in *. clear CUR_SWITCH_STAR.
        i. rewrite CNTS_NEXT in H. inv H. rename cnt into cnt_next.
        subst f_next. unfold comp_of. ss. apply match_symbs_code_bundle_trace.
        destruct MS0 as (MS0 & _); auto.

      - clear CUR_SWITCH_STAR. move MS5 after le_next. destruct MS5 as (MP1 & MP2 & MP3).
        eapply alloc_variables_wf_params_of_symb. eapply ENV_ALLOC. eapply MP3.
        rewrite app_nil_r. apply PARS_NEXT.

      - clear CUR_SWITCH_STAR. move WFNB after ENV_NINJ. unfold wf_c_nb in *.
        eapply bind_parameters_wunchanged_on in ENV_BIND. eapply alloc_variables_wunchanged_on in ENV_ALLOC.
        eapply mem_delta_apply_wf_wunchanged_on in DELTA_C. eapply store_wunchanged_on in CNT_CUR_STORE.
        eapply wunchanged_on_nextblock in CNT_CUR_STORE, DELTA_C, ENV_ALLOC, ENV_BIND.
        clear - CNT_CUR_STORE DELTA_C ENV_ALLOC ENV_BIND WFNB.
        do 5 (etransitivity; eauto).
    }

    assert (MS_NEXT: match_state ge_i ge_c (meminj_public ge_i) ttr cnts pars id_next (Some (b, m2, ir_cont cur :: k_i)) cst2).
    { clear CUR_SWITCH_STAR WFC_NEXT. subst cst2. ss.
      rewrite app_nil_r in ENV_ALLOC. splits; auto.
      - unfold match_mem. splits; auto.
        + eapply bind_parameters_outside_mem_inject. eapply ENV_BIND.
          2:{ eapply not_inj_blks_get_env. erewrite match_symbs_meminj_public. eapply ENV_NINJ. destruct MS0 as (MS0 & _). apply MS0.
          }
          2: apply meminj_public_same_block.
          eapply alloc_variables_mem_inject. eapply ENV_ALLOC. auto.
        + move MS1 after ENV_NINJ. destruct MS1 as (MM1 & MM2 & MM3).
          move DELTA after ENV_NINJ. eapply meminj_not_alloc_delta. eapply MM3. eapply DELTA.
      - unfold match_cur_fun. splits; auto.
        + rewrite Genv.find_funct_ptr_iff. eapply FINDF_C.
        + eexists. eapply FINDF.
        + apply Genv.find_invert_symbol. apply FINDB.
      - move MS4 after ENV_NINJ. econs 2. 4,5,6: eauto. all: auto.
        apply Genv.find_invert_symbol. apply FIND_CUR_C.
      - move MS1 after ENV_NINJ. move MCNTS after MS1. destruct MS1 as (MM1 & MM2 & MM3).
        eapply mem_inject_incr_match_cnts_rev. eapply MM2. auto.
    }

    exists cst2. split.
    2:{ left. exists id_next. split. apply WFC_NEXT. eexists. eapply MS_NEXT. }
    unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
    eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
    unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
    rewrite ! (match_symbs_code_bundle_call ge_i ge_c) in CUR_SWITCH_STAR. rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
    eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: auto.
    clear BOUND2 CUR_SWITCH_STAR.
    unfold code_bundle_call. eapply star_trans. eapply code_mem_delta_correct. auto.
    { erewrite <- match_symbs_mem_delta_apply_wf. eapply DELTA_C.
      destruct MS0 as (MSYMB & _). auto. }
    2: ss. 2,3: destruct MS0 as (MSENV & _); apply MSENV.
    unfold unbundle. simpl. rename b into next.

    assert (CP_NEXT:
             (Genv.find_comp ge_c (Vptr next Ptrofs.zero)) =
               (comp_of fi_next)).
    { unfold Genv.find_comp. apply Genv.find_funct_ptr_iff in FINDF_C. setoid_rewrite FINDF_C. subst f_next. ss. }
    assert (EVARGS: list_eventval_to_list_val ge_c evargs = vargs).
    { destruct MS0 as (MSENV & MGENV). inv TR.
      eapply eventval_list_match_list_eventval_to_list_val. eapply match_symbs_eventval_list_match; eauto.
    }

    econs 2.
    { eapply step_call. ss.
      { econs. assert (FSN_C: Senv.find_symbol ge_c id_next = Some next).
        { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1. auto. }
        eapply eval_Evar_global.
        - unfold wf_env in WFC3. specialize (WFC3 id_next). rewrite FSN_C in WFC3. apply WFC3.
        - eapply FSN_C.
        - econs 2. ss.
      }
      { eapply list_eventval_to_expr_val_eval. auto. inv TR. eapply eventval_list_match_transl. eapply match_senv_eventval_list_match; eauto. destruct MS0 as (MSENV & _); auto. }
      { unfold match_find_def in MS3. hexploit MS3.
        unfold Genv.find_funct in FINDF. rewrite pred_dec_true in FINDF; auto. unfold Genv.find_funct_ptr in FINDF. des_ifs. eapply Heq.
        eapply Senv.find_invert_symbol; eapply FINDB.
        rewrite CNTS_NEXT, PARS_NEXT. intros. unfold Genv.find_funct. rewrite pred_dec_true. unfold Genv.find_funct_ptr. rewrite H. ss. ss.
      }
      { ss. unfold type_of_function, gen_function. ss. f_equal. apply type_of_params_eq. apply PARSIGS. }
      { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV).
        subst f. setoid_rewrite CP_CUR.
        eapply allowed_call_gen_function; eauto.
        { setoid_rewrite Genv.find_funct_ptr_iff. rewrite FINDF_C. subst f_next. eauto. }
      }
      { move NPTR after MS_NEXT. move TR after NPTR. i.
        rewrite EVARGS. apply NPTR. unfold crossing_comp. rewrite <- H.
        setoid_rewrite CP_CUR. rewrite CP_NEXT. auto.
      }
      { move TR after MS_NEXT. instantiate (1:=tr). inv TR.
        setoid_rewrite CP_CUR. rewrite CP_NEXT.
        econs 2.
        { rewrite <- H. ss. }
        eauto.
        { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.find_invert_symbol. apply MSENV1. auto. }
        { eapply eventval_list_match_transl. eapply match_senv_eventval_list_match; eauto. destruct MS0 as (MSENV & _); auto. }
      }
    }
    { econs 2. 2: econs 1. eapply step_internal_function. 2: ss.
      econs; eauto.
      { destruct MS5 as (MPARS & _). specialize (MPARS _ _ PARS_NEXT). subst f_next. ss. rewrite app_nil_r. auto. }
      { rewrite EVARGS. auto. }
    }
    traceEq.

    Unshelve. all: try exact 0%nat. all: exact (fun _ _ => True).
  Qed.

  Lemma ir_to_clight_step_2
        ge_i ge_c
        (WFGE : wf_ge ge_i)
        cnts pars cur m_i pretr btr tr evretv d id_cur
        (BOUND : Z.of_nat (Datatypes.length (pretr ++ (id_cur, Bundle_return tr evretv d) :: btr)) <
                   Int64.modulus)
        k_c id f stmt k0 e le m_c
        (MS0 : match_genv ge_i ge_c)
        (MS1 : match_mem ge_i k_c m_i m_c)
        (MS2 : match_cur_fun ge_i ge_c cur f id)
        (MS3 : match_find_def ge_i ge_c cnts pars (pretr ++ (id_cur, Bundle_return tr evretv d) :: btr))
        next ik_tl
        (MS4 : match_cont ge_c (pretr ++ (id_cur, Bundle_return tr evretv d) :: btr) cnts k0
                          (ir_cont next :: ik_tl))
        (MS5 : match_params pars ge_c ge_i)
        (MCNTS : match_cnts cnts ge_c k_c)
        (CNT_INJ : forall (id0 id1 : positive) (cnt : ident),
            cnts ! id0 = Some cnt -> cnts ! id1 = Some cnt -> id0 = id1)
        (WFC0 : forall (id : ident) (b : block) gd,
            Genv.find_symbol ge_i id = Some b ->
            Genv.find_def ge_i b = Some gd ->
            exists cnt : ident,
              cnts ! id = Some cnt /\
                wf_counter ge_c m_c (comp_of gd) (Datatypes.length (get_id_tr pretr id)) cnt)
        m_freeenv
        (FREEENV : Mem.free_list m_c (blocks_of_env ge_c e) (comp_of f) = Some m_freeenv)
        (WFC1 : wf_c_cont ge_c m_freeenv k0)
        (WFC2 : wf_c_stmt ge_c (comp_of f) cnts id (pretr ++ (id_cur, Bundle_return tr evretv d) :: btr)
                          stmt)
        (WFC3 : wf_env ge_c e)
        (WFC4 : not_global_blks ge_c (blocks_of_env2 ge_c e))
        (WFNB : wf_c_nb ge_c m_c)
        vretv fd_cur f_next m2
        (FINDFD : Genv.find_funct_ptr ge_i cur = Some fd_cur)
        (NPTR : crossing_comp ge_i (Genv.find_comp ge_i (Vptr next Ptrofs.zero))
                              (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) -> not_ptr vretv)
        (INTERNAL : Genv.find_funct_ptr ge_i next = Some (AST.Internal f_next))
        (TR : return_trace_cross ge_i (Genv.find_comp ge_i (Vptr next Ptrofs.zero))
                                 (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) vretv (sig_res (funsig fd_cur)) tr evretv)
        (DELTA : mem_delta_apply_wf ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) d (Some m_i) =
                   Some m2)
        (PUB : public_first_order ge_i m2)
        (IDCUR : Genv.invert_symbol ge_i cur = Some id_cur)
    :
    exists cst2 : state,
      star step1 ge_c (State f stmt k0 e le m_c) (unbundle (id_cur, Bundle_return tr evretv d))
           cst2 /\
        ((exists id' : positive,
             wf_c_state ge_i ge_c (pretr ++ [(id_cur, Bundle_return tr evretv d)])
                        (pretr ++ (id_cur, Bundle_return tr evretv d) :: btr) cnts id' cst2 /\
               (exists k : meminj,
                   match_state ge_i ge_c k (pretr ++ (id_cur, Bundle_return tr evretv d) :: btr) cnts
                               pars id' (Some (next, m2, ik_tl)) cst2)) \/ Some (next, m2, ik_tl) = None).
  Proof.
    assert (id = id_cur).
    { unfold match_cur_fun in MS2. des. rewrite MS7 in IDCUR. clarify. }
    subst id. rename f_next into fi_next.
    assert (INV_ID_NEXT: exists id_next, Genv.invert_symbol ge_i next = Some id_next).
    { rewrite Genv.find_funct_ptr_iff in INTERNAL. eapply wf_ge_block_to_id. auto. eauto. }
    des.
    destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).
    assert (FIND_CUR_I: Genv.find_symbol ge_i id_cur = Some cur).
    { apply Genv.invert_find_symbol; auto. }

    exploit MS3.
    { eapply Genv.find_funct_ptr_iff. eapply INTERNAL. }
    { eapply INV_ID_NEXT. }
    intros FINDF_C. des_ifs. rename i into cnt_next, Heq into CNTS_NEXT, l into params_next, Heq0 into PARS_NEXT. simpl in FINDF_C.
    set (pretr ++ (id_cur, Bundle_return tr evretv d) :: btr) as ttr in *.
    set (gen_function ge_i cnt_next params_next (get_id_tr ttr id_next) fi_next) as f_next in *.
    set (fn_body f_next) as stmt_next.
    assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
    { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.invert_find_symbol in IDCUR. apply MSENV1 in IDCUR. auto. }
    assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
    { auto. }

    exploit WFC0. eapply FIND_CUR_I. rewrite <- Genv.find_funct_ptr_iff; eauto.
    intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
    inv WFC1.
    { inv MS4. inv IK. inv CK. }
    assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_return tr evretv d) :: (get_id_tr btr id_cur)).
    { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
    assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
    { rewrite map_length. eapply Z.le_lt_trans. 2: eauto. unfold get_id_tr.
      apply inj_le. apply list_length_filter_le.
    }
    destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).
    assert (PARSIGS: list_typ_to_list_type (sig_args (fn_sig fi_next)) = map snd params_next).
    { destruct MS5 as (_ & WFP1 & _). exploit WFP1. apply INTERNAL. apply Genv.invert_find_symbol. apply INV_ID_NEXT. apply PARS_NEXT. ss. }

    inv MS4.
    { inv IK. }
    clarify.

    hexploit cur_fun_def. eapply FIND_FUN_C. eapply FINDFD. eapply IDCUR. eauto.
    intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
    rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
    assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
    { unfold Genv.find_comp. setoid_rewrite FINDFD. subst f. ss. }
    assert (COMP_CUR_EQ: comp_of (@Gfun _ unit (AST.Internal f_i_cur)) = comp_of f).
    { subst f. ss. }
    setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_VA. setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_LOAD.

    rename ck'0 into ck_next. rename e1 into e_next. rename le1 into le_next.
    hexploit switch_spec.
    { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
    { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3. }
    eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
    { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
    instantiate (1:=le).
    instantiate (1:= (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur)))
                             Sskip
                             (Kcall None f_next e_next le_next (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_next (comp_of f_next) (get_id_tr ttr id_next))) Sskip ck_next)))).
    instantiate (1:=Sreturn None).
    intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).

    assert (DELTA_C: exists m_c', (mem_delta_apply_wf ge_i (comp_of f) d (Some m_cu) = Some m_c') /\
                               (Mem.inject (meminj_public ge_i) m2 m_c')).
    { move MS1 after CUR_SWITCH_STAR. destruct MS1 as (MINJ & INJINCR & NALLOC).
      move DELTA after NALLOC. move PUB after NALLOC.
      hexploit mem_delta_apply_establish_inject_preprocess2.
      apply MINJ. eapply CNT_CUR_STORE.
      { instantiate (1:=ge_i). erewrite match_symbs_meminj_public. 2: destruct MS0 as (MS & _); apply MS.
        ii. unfold meminj_public in H. des_ifs. apply Senv.find_invert_symbol in FIND_CNT_CUR.
        rewrite FIND_CNT_CUR in Heq. clarify.
      }
      apply INJINCR. apply NALLOC. apply DELTA. apply PUB.
      intros (m_c' & DELTA' & INJ'). exists m_c'. splits; auto.
      rewrite CP_CUR. auto.
    }
    des. rename DELTA_C0 into MEMINJ_CNT.

    assert (f1 = f_next).
    { rewrite <- Genv.find_funct_ptr_iff in FINDF_C. rewrite FINDF_C in FUN. clarify. }
    subst f1. clear INV_CUR.
    assert (id = id_next).
    { apply Genv.invert_find_symbol in INV_ID_NEXT. destruct MS0 as ((_ & MS & _) & _). apply MS in INV_ID_NEXT.
      apply Senv.find_invert_symbol in INV_ID_NEXT. setoid_rewrite INV_ID_NEXT in ID. clarify.
    }
    subst id.
    assert (cnt = cnt_next).
    { rewrite CNTS_NEXT in CNT. clarify. }
    subst cnt. clear ID CNT.

    assert (WCHG1: wunchanged_on (fun b _ => Mem.valid_block m_c b) m_c m_c').
    { eapply wunchanged_on_trans. eapply store_wunchanged_on. eapply CNT_CUR_STORE.
      eapply wunchanged_on_implies. eapply mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. ss.
    }
    assert (FREENEXT: exists m_c_next, Mem.free_list m_c' (blocks_of_env ge_c e) (comp_of f) = Some m_c_next).
    { eapply wunchanged_on_exists_mem_free_list. eapply WCHG1. eapply FREEENV. }
    des.

    set (State f_next (fn_body f_next) ck_next e_next le_next m_c_next) as cst2.

    assert (WFC_NEXT: wf_c_state ge_i ge_c (pretr ++ [(id_cur, Bundle_return tr evretv d)]) ttr cnts id_next cst2).
    { clear CUR_SWITCH_STAR. ss. splits; auto.
      - unfold wf_counters. split. auto.
        move WFC0 after cst2.
        ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
        unfold wf_counter in WFC1. des. unfold wf_counter. splits; auto.
        exists b1. splits; auto.
        + eapply mem_valid_access_wunchanged_on. eapply WFC6.
          eapply wunchanged_on_trans; cycle 1. eapply mem_free_list_wunchanged_on_2. eapply FREENEXT.
          eapply wunchanged_on_trans; cycle 1. eapply mem_delta_apply_wf_wunchanged_on. eapply DELTA_C.
          eapply store_wunchanged_on. eapply CNT_CUR_STORE. ss. i.
          move MS5 after H0. destruct MS5 as (MP0 & MP1 & MP). specialize (MP _ _ WFC5). move WFC4 after MP.
          eapply not_global_blks_global_not_in; eauto.
        + move WFNB after CP_CUR. move WFC4 after WFNB.
          eapply Mem.load_unchanged_on. eapply mem_free_list_unchanged_on. eapply FREENEXT.
          { ss. i. eapply not_global_blks_global_not_in; eauto. }
          erewrite mem_delta_apply_wf_mem_load; cycle 1.
          { erewrite match_symbs_mem_delta_apply_wf in DELTA_C. apply DELTA_C. destruct MS0 as (MS & _). eauto. }
          { eapply Genv.find_invert_symbol. apply WFC5. }
          { auto. }
          destruct (Pos.eq_dec id id_cur).
          * subst id. assert (cnt_cur = cnt).
            { rewrite WFC0 in CNTS_CUR. clarify. }
            subst cnt. assert (b1 = cnt_cur_b).
            { setoid_rewrite WFC5 in FIND_CNT_CUR. clarify. }
            subst b1. assert (b0 = cur).
            { rewrite FIND_CUR_I in H. clarify. }
            subst b0. assert (gd = Gfun (AST.Internal f_i_cur)).
            { apply Genv.find_funct_ptr_iff in FINDFD. rewrite FINDFD in H0. clarify. }
            subst gd. erewrite Mem.load_store_same.
            2: setoid_rewrite COMP_CUR_EQ; eapply CNT_CUR_STORE.
            ss. rewrite map_length. rewrite get_id_tr_app. ss.
            rewrite Pos.eqb_refl. rewrite app_length. ss.
            do 2 f_equal. apply nat64_int64_add_one.
            subst ttr. clear - BOUND. unfold get_id_tr. eapply Z.le_lt_trans; eauto.
            eapply inj_le. rewrite app_length. etransitivity. eapply list_length_filter_le.
            apply Nat.le_add_r.
          * ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
            2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC5.
                rewrite FIND_CNT_CUR in WFC5. clarify. rename cnt into cnt_cur.
                specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
            }
            rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. rewrite WFC7. auto.

      - move IND after cst2. move FREE after cst2. move FREEENV after cst2.
        hexploit wunchanged_on_free_list_preserves. eapply WCHG1. all: eauto. intros WCHG2.
        hexploit wunchanged_on_exists_mem_free_list. eapply WCHG2. eapply FREE. intros (m_c_next2 & FREE2).
        exists m_c_next2. splits; auto.
        hexploit wunchanged_on_free_list_preserves. eapply WCHG2. all: eauto. intros WCHG3.
        eapply wf_c_cont_wunchanged_on. eapply IND. auto.

      - move WFC2 after cst2. unfold wf_c_stmt in *. i. rewrite CNTS_NEXT in H. inv H. rename cnt into cnt_next.
        subst f_next. unfold comp_of. ss. apply match_symbs_code_bundle_trace. destruct MS0 as (MS0 & _); auto.

      - move WFNB after cst2. unfold wf_c_nb in *.
        apply SimplLocalsproof.free_list_nextblock in FREENEXT. rewrite FREENEXT.
        eapply mem_delta_apply_wf_wunchanged_on in DELTA_C. eapply store_wunchanged_on in CNT_CUR_STORE.
        eapply wunchanged_on_nextblock in CNT_CUR_STORE, DELTA_C.
        clear - WFNB CNT_CUR_STORE DELTA_C.
        do 5 (etransitivity; eauto).
        Unshelve. all: try (exact 0%nat). all: try (exact (fun _ _ => True)).
    }

    assert (MS_NEXT: match_state ge_i ge_c (meminj_public ge_i) ttr cnts pars id_next (Some (b, m2, ik')) cst2).
    { clear CUR_SWITCH_STAR WFC_NEXT. ss. splits; auto.
      - unfold match_mem. splits; auto.
        + eapply SimplLocalsproof.free_list_right_inject. eapply MEMINJ_CNT. eapply FREENEXT.
          i. move WFC4 after cst2. apply not_global_is_not_inj_bloks in WFC4. setoid_rewrite Forall_forall in WFC4.
          assert (b2 = b1).
          { clear - H. unfold meminj_public in H. des_ifs. }
          subst b2. hexploit (WFC4 b1).
          { unfold blocks_of_env2, blocks_of_env in *. rewrite map_map.
            eapply (in_map (fun x => fst (fst x))) in H0. ss. rewrite map_map in H0. ss.
          }
          intros. erewrite <- match_symbs_meminj_public in H3. rewrite H in H3. clarify.
          destruct MS0 as (MS & _). apply MS.
        + move MS1 after cst2. destruct MS1 as (MM1 & MM2 & MM3).
          move DELTA after cst2. eapply meminj_not_alloc_delta. eapply MM3. eapply DELTA.
      - unfold match_cur_fun. splits; auto. eauto.
      - destruct MS1 as (MM1 & MM2 & MM3). eapply mem_inject_incr_match_cnts_rev; eauto.
    }
    exists cst2. split.
    2:{ left. exists id_next. split. apply WFC_NEXT. eexists. eapply MS_NEXT. }

    unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
    eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
    unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
    rewrite ! (match_symbs_code_bundle_return ge_i ge_c) in CUR_SWITCH_STAR. rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
    eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
    clear BOUND2 CUR_SWITCH_STAR.
    unfold code_bundle_return. eapply star_trans. eapply code_mem_delta_correct. auto.
    { erewrite <- match_symbs_mem_delta_apply_wf. eapply DELTA_C. destruct MS0 as (MSYMB & _). auto. }
    2: ss.
    unfold unbundle. simpl. rename b into next.

    assert (CP_NEXT: (Genv.find_comp ge_c (Vptr next Ptrofs.zero)) = (comp_of fi_next)).
    { unfold Genv.find_comp. apply Genv.find_funct_ptr_iff in FINDF_C. setoid_rewrite FINDF_C. subst f_next. ss. }
    assert (EVRETV: eventval_to_val ge_c evretv = vretv).
    { destruct MS0 as (MSENV & MGENV). inv TR.
      eapply eventval_match_eventval_to_val. eapply match_symbs_eventval_match; eauto.
    }

    econs 2.
    { inv TR. eapply match_senv_eventval_match in H0. 2: destruct MS0 as (MS0 & _); apply MS0.
      eapply step_return_1.
      - eapply eventval_to_expr_val_eval. auto. eapply H0.
      - ss.
        (* assert (fd_cur = AST.Internal f_i_cur). *)
        (* { rewrite FINDFD in FINDF_I_CUR; clarify. } *)
        (* subst fd_cur. *)
        eapply sem_cast_proj_rettype. eapply H0.
      - eapply FREENEXT.
    }
    ss. econs 2.
    { assert (CPEQ1: comp_of f_next = (Genv.find_comp ge_i (Vptr next Ptrofs.zero))).
      { subst f_next. unfold comp_of, gen_function. ss. unfold Genv.find_comp. setoid_rewrite INTERNAL. ss. }
      assert (CPEQ2: (comp_of (gen_function ge_i cnt_cur params_cur (get_id_tr ttr id_cur) f_i_cur)) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
      { unfold comp_of, gen_function. ss. unfold Genv.find_comp. setoid_rewrite FINDFD. ss. }
      eapply step_returnstate.
      - move NPTR after EVRETV. i. rewrite EVRETV. apply NPTR. rr. rewrite CPEQ1 in H. setoid_rewrite CPEQ2 in H. apply H.
      - move TR after EVRETV. instantiate (1:=tr). inv TR. setoid_rewrite CPEQ2. rewrite CPEQ1. econs; auto.
        (* assert (fd_cur = AST.Internal f_i_cur). *)
        (* { rewrite FINDFD in FINDF_I_CUR; clarify. } *)
        (* subst fd_cur. *)
        (* ss. *)
        erewrite proj_rettype_to_type_rettype_of_type_eq. 2: eapply H0.
        eapply match_senv_eventval_match. 2: eapply H0. apply MS0.
    }
    ss. econs 2.
    { eapply step_skip_or_continue_loop1. auto. }
    econs 2.
    { eapply step_skip_loop2. }
    { subst cst2. unfold code_bundle_trace. unfold Swhile. destruct MS0 as (MS0 & _).
      erewrite (match_symbs_switch_bundle_events _ _ MS0).
      setoid_rewrite <- CP_NEXT. unfold Genv.find_comp. setoid_rewrite FUN.
      replace (comp_of (Internal f_next)) with (comp_of f_next). econs 1. ss.
    }
    all: traceEq. traceEq.
  Qed.

  Lemma ir_to_clight_step_3
        ge_i ge_c
        (WFGE : wf_ge ge_i)
        cnts pars k_i cur m_i pretr btr tr id0 ef d vargs id_cur
        (BOUND : Z.of_nat
                   (Datatypes.length
                      (pretr ++
                             (id_cur, Bundle_call tr id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr)) <
                   Int64.modulus)
        k_c id f stmt k0 e le m_c
        (MS0 : match_genv ge_i ge_c)
        (MS1 : match_mem ge_i k_c m_i m_c)
        (MS2 : match_cur_fun ge_i ge_c cur f id)
        (MS4 : match_cont ge_c
                          (pretr ++
                                 (id_cur, Bundle_call tr id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr) cnts
                          k0 k_i)
        (MS3 : match_find_def ge_i ge_c cnts pars
                              (pretr ++
                                     (id_cur, Bundle_call tr id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr))
        (MS5 : match_params pars ge_c ge_i)
        (MCNTS : match_cnts cnts ge_c k_c)
        (CNT_INJ : forall (id0 id1 : positive) (cnt : ident),
            cnts ! id0 = Some cnt -> cnts ! id1 = Some cnt -> id0 = id1)
        (WFC0 : forall (id : ident) (b : block) gd,
            Genv.find_symbol ge_i id = Some b ->
            Genv.find_def ge_i b = Some gd ->
            exists cnt : ident,
              cnts ! id = Some cnt /\
                wf_counter ge_c m_c (comp_of gd) (Datatypes.length (get_id_tr pretr id)) cnt)
        m_freeenv
        (FREEENV : Mem.free_list m_c (blocks_of_env ge_c e) (comp_of f) = Some m_freeenv)
        (WFC1 : wf_c_cont ge_c m_freeenv k0)
        (WFC2 : wf_c_stmt ge_c (comp_of f) cnts id
                          (pretr ++
                                 (id_cur, Bundle_call tr id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr)
                          stmt)
        (WFC3 : wf_env ge_c e)
        (WFC4 : not_global_blks ge_c (blocks_of_env2 ge_c e))
        (WFNB : wf_c_nb ge_c m_c)
        m2 b_ext m1' vretv
        (FINDB : Genv.find_symbol ge_i id0 = Some b_ext)
        (FINDF : Genv.find_funct ge_i (Vptr b_ext Ptrofs.zero) = Some (AST.External ef))
        (INTRA : Genv.type_of_call ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) (comp_of ef) =
                   Genv.InternalCall)
        (MEM : mem_delta_apply_wf ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) d (Some m_i) =
                 Some m1')
        (EC : external_call ef ge_i vargs m1' tr vretv m2)
        (ECCASES : external_call_unknowns ef ge_i m1' vargs \/
                     external_call_known_observables ef ge_i m1' vargs tr vretv m2 /\ d = [])
        (IDCUR : Genv.invert_symbol ge_i cur = Some id_cur)
    :
    exists cst2 : state,
    star step1 ge_c (State f stmt k0 e le m_c)
      (unbundle (id_cur, Bundle_call tr id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d)) cst2 /\
    ((exists id' : positive,
        wf_c_state ge_i ge_c
          (pretr ++ [(id_cur, Bundle_call tr id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d)])
          (pretr ++
           (id_cur, Bundle_call tr id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr) cnts
          id' cst2 /\
        (exists k : meminj,
           match_state ge_i ge_c k
             (pretr ++
              (id_cur, Bundle_call tr id0 (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr)
             cnts pars id' (Some (cur, m2, k_i)) cst2)) \/ Some (cur, m2, k_i) = None).
  Proof.
    assert (id = id_cur).
    { unfold match_cur_fun in MS2. desH MS2. rewrite MS7 in IDCUR. clarify. }
    subst id. rename id0 into id_next. 
    destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).

    set (pretr ++ (id_cur, Bundle_call tr id_next (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr) as ttr in *.
    assert (FIND_CUR_I: Genv.find_symbol ge_i id_cur = Some cur).
    { apply Genv.invert_find_symbol in IDCUR. auto. }
    assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
    { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1 in FIND_CUR_I. auto. }
    assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
    { auto. }

    exploit WFC0. eapply FIND_CUR_I. rewrite <- Genv.find_funct_ptr_iff; eapply FINDF_I_CUR.
    intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
    assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_call tr id_next (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: (get_id_tr btr id_cur)).
    { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
    assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
    { rewrite map_length. eapply Z.le_lt_trans. 2: eauto. unfold get_id_tr.
      apply inj_le. apply list_length_filter_le.
    }
    destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).

    hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply INV_CUR. eauto.
    intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
    rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
    assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
    { unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss. }

    assert (COMP_CUR_EQ: comp_of (@Gfun _ unit (AST.Internal f_i_cur)) = comp_of f).
    { subst f. ss. }
    setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_VA. setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_LOAD.

    hexploit switch_spec.
    { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
    { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3. }
    eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
    { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
    instantiate (1:=le).
    instantiate (1:= (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)).
    instantiate (1:=Sreturn None).
    intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).
    rename MEM into DELTA. move ECCASES after CUR_SWITCH_STAR.

    assert (FIND_F_C: Genv.find_funct ge_c (Vptr b_ext Ptrofs.zero) =
                        Some (External ef (list_typ_to_typelist (sig_args (ef_sig ef))) (rettype_to_type (sig_res (ef_sig ef))) (sig_cc (ef_sig ef)))).
    { unfold match_find_def in MS3. hexploit MS3.
      unfold Genv.find_funct in FINDF. rewrite pred_dec_true in FINDF; auto. unfold Genv.find_funct_ptr in FINDF. des_ifs. eapply Heq.
      eapply Senv.find_invert_symbol; eapply FINDB.
      intros. des_ifs. ss. rewrite pred_dec_true; auto. rewrite Genv.find_funct_ptr_iff. auto.
    }
    assert (COMP_F_C: comp_of f = Genv.find_comp ge_c (Vptr b_ext Ptrofs.zero)).
    { unfold Genv.type_of_call in INTRA. des_ifs.
      setoid_rewrite CP_CUR. apply Peqb_true_eq in Heq. rewrite Heq.
      unfold Genv.find_comp. setoid_rewrite FIND_F_C. ss.
    }

    desH ECCASES; cycle 1.

    (* Case 3-1: observable defined external calls *)
    { subst d. unfold mem_delta_apply_wf in DELTA. simpl in DELTA. inversion DELTA; clear DELTA. subst m1'.
      hexploit exists_vargs_vres. eapply MS0. eapply ECCASES. eauto. intros (EVALS & EXT2).
      eapply star_cut_middle. exists E0.
      eexists. split.
      { unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
        eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
        unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
        rewrite ! (match_symbs_code_bundle_call ge_i ge_c) in CUR_SWITCH_STAR.
        rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
        eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
        clear BOUND2 CUR_SWITCH_STAR.
        unfold code_bundle_call. eapply star_trans. eapply code_mem_delta_correct. auto.
        { unfold mem_delta_apply_wf. simpl. reflexivity. }
        2: ss. econs 2. 2: econs 1. 2: traceEq.
        eapply step_call. ss.
        { econs. assert (FSN_C: Senv.find_symbol ge_c id_next = Some b_ext).
          { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1. auto. }
          eapply eval_Evar_global.
          - unfold wf_env in WFC3. specialize (WFC3 id_next). rewrite FSN_C in WFC3. apply WFC3.
          - eapply FSN_C.
          - econs 2. ss.
        }
        { eapply EVALS. }
        { eapply FIND_F_C. }
        { ss. }
        { left. apply COMP_F_C. }
        { i. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_F_C. rewrite COMP_F_C in H. inv H. }
        { econs 1. ii. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_F_C. rewrite COMP_F_C in H. inv H. }
      }
      clear BOUND2 CUR_SWITCH_STAR.
      assert (COMP_SAME: comp_of f = comp_of ef).
      { rewrite COMP_F_C. unfold Genv.find_comp. rewrite FIND_F_C. ss. }
      do 2 eexists. split.
      { econs 2. eapply step_external_function. eapply EXT2.
        econs 2. eapply step_returnstate.
        { i. exfalso. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_SAME. rewrite COMP_SAME in H. ss. }
        { econs 1. rewrite COMP_SAME. unfold Genv.type_of_call. rewrite Pos.eqb_refl. ss. }
        econs 2. eapply step_skip_or_continue_loop1. left; auto. econs 2. eapply step_skip_loop2.
        econs 1. all: ss.
      }
      splits.
      2:{ unfold unbundle. ss. traceEq. }

      left. exists id_cur. split.
      { ss. splits; auto.
        - unfold wf_counters. split; auto.
          move WFC0 after COMP_SAME. ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
          unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
          exists b0. splits; auto.
          + eapply mem_valid_access_wunchanged_on. eapply WFC7.
            eapply store_wunchanged_on. eapply CNT_CUR_STORE. instantiate (1:= fun _ _ => True). ss.
          + destruct (Pos.eq_dec id id_cur).
            * subst id. assert (cnt_cur = cnt).
              { rewrite WFC0 in CNTS_CUR. clarify. }
              subst cnt. assert (b0 = cnt_cur_b).
              { setoid_rewrite WFC6 in FIND_CNT_CUR. clarify. }
              subst b0. assert (b = cur).
              { rewrite FIND_CUR_I in H. clarify. }
              subst b. assert (gd = Gfun (AST.Internal f_i_cur)).
              { apply Genv.find_funct_ptr_iff in FINDF_I_CUR. setoid_rewrite FINDF_I_CUR in H0. clarify. }
              subst gd.
              ss. erewrite Mem.load_store_same.
              2: setoid_rewrite COMP_CUR_EQ; eapply CNT_CUR_STORE.
              ss. rewrite map_length. rewrite get_id_tr_app. ss.
              rewrite Pos.eqb_refl. rewrite app_length. ss.
              do 2 f_equal. apply nat64_int64_add_one.
              subst ttr. clear - BOUND. unfold get_id_tr. eapply Z.le_lt_trans; eauto.
              eapply inj_le. rewrite app_length. etransitivity. eapply list_length_filter_le.
              apply Nat.le_add_r.
            * ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
              2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                  rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                  specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
              }
              rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. rewrite WFC8. auto.
        - hexploit wunchanged_on_exists_mem_free_list.
          { eapply store_wunchanged_on. eapply CNT_CUR_STORE. }
          eapply FREEENV. intros (m_f & FREE2). esplits. eapply FREE2.
          eapply wf_c_cont_wunchanged_on. eapply WFC1. 
          hexploit wunchanged_on_free_list_preserves. 2: eapply FREEENV. 2: eapply FREE2. 2: auto.
          eapply store_wunchanged_on. eapply CNT_CUR_STORE.
        - move WFC2 after COMP_SAME. unfold wf_c_stmt in *. i. rewrite CNTS_CUR in H. inv H. rename cnt into cnt_cur. ss.
        - move WFNB after COMP_SAME. unfold wf_c_nb in *. erewrite Mem.nextblock_store. eapply WFNB. eapply CNT_CUR_STORE.
      }
      { ss. exists k_c. splits; auto.
        2:{ unfold match_cur_fun. splits; eauto. }
        move MS1 after COMP_SAME. move MCNTS after COMP_SAME. destruct MS1 as (MM0 & MM1 & MM2).
        assert (m2 = m_i).
        { eapply known_obs_preserves_mem. eapply ECCASES. }
        subst m2. unfold match_mem. splits; auto.
        { eapply Mem.store_outside_inject. eapply MM0. 2: eapply CNT_CUR_STORE. ss. i.
          unfold match_cnts in MCNTS. eapply MCNTS. 3: eapply H. all: eauto.
        }
      }
    }

    (* Case 3-2: observables unknown external calls *)
    { hexploit external_call_unknowns_fo. eapply ECCASES. intros FO_I.
      hexploit external_call_unknowns_val_inject_list. eapply ECCASES. intros ARGS_INJ.
      move MS1 after ARGS_INJ. destruct MS1 as (MM0 & MM1 & MM2).
      hexploit mem_delta_apply_establish_inject_preprocess2.
      eapply MM0. eapply CNT_CUR_STORE. 2: eapply MM1. 2: eapply MM2.
      2: eapply DELTA.
      2:{ apply meminj_first_order_public_first_order. auto. }
      { clear CUR_SWITCH_STAR CNT_CUR_STORE. ii. erewrite match_symbs_meminj_public in H.
        2:{ destruct MS0 as (MS & _). apply MS. }
        unfold meminj_public in H. des_ifs.
        eapply Senv.find_invert_symbol in FIND_CNT_CUR. rewrite FIND_CNT_CUR in Heq. clarify.
      }
      intros (m_next0 & DELTA_C & INJ0).
      hexploit external_call_mem_inject_gen.
      { eapply match_symbs_symbols_inject. destruct MS0 as (MS & _). apply MS. }
      apply EC. apply INJ0. apply ARGS_INJ.
      intros (j2 & vres2 & m_next & EC2 & RET_INJ & INJ2 & UCH0 & UCH1 & INCR2 & INJ_SEP).
      assert (COMP_SAME: comp_of f = comp_of ef).
      { rewrite COMP_F_C. unfold Genv.find_comp. rewrite FIND_F_C. ss. }

      exists (State f stmt k0 e le m_next). split.
      { unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
        eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
        unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
        rewrite ! (match_symbs_code_bundle_call ge_i ge_c) in CUR_SWITCH_STAR.
        rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
        eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
        clear BOUND2 CUR_SWITCH_STAR CNT_CUR_STORE.
        unfold code_bundle_call. eapply star_trans. eapply code_mem_delta_correct. auto.
        { erewrite <- match_symbs_mem_delta_apply_wf. rewrite CP_CUR. eapply DELTA_C.
          destruct MS0 as (MSYMB & _). auto.
        }
        2: ss. unfold unbundle. simpl.
        econs 2. eapply step_call. ss.
        { econs. assert (FSN_C: Senv.find_symbol ge_c id_next = Some b_ext).
          { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1. auto. }
          eapply eval_Evar_global.
          - unfold wf_env in WFC3. specialize (WFC3 id_next). rewrite FSN_C in WFC3. apply WFC3.
          - eapply FSN_C.
          - econs 2. ss.
        }
        { eapply match_symbs_vals_public_eval_to_vargs; auto.
          destruct MS0 as (MS0 & _). auto.
          eapply extcall_unkowns_vals_public; eauto.
        }
        { eapply FIND_F_C. }
        { ss. }
        { left. apply COMP_F_C. }
        { i. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_F_C. rewrite COMP_F_C in H. inv H. }
        { econs 1. ii. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_F_C. rewrite COMP_F_C in H. inv H. }

        econs 2. eapply step_external_function. eapply EC2.
        econs 2. eapply step_returnstate.
        { i. exfalso. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_SAME. rewrite COMP_SAME in H. ss. }
        { econs 1. rewrite COMP_SAME. unfold Genv.type_of_call. rewrite Pos.eqb_refl. ss. }
        econs 2. eapply step_skip_or_continue_loop1. left; auto. econs 2. eapply step_skip_loop2.
        econs 1. all: ss. traceEq.
      }

      clear CUR_SWITCH_STAR BOUND2.
      assert (UCH2: Mem.unchanged_on (fun b _ => forall b0 ofs0, (meminj_public ge_i) b0 <> Some (b, ofs0)) m_next0 m_next).
      { eapply Mem.unchanged_on_implies. eapply UCH1. ii. eapply H; eauto. }
      assert (UCH3: Mem.unchanged_on (fun b _ => Senv.invert_symbol ge_c b = None) m_next0 m_next).
      { eapply Mem.unchanged_on_implies. eapply UCH2. ss. i. unfold meminj_public. des_ifs. ii. clarify.
        apply Senv.invert_find_symbol in Heq. destruct MS0 as ((MSE1 & MSE2 & MSE3) & _). apply MSE2 in Heq.
        apply Senv.find_invert_symbol in Heq. setoid_rewrite H in Heq. ss.
      }
      eapply mem_unchanged_wunchanged in UCH3.
      hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros UCH4.
      hexploit wunchanged_on_trans. eapply UCH4. eapply UCH3. intros UCH5.
      hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros UCH6.
      hexploit wunchanged_on_trans. eapply UCH6. eapply UCH5. intros UCH7.
      clear UCH3 UCH4 UCH5 UCH6.
      left. exists id_cur. split.
      { ss. splits; auto.
        - unfold wf_counters. split; auto.
          move WFC0 after COMP_SAME. ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
          unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
          exists b0. splits; auto.
          + move MCNTS after COMP_SAME.
            eapply mem_valid_access_wunchanged_on. 2: eapply mem_unchanged_wunchanged; eapply UCH2.
            eapply mem_delta_apply_wf_valid_access. eapply DELTA_C.
            eapply mem_valid_access_wunchanged_on. 2: eapply store_wunchanged_on; eapply CNT_CUR_STORE.
            auto. instantiate (1:= fun _ _ => True). ss.
            ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto.
          + destruct (Pos.eq_dec id id_cur).
            * subst id. assert (cnt_cur = cnt).
              { rewrite WFC0 in CNTS_CUR. clarify. }
              subst cnt. assert (b0 = cnt_cur_b).
              { setoid_rewrite WFC6 in FIND_CNT_CUR. clarify. }
              subst b0. assert (b = cur).
              { rewrite FIND_CUR_I in H. clarify. }
              subst b. assert (gd = Gfun (AST.Internal f_i_cur)).
              { apply Genv.find_funct_ptr_iff in FINDF_I_CUR. setoid_rewrite FINDF_I_CUR in H0. clarify. }
              subst gd.
              ss. eapply Mem.load_unchanged_on. eapply UCH2.
              { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
              erewrite mem_delta_apply_wf_mem_load.
              2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
              2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
              2:{ auto. }
              erewrite Mem.load_store_same.
              2: setoid_rewrite COMP_CUR_EQ; eapply CNT_CUR_STORE.
              { ss. rewrite map_length. rewrite get_id_tr_app. ss. rewrite Pos.eqb_refl. rewrite app_length. ss.
                do 2 f_equal. apply nat64_int64_add_one.
                subst ttr. clear - BOUND. unfold get_id_tr. eapply Z.le_lt_trans; eauto.
                eapply inj_le. rewrite app_length. etransitivity. eapply list_length_filter_le.
                apply Nat.le_add_r.
              }
            * eapply Mem.load_unchanged_on. eapply UCH2.
              { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
              erewrite mem_delta_apply_wf_mem_load.
              2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
              2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
              2:{ auto. }
              ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
              { rewrite WFC8. rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. auto. }
              { left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
              }

        - move FREEENV after COMP_SAME. move WFC1 after FREEENV. move WFC4 after FREEENV.
          hexploit wunchanged_on_exists_mem_free_list_2. eapply FREEENV.
          instantiate (2:=ge_c). eapply UCH7. ss.
          intros (m_c' & FREE2). esplits. eapply FREE2.
          eapply wf_c_cont_wunchanged_on_2. eapply WFC1.
          eapply wunchanged_on_free_list_preserves_gen. 2,3: eauto. auto.
        - move WFNB after UCH7. eapply wf_c_nb_wunchanged_on; eauto.
      }
      { ss. exists j2. splits; auto.
        2:{ unfold match_cur_fun. splits; eauto. }
        { unfold match_mem. splits; auto. move DELTA after UCH7. move EC after UCH7.
          eapply meminj_not_alloc_delta in MM2. 2: eapply DELTA.
          eapply meminj_not_alloc_external_call. eapply MM2. eauto.
        }
        { ii. assert (NINJP: (meminj_public ge_i) b = None).
          { move MCNTS after UCH7. specialize (MCNTS _ _ _ H H0 b ofs).
            destruct (meminj_public ge_i b) eqn:CASES; ss. exfalso.
            destruct p. move MM1 after UCH7. move INCR2 after UCH7.
            unfold inject_incr in *. hexploit MM1. apply CASES. hexploit INCR2. apply CASES.
            i. rewrite H1 in H2. clarify.
          }
          specialize (INJ_SEP _ _ _ NINJP H1). des. apply INJ_SEP0.
          hexploit Genv.genv_symb_range. eapply H0. intros RANGE.
          move WFNB before RANGE.
          hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros T1.
          hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros T2.
          eapply wunchanged_on_nextblock in T1, T2. revert_until NINJP. clear. i.
          unfold wf_c_nb in WFNB. unfold Mem.valid_block. eapply Plt_Ple_trans. eauto.
          etransitivity. eapply WFNB. etransitivity; eauto.
        }
      }
    }

    Unshelve. all: exact (fun _ _ => True).
  Qed.

  Lemma ir_to_clight_step_4
        ge_i ge_c
        (WFGE : wf_ge ge_i)
        cnts pars k_i cur m_i pretr btr tr ef d vargs id_cur
        (BOUND : Z.of_nat
                   (Datatypes.length
                      (pretr ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: btr)) <
                   Int64.modulus)
        k_c id f stmt k0 e le m_c
        (MS0 : match_genv ge_i ge_c)
        (MS1 : match_mem ge_i k_c m_i m_c)
        (MS2 : match_cur_fun ge_i ge_c cur f id)
        (MS4 : match_cont ge_c
                          (pretr ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: btr) cnts
                          k0 k_i)
        (MS3 : match_find_def ge_i ge_c cnts pars
                              (pretr ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: btr))
        (MS5 : match_params pars ge_c ge_i)
        (MCNTS : match_cnts cnts ge_c k_c)
        (CNT_INJ : forall (id0 id1 : positive) (cnt : ident),
            cnts ! id0 = Some cnt -> cnts ! id1 = Some cnt -> id0 = id1)
        (WFC0 : forall (id : ident) (b : block) gd,
            Genv.find_symbol ge_i id = Some b ->
            Genv.find_def ge_i b = Some gd ->
            exists cnt : ident,
              cnts ! id = Some cnt /\
                wf_counter ge_c m_c (comp_of gd) (Datatypes.length (get_id_tr pretr id)) cnt)
        m_freeenv
        (FREEENV : Mem.free_list m_c (blocks_of_env ge_c e) (comp_of f) = Some m_freeenv)
        (WFC1 : wf_c_cont ge_c m_freeenv k0)
        (WFC2 : wf_c_stmt ge_c (comp_of f) cnts id
                          (pretr ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: btr) stmt)
        (WFC3 : wf_env ge_c e)
        (WFC4 : not_global_blks ge_c (blocks_of_env2 ge_c e))
        (WFNB : wf_c_nb ge_c m_c)
        m2 m1' vretv
        (MEM : mem_delta_apply_wf ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) d (Some m_i) =
                 Some m1')
        (ALLOWED : comp_of ef = Genv.find_comp ge_i (Vptr cur Ptrofs.zero))
        (EC : external_call ef ge_i vargs m1' tr vretv m2)
        (ECCASES : external_call_unknowns ef ge_i m1' vargs \/
                     external_call_known_observables ef ge_i m1' vargs tr vretv m2 /\ d = [])
        (IDCUR : Genv.invert_symbol ge_i cur = Some id_cur)
    :
  exists cst2 : state,
    star step1 ge_c (State f stmt k0 e le m_c)
      (unbundle (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d)) cst2 /\
    ((exists id' : positive,
        wf_c_state ge_i ge_c
          (pretr ++ [(id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d)])
          (pretr ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: btr) cnts
          id' cst2 /\
        (exists k : meminj,
           match_state ge_i ge_c k
             (pretr ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: btr)
             cnts pars id' (Some (cur, m2, k_i)) cst2)) \/ Some (cur, m2, k_i) = None).
  Proof.
    assert (id = id_cur).
    { unfold match_cur_fun in MS2. desH MS2. rewrite MS7 in IDCUR. clarify. }
    subst id.
    destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).

    set (pretr ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: btr) as ttr in *.
    assert (FIND_CUR_I: Genv.find_symbol ge_i id_cur = Some cur).
    { apply Genv.invert_find_symbol in IDCUR. auto. }
    assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
    { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1 in FIND_CUR_I. auto. }
    assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
    { auto. }

    exploit WFC0. eapply FIND_CUR_I. rewrite <- Genv.find_funct_ptr_iff; eapply FINDF_I_CUR.
    intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
    assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: (get_id_tr btr id_cur)).
    { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
    assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
    { rewrite map_length. eapply Z.le_lt_trans. 2: eauto. unfold get_id_tr.
      apply inj_le. apply list_length_filter_le.
    }
    destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).

    hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply INV_CUR. eauto.
    intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
    rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
    assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
    { unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss. }
    assert (COMP_CUR_EQ: comp_of (@Gfun _ unit (AST.Internal f_i_cur)) = comp_of f).
    { subst f. ss. }
    setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_VA. setoid_rewrite COMP_CUR_EQ in CNT_CUR_MEM_LOAD.

    hexploit switch_spec.
    { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
    { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3.  }
    eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
    { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
    instantiate (1:=le).
    instantiate (1:= (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)).
    instantiate (1:=Sreturn None).
    intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).
    assert (COMP_SAME: comp_of f = comp_of ef).
    { rewrite ALLOWED. apply CP_CUR. }
    rename MEM into DELTA. move ECCASES after CUR_SWITCH_STAR.

    desH ECCASES; cycle 1.

    (* Case 4-1: observable defined external calls *)
    { subst d. unfold mem_delta_apply_wf in DELTA. simpl in DELTA. inversion DELTA; clear DELTA. subst m1'.
      hexploit exists_vargs_vres_2. eapply MS0. eapply ECCASES. eauto. intros (vargs2 & vretv2 & EVALS & EXT2).
      eapply star_cut_middle. exists E0.
      eexists. split.
      { unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
        eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
        unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
        rewrite ! (match_symbs_code_bundle_builtin ge_i ge_c) in CUR_SWITCH_STAR.
        rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
        eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
        clear BOUND2 CUR_SWITCH_STAR.
        unfold code_bundle_builtin. eapply star_trans. eapply code_mem_delta_correct. auto.
        { unfold mem_delta_apply_wf. simpl. reflexivity. }
        econs 1. ss.
      }
      clear BOUND2 CUR_SWITCH_STAR.
      do 2 eexists. split. econs 2.
      { eapply step_builtin. ss.
        { eapply EVALS. }
        { auto. }
        { eapply EXT2. }
      }
      econs 2. eapply step_skip_or_continue_loop1. left; auto.
      econs 2. eapply step_skip_loop2.
      econs 1. all: ss.
      splits.
      2:{ unfold unbundle. ss. traceEq. }

      left. exists id_cur. split.
      { splits; auto.
        - unfold wf_counters. split; auto.
          move WFC0 after COMP_SAME. ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
          unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
          exists b0. splits; auto.
          + eapply mem_valid_access_wunchanged_on. eapply WFC7.
            eapply store_wunchanged_on. eapply CNT_CUR_STORE. instantiate (1:= fun _ _ => True). ss.
          + destruct (Pos.eq_dec id id_cur).
            * subst id. assert (cnt_cur = cnt).
              { rewrite WFC0 in CNTS_CUR. clarify. }
              subst cnt. assert (b0 = cnt_cur_b).
              { setoid_rewrite WFC6 in FIND_CNT_CUR. clarify. }
              subst b0. assert (b = cur).
              { rewrite FIND_CUR_I in H. clarify. }
              subst b. assert (gd = Gfun (AST.Internal f_i_cur)).
              { apply Genv.find_funct_ptr_iff in FINDF_I_CUR. setoid_rewrite FINDF_I_CUR in H0. clarify. }
              subst gd.
              ss. erewrite Mem.load_store_same.
              2: setoid_rewrite COMP_CUR_EQ; eapply CNT_CUR_STORE.
              ss. rewrite map_length. rewrite get_id_tr_app. ss.
              rewrite Pos.eqb_refl. rewrite app_length. ss.
              do 2 f_equal. apply nat64_int64_add_one.
              subst ttr. clear - BOUND. unfold get_id_tr. eapply Z.le_lt_trans; eauto.
              eapply inj_le. rewrite app_length. etransitivity. eapply list_length_filter_le.
              apply Nat.le_add_r.
            * ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
              2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                  rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                  specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
              }
              rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. rewrite WFC8. auto.
        - hexploit wunchanged_on_exists_mem_free_list.
          { eapply store_wunchanged_on. eapply CNT_CUR_STORE. }
          eapply FREEENV. intros (m_f & FREE2). esplits. eapply FREE2.
          eapply wf_c_cont_wunchanged_on. eapply WFC1. 
          hexploit wunchanged_on_free_list_preserves. 2: eapply FREEENV. 2: eapply FREE2. 2: auto.
          eapply store_wunchanged_on. eapply CNT_CUR_STORE.
        - move WFC2 after COMP_SAME. unfold wf_c_stmt in *. i. rewrite CNTS_CUR in H. inv H. rename cnt into cnt_cur. ss.
        - move WFNB after COMP_SAME. unfold wf_c_nb in *. erewrite Mem.nextblock_store. eapply WFNB. eapply CNT_CUR_STORE.
      }
      { ss. exists k_c. splits; auto.
        2:{ unfold match_cur_fun. splits; eauto. }
        move MS1 after COMP_SAME. move MCNTS after COMP_SAME. destruct MS1 as (MM0 & MM1 & MM2).
        assert (m2 = m_i).
        { eapply known_obs_preserves_mem. eapply ECCASES. }
        subst m2. unfold match_mem. splits; auto.
        { eapply Mem.store_outside_inject. eapply MM0. 2: eapply CNT_CUR_STORE. ss. i.
          unfold match_cnts in MCNTS. eapply MCNTS. 3: eapply H. all: eauto.
        }
      }
    }

    (* Case 4-2: observables unknown external calls *)
    { hexploit external_call_unknowns_fo. eapply ECCASES. intros FO_I.
      hexploit external_call_unknowns_val_inject_list. eapply ECCASES. intros ARGS_INJ.
      move MS1 after ARGS_INJ. destruct MS1 as (MM0 & MM1 & MM2).
      hexploit mem_delta_apply_establish_inject_preprocess2.
      eapply MM0. eapply CNT_CUR_STORE. 2: eapply MM1. 2: eapply MM2.
      2: eapply DELTA.
      2:{ apply meminj_first_order_public_first_order. auto. }
      { clear CUR_SWITCH_STAR CNT_CUR_STORE. ii. erewrite match_symbs_meminj_public in H.
        2:{ destruct MS0 as (MS & _). apply MS. }
        unfold meminj_public in H. des_ifs.
        eapply Senv.find_invert_symbol in FIND_CNT_CUR. rewrite FIND_CNT_CUR in Heq. clarify.
      }
      intros (m_next0 & DELTA_C & INJ0).
      hexploit external_call_mem_inject_gen.
      { eapply match_symbs_symbols_inject. destruct MS0 as (MS & _). apply MS. }
      apply EC. apply INJ0. apply ARGS_INJ.
      intros (j2 & vres2 & m_next & EC2 & RET_INJ & INJ2 & UCH0 & UCH1 & INCR2 & INJ_SEP).

      exists (State f stmt k0 e le m_next). split.
      { unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
        eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
        unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
        rewrite ! (match_symbs_code_bundle_builtin ge_i ge_c) in CUR_SWITCH_STAR.
        rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
        eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
        clear BOUND2 CUR_SWITCH_STAR CNT_CUR_STORE.
        unfold code_bundle_builtin. eapply star_trans. eapply code_mem_delta_correct. auto.
        { erewrite <- match_symbs_mem_delta_apply_wf. rewrite CP_CUR. eapply DELTA_C.
          destruct MS0 as (MSYMB & _). auto.
        }
        2: ss. unfold unbundle. simpl.
        econs 2. eapply step_builtin.
        { eapply match_symbs_vals_public_eval_to_vargs_2; auto.
          destruct MS0 as (MS0 & _). auto. eapply extcall_unkowns_vals_public; eauto.
        }
        { auto. }
        { eapply EC2. }
        econs 2. eapply step_skip_or_continue_loop1. left; auto.
        econs 2. eapply step_skip_loop2. econs 1. all: ss. traceEq.
      }

      clear CUR_SWITCH_STAR BOUND2.
      assert (UCH2: Mem.unchanged_on (fun b _ => forall b0 ofs0, (meminj_public ge_i) b0 <> Some (b, ofs0)) m_next0 m_next).
      { eapply Mem.unchanged_on_implies. eapply UCH1. ii. eapply H; eauto. }
      assert (UCH3: Mem.unchanged_on (fun b _ => Senv.invert_symbol ge_c b = None) m_next0 m_next).
      { eapply Mem.unchanged_on_implies. eapply UCH2. ss. i. unfold meminj_public. des_ifs. ii. clarify.
        apply Senv.invert_find_symbol in Heq. destruct MS0 as ((MSE1 & MSE2 & MSE3) & _). apply MSE2 in Heq.
        apply Senv.find_invert_symbol in Heq. setoid_rewrite H in Heq. ss.
      }
      eapply mem_unchanged_wunchanged in UCH3.
      hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros UCH4.
      hexploit wunchanged_on_trans. eapply UCH4. eapply UCH3. intros UCH5.
      hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros UCH6.
      hexploit wunchanged_on_trans. eapply UCH6. eapply UCH5. intros UCH7.
      clear UCH3 UCH4 UCH5 UCH6.
      left. exists id_cur. split.
      { ss. splits; auto.
        - unfold wf_counters. split; auto.
          move WFC0 after COMP_SAME. ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
          unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
          exists b0. splits; auto.
          + move MCNTS after COMP_SAME.
            eapply mem_valid_access_wunchanged_on. 2: eapply mem_unchanged_wunchanged; eapply UCH2.
            eapply mem_delta_apply_wf_valid_access. eapply DELTA_C.
            eapply mem_valid_access_wunchanged_on. 2: eapply store_wunchanged_on; eapply CNT_CUR_STORE.
            auto. instantiate (1:= fun _ _ => True). ss.
            ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto.
          + destruct (Pos.eq_dec id id_cur).
            * subst id. assert (cnt_cur = cnt).
              { rewrite WFC0 in CNTS_CUR. clarify. }
              subst cnt. assert (b0 = cnt_cur_b).
              { setoid_rewrite WFC6 in FIND_CNT_CUR. clarify. }
              subst b0. assert (b = cur).
              { rewrite FIND_CUR_I in H. clarify. }
              subst b. assert (gd = Gfun (AST.Internal f_i_cur)).
              { apply Genv.find_funct_ptr_iff in FINDF_I_CUR. setoid_rewrite FINDF_I_CUR in H0. clarify. }
              subst gd.
              ss. eapply Mem.load_unchanged_on. eapply UCH2.
              { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
              erewrite mem_delta_apply_wf_mem_load.
              2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
              2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
              2:{ auto. }
              erewrite Mem.load_store_same.
              2: setoid_rewrite COMP_CUR_EQ; eapply CNT_CUR_STORE.
              { ss. rewrite map_length. rewrite get_id_tr_app. ss. rewrite Pos.eqb_refl. rewrite app_length. ss.
                do 2 f_equal. apply nat64_int64_add_one.
                subst ttr. clear - BOUND. unfold get_id_tr. eapply Z.le_lt_trans; eauto.
                eapply inj_le. rewrite app_length. etransitivity. eapply list_length_filter_le.
                apply Nat.le_add_r.
              }
            * eapply Mem.load_unchanged_on. eapply UCH2.
              { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
              erewrite mem_delta_apply_wf_mem_load.
              2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
              2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
              2:{ auto. }
              ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
              { rewrite WFC8. rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. auto. }
              { left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
              }

        - move FREEENV after COMP_SAME. move WFC1 after FREEENV. move WFC4 after FREEENV.
          hexploit wunchanged_on_exists_mem_free_list_2. eapply FREEENV.
          instantiate (2:=ge_c). eapply UCH7. ss.
          intros (m_c' & FREE2). esplits. eapply FREE2.
          eapply wf_c_cont_wunchanged_on_2. eapply WFC1.
          eapply wunchanged_on_free_list_preserves_gen. 2,3: eauto. auto.
        - move WFNB after UCH7. eapply wf_c_nb_wunchanged_on; eauto.
      }
      { ss. exists j2. splits; auto.
        2:{ unfold match_cur_fun. splits; eauto. }
        { unfold match_mem. splits; auto. move DELTA after UCH7. move EC after UCH7.
          eapply meminj_not_alloc_delta in MM2. 2: eapply DELTA.
          eapply meminj_not_alloc_external_call. eapply MM2. eauto.
        }
        { ii. assert (NINJP: (meminj_public ge_i) b = None).
          { move MCNTS after UCH7. specialize (MCNTS _ _ _ H H0 b ofs).
            destruct (meminj_public ge_i b) eqn:CASES; ss. exfalso.
            destruct p. move MM1 after UCH7. move INCR2 after UCH7.
            unfold inject_incr in *. hexploit MM1. apply CASES. hexploit INCR2. apply CASES.
            i. rewrite H1 in H2. clarify.
          }
          specialize (INJ_SEP _ _ _ NINJP H1). des. apply INJ_SEP0.
          hexploit Genv.genv_symb_range. eapply H0. intros RANGE.
          move WFNB before RANGE.
          hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros T1.
          hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros T2.
          eapply wunchanged_on_nextblock in T1, T2. revert_until NINJP. clear. i.
          unfold wf_c_nb in WFNB. unfold Mem.valid_block. eapply Plt_Ple_trans. eauto.
          etransitivity. eapply WFNB. etransitivity; eauto.
        }
      }
    }

    Unshelve. all: exact (fun _ _ => True).
  Qed.

  Lemma ir_to_clight_step
        (ge_i: Asm.genv) (ge_c: Clight.genv)
        (WFGE: wf_ge ge_i)
        cnts pars ist1 ev ist2
        (STEP: ir_step ge_i ist1 ev ist2)
        ttr pretr btr
        (BOUND: Z.of_nat (Datatypes.length ttr) < Int64.modulus)
        (TOTAL: ttr = pretr ++ ev :: btr)
        cst1 k id
        (WFC: wf_c_state ge_i ge_c pretr ttr cnts id cst1)
        (MS: match_state ge_i ge_c k ttr cnts pars id ist1 cst1)
    :
    exists cst2, (star step1 ge_c cst1 (unbundle ev) cst2) /\
              ((exists id', (wf_c_state ge_i ge_c (pretr ++ [ev]) ttr cnts id' cst2) /\
                         exists k, (match_state ge_i ge_c k ttr cnts pars id' ist2 cst2))
               \/ (ist2 = None)).
  Proof.
    unfold wf_c_state in WFC. des_ifs. rename s into stmt, k into k_c, m into m_c.
    destruct WFC as ((CNT_INJ & WFC0) & (m_freeenv & FREEENV & WFC1) & WFC2 & WFC3 & WFC4 & WFNB).
    unfold match_state in MS. des_ifs. rename i into k_i, b into cur, m into m_i.
    destruct MS as (MS0 & MS1 & MS2 & MS3 & MS4 & MS5 & MCNTS).
    move STEP after WFC4. inv STEP.

    (** Case 1: Cross Call *)
    - eapply ir_to_clight_step_1; eauto.

    (** Case 2: Cross Return *)
    - eapply ir_to_clight_step_2; eauto.

    (** Case 3: Internal-External Call *)
    - eapply ir_to_clight_step_3; eauto.

    (** Case 4: Builtins *)
    - eapply ir_to_clight_step_4; eauto.

    (** Case 5: Cross Call External 1 *)
    - hexploit ir_to_clight_step_cce_1; eauto.
      { unfold mem_delta_apply_wf. ss. }
      { exists []. rewrite app_nil_r. auto. }
      intros (cnt_cur & cnt_cur_b & (CNT_CUR & FIND_CNT & CNT_CUR_NP) & m_c' & STAR & MEM).
      destruct MEM as (m_cu & CNT_CUR_STORE & DELTA_NIL & DELTA_PUB).
      eapply star_cut_middle. esplits.
      { eapply STAR. }
      { econs 1. }
      { ss. right; auto. }
      { unfold unbundle. ss. traceEq. }

    (** Case 6: Cross Call External 2 *)
    - hexploit ir_to_clight_step_cce_2; eauto.
      { exists []. rewrite app_nil_r. auto. }
      rename MEM into DELTA.
      intros (cnt_cur & cnt_cur_b & (CNT_CUR & FIND_CNT & CNT_CUR_NP) & m_c' & STAR & MEM).
      destruct STAR as (vres & m_next & STAR & EC2).
      destruct MEM as (m_cu & CNT_CUR_STORE & DELTA_NIL & DELTA_PUB).
      eapply star_cut_middle. esplits.
      { eapply STAR. }
      { econs 1. }
      { ss. right; auto. }
      { unfold unbundle. ss. traceEq. }

    (** Case 7: Cross Call External 3 *)
    - hexploit ir_to_clight_step_cce_2; eauto.
      rename MEM into DELTA.
      intros (cnt_cur & cnt_cur_b & (CNT_CUR & FIND_CNT & CNT_CUR_NP) & m_c' & STAR & MEM).
      destruct STAR as (vres & m_next & STAR & EC2).
      destruct MEM as (m_cu & CNT_CUR_STORE & DELTA_NIL & DELTA_PUB).

      assert (id = id_cur).
      { unfold match_cur_fun in MS2. desH MS2. rewrite MS7 in IDCUR. clarify. }
      subst id.
      assert (COMP_CUR_F: (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) = comp_of f).
      { destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).
        hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply INV_CUR. eauto.
        intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
        unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss.
      }
      assert (FIND_CUR_I: Genv.find_symbol ge_i id_cur = Some cur).
      { apply Genv.invert_find_symbol in IDCUR. auto. }
      assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
      { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1 in FIND_CUR_I. auto. }
      assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
      { destruct MS2 as (MFUN0 & MFUN1). auto. }
      assert (COMP_CUR_EQ: (comp_of (@Gfun _ unit (AST.Internal f_cur))) = comp_of f).
      { rewrite <- COMP_CUR_F. unfold Genv.find_comp. setoid_rewrite INTERNAL. ss. }
      desH ECCASES; cycle 1.

      (* Case 3-1: observable defined external calls *)
      { clear DELTA_PUB. subst d. specialize (DELTA_NIL eq_refl). subst m_c'.
        hexploit exists_vargs_vres. apply MS0. apply ECCASES. eauto. intros (_ & EC2').
        hexploit external_call_deterministic. eapply EC2. eapply EC2'. intros (EQ1 & EQ2).
        subst vres m_cu. clear EC2'.
        eapply star_cut_middle. esplits. eapply STAR.
        econs 2.
        { eapply step_returnstate.
          - i. apply NPTR0. rewrite COMP_CUR_F. apply H.
          - move TR3 after COMP_CUR_F. rewrite COMP_CUR_F in TR3. instantiate (1:=tr3).
            inv TR3. econs; [auto |]. ss.
            erewrite proj_rettype_to_type_rettype_of_type_eq. 2: apply H0.
            eapply match_symbs_eventval_match. apply MS0. auto.
        }
        ss. econs 2.
        { eapply step_skip_or_continue_loop1. auto. }
        econs 2.
        { eapply step_skip_loop2. }
        econs 1. all: ss.
        2:{ unfold unbundle. ss. traceEq. }
        left. exists id_cur. clear STAR. split.

        - splits; auto.
          { unfold wf_counters. split; auto.
            move WFC0 after COMP_CUR_F. i. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
            unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
            exists b1. splits; auto.
            + eapply mem_valid_access_wunchanged_on. eapply WFC7.
              eapply store_wunchanged_on. eapply CNT_CUR_STORE. instantiate (1:= fun _ _ => True). ss.
            + destruct (Pos.eq_dec id id_cur).
              * subst id. assert (cnt_cur = cnt).
                { rewrite WFC0 in CNT_CUR. clarify. }
                subst cnt. assert (b1 = cnt_cur_b).
                { setoid_rewrite WFC6 in FIND_CNT. clarify. }
                subst b1. assert (b0 = cur).
                { rewrite FIND_CUR_I in H. clarify. }
                subst b0. assert (gd = Gfun (AST.Internal f_cur)).
                { apply Genv.find_funct_ptr_iff in INTERNAL. setoid_rewrite INTERNAL in H0. clarify. }
                subst gd.
                ss. erewrite Mem.load_store_same.
                2: setoid_rewrite COMP_CUR_EQ; eapply CNT_CUR_STORE.
                ss. rewrite map_length. rewrite get_id_tr_app. ss.
                rewrite Pos.eqb_refl. rewrite app_length. ss.
                do 2 f_equal. apply nat64_int64_add_one.
                clear - BOUND. unfold get_id_tr. eapply Z.le_lt_trans; eauto.
                eapply inj_le. rewrite app_length. etransitivity. eapply list_length_filter_le.
                apply Nat.le_add_r.
              * ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
                2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT, WFC6.
                    rewrite FIND_CNT in WFC6. clarify. rename cnt into cnt_cur.
                    specialize (CNT_INJ _ _ _ CNT_CUR WFC0). clarify.
                }
                rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n.
                rewrite app_nil_r. rewrite WFC8. auto.
          }
          { hexploit wunchanged_on_exists_mem_free_list.
            { eapply store_wunchanged_on. eapply CNT_CUR_STORE. }
            eapply FREEENV. intros (m_f & FREE2). esplits. eapply FREE2.
            eapply wf_c_cont_wunchanged_on. eapply WFC1. 
            hexploit wunchanged_on_free_list_preserves. 2: eapply FREEENV. 2: eapply FREE2. 2: auto.
            eapply store_wunchanged_on. eapply CNT_CUR_STORE.
          }
          { ii. rewrite CNT_CUR in H. inv H. ss. }
          { move WFNB after FIND_FUN_C. unfold wf_c_nb in *. erewrite Mem.nextblock_store. eapply WFNB. eapply CNT_CUR_STORE.
          }
        - exists k_c. splits; auto.
          move MS1 after FIND_FUN_C. move MCNTS after MS1. destruct MS1 as (MM0 & MM1 & MM2).
          unfold mem_delta_apply_wf in DELTA. ss. inv DELTA.
          assert (m2 = m1').
          { eapply known_obs_preserves_mem. eapply ECCASES. }
          subst m1'. unfold match_mem. splits; auto.
          eapply Mem.store_outside_inject. eapply MM0. 2: eapply CNT_CUR_STORE. ss. i.
          unfold match_cnts in MCNTS. eapply MCNTS. 3: eapply H. all: eauto.
      }

      (* Case 3-2: observables unknown external calls *)
      { hexploit external_call_unknowns_fo. eapply ECCASES. intros FO_I.
        hexploit external_call_unknowns_val_inject_list. eapply ECCASES. intros ARGS_INJ.
        hexploit meminj_first_order_public_first_order. apply FO_I. intros PFO.
        clear DELTA_NIL. specialize (DELTA_PUB PFO). desH DELTA_PUB. rename DELTA_PUB0 into INJ0.
        move MS1 after ARGS_INJ. destruct MS1 as (MM0 & MM1 & MM2).
        hexploit external_call_mem_inject_gen.
        { eapply match_symbs_symbols_inject. destruct MS0 as (MS & _). apply MS. }
        apply TR2. apply INJ0. apply ARGS_INJ.
        intros (j2 & vres2 & m_next' & EC2' & RET_INJ & INJ2 & UCH0 & UCH1 & INCR2 & INJ_SEP).
        hexploit external_call_deterministic. eapply EC2. eapply EC2'. intros (EQ1 & EQ2).
        subst vres m_next'. clear EC2'.
        eapply star_cut_middle. esplits. eapply STAR.
        econs 2.
        { assert (CROSS_I: crossing_comp ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) (comp_of ef)).
          { move TR1 after INJ_SEP. inv TR1. apply H. }
          assert (NPTR': not_ptr vretv).
          { apply NPTR0. auto. }
          eapply step_returnstate.
          - i. eapply val_inject_not_ptr; eauto.
          - move TR3 after COMP_CUR_F. rewrite COMP_CUR_F in TR3. instantiate (1:=tr3).
            inv TR3. econs; [auto |]. ss.
            erewrite proj_rettype_to_type_rettype_of_type_eq. 2: apply H0.

            hexploit not_ptr_val_inject_eq; eauto. i; subst vres2.
            eapply match_symbs_eventval_match. apply MS0. auto.
        }
        econs 2. eapply step_skip_or_continue_loop1. left; auto. econs 2. eapply step_skip_loop2.
        econs 1. all: ss.
        2:{ unfold unbundle. ss. traceEq. }

        rename m_c' into m_next0. rename DELTA_PUB into DELTA_C.
        assert (UCH2: Mem.unchanged_on (fun b _ => forall b0 ofs0, (meminj_public ge_i) b0 <> Some (b, ofs0)) m_next0 m_next).
        { eapply Mem.unchanged_on_implies. eapply UCH1. ii. eapply H; eauto. }
        assert (UCH3: Mem.unchanged_on (fun b _ => Senv.invert_symbol ge_c b = None) m_next0 m_next).
        { eapply Mem.unchanged_on_implies. eapply UCH2. ss. i. unfold meminj_public. des_ifs. ii. clarify.
          apply Senv.invert_find_symbol in Heq. destruct MS0 as ((MSE1 & MSE2 & MSE3) & _). apply MSE2 in Heq.
          apply Senv.find_invert_symbol in Heq. setoid_rewrite H in Heq. ss.
        }
        eapply mem_unchanged_wunchanged in UCH3.
        hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros UCH4.
        hexploit wunchanged_on_trans. eapply UCH4. eapply UCH3. intros UCH5.
        hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros UCH6.
        hexploit wunchanged_on_trans. eapply UCH6. eapply UCH5. intros UCH7.
        clear UCH3 UCH4 UCH5 UCH6.

        left. exists id_cur. clear STAR. split.
        { ss. splits; auto.
          - unfold wf_counters. split; auto.
            move WFC0 after INJ_SEP. ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
            unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
            exists b1. splits; auto.
            + move MCNTS after INJ_SEP.
              eapply mem_valid_access_wunchanged_on.
              2: eapply mem_unchanged_wunchanged; eapply UCH2.
              eapply mem_delta_apply_wf_valid_access. eapply DELTA_C.
              eapply mem_valid_access_wunchanged_on. 2: eapply store_wunchanged_on; eapply CNT_CUR_STORE.
              auto. instantiate (1:= fun _ _ => True). ss.
              ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto.
            + destruct (Pos.eq_dec id id_cur).
              * subst id. assert (cnt_cur = cnt).
                { rewrite WFC0 in CNT_CUR. clarify. }
                subst cnt. assert (b1 = cnt_cur_b).
                { setoid_rewrite WFC6 in FIND_CNT. clarify. }
                subst b1. assert (b0 = cur).
                { rewrite FIND_CUR_I in H. clarify. }
                subst b0. assert (gd = Gfun (AST.Internal f_cur)).
                { apply Genv.find_funct_ptr_iff in INTERNAL. setoid_rewrite INTERNAL in H0. clarify. }
                subst gd.
                ss. eapply Mem.load_unchanged_on. eapply UCH2.
                { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
                erewrite mem_delta_apply_wf_mem_load.
                2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
                2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
                2:{ auto. }
                erewrite Mem.load_store_same.
                2: setoid_rewrite COMP_CUR_EQ; eapply CNT_CUR_STORE.
                { ss. rewrite map_length. rewrite get_id_tr_app. ss. rewrite Pos.eqb_refl. rewrite app_length. ss.
                  do 2 f_equal. apply nat64_int64_add_one.
                  clear - BOUND. unfold get_id_tr. eapply Z.le_lt_trans; eauto.
                  eapply inj_le. rewrite app_length. etransitivity. eapply list_length_filter_le.
                  apply Nat.le_add_r.
                }
              * eapply Mem.load_unchanged_on. eapply UCH2.
                { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
                erewrite mem_delta_apply_wf_mem_load.
                2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
                2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
                2:{ auto. }
                ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
                { rewrite WFC8. rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. auto. }
                { left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT, WFC6.
                  rewrite FIND_CNT in WFC6. clarify. rename cnt into cnt_cur.
                  specialize (CNT_INJ _ _ _ CNT_CUR WFC0). clarify.
                }

          - move FREEENV after INJ_SEP. move WFC1 after FREEENV. move WFC4 after FREEENV.
            hexploit wunchanged_on_exists_mem_free_list_2. eapply FREEENV.
            instantiate (2:=ge_c). eapply UCH7. ss.
            intros (m_c' & FREE2). esplits. eapply FREE2.
            eapply wf_c_cont_wunchanged_on_2. eapply WFC1.
            eapply wunchanged_on_free_list_preserves_gen. 2,3: eauto. auto.
          - ii. rewrite CNT_CUR in H. inv H. ss.
          - move WFNB after UCH7. eapply wf_c_nb_wunchanged_on; eauto.
        }
        { exists j2. splits; auto.
          { unfold match_mem. splits; auto. move DELTA after UCH7. move TR2 after UCH7.
            eapply meminj_not_alloc_delta in MM2. 2: eapply DELTA.
            eapply meminj_not_alloc_external_call. eapply MM2. eauto.
          }
          { ii. assert (NINJP: (meminj_public ge_i) b0 = None).
            { move MCNTS after UCH7. specialize (MCNTS _ _ _ H H0 b0 ofs).
              destruct (meminj_public ge_i b0) eqn:CASES; ss. exfalso.
              destruct p. move MM1 after UCH7. move INCR2 after UCH7.
              unfold inject_incr in *. hexploit MM1. apply CASES. hexploit INCR2. apply CASES.
              i. rewrite H1 in H2. clarify.
            }
            specialize (INJ_SEP _ _ _ NINJP H1). des. apply INJ_SEP0.
            hexploit Genv.genv_symb_range. eapply H0. intros RANGE.
            move WFNB before RANGE.
            hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros T1.
            hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros T2.
            eapply wunchanged_on_nextblock in T1, T2. revert_until NINJP. clear. i.
            unfold wf_c_nb in WFNB. unfold Mem.valid_block. eapply Plt_Ple_trans. eauto.
            etransitivity. eapply WFNB. etransitivity; eauto.
          }
        }
      }

      Unshelve. all: try exact (fun _ _ => True). exact 1%positive. exact le.
  Qed.

  Lemma ir_to_clight_aux
        (ge_i: Asm.genv) (ge_c: Clight.genv)
        (WFGE: wf_ge ge_i)
        (pretr: bundle_trace)
        pist ist
        (PREIR: istar (ir_step) ge_i pist pretr ist)
        pcst cst
        (PREC: star step1 ge_c pcst (unbundle_trace pretr) cst)
        ttr cnts pars k id
        (BOUND: Z.of_nat (Datatypes.length ttr) < Int64.modulus)
        (WFC: wf_c_state ge_i ge_c pretr ttr cnts id cst)
        (MS: match_state ge_i ge_c k ttr cnts pars id ist cst)
        btr ist'
        (TOTAL: ttr = pretr ++ btr)
        (STAR: istar (ir_step) ge_i ist btr ist')
    :
    exists cst', star step1 ge_c cst (unbundle_trace btr) cst'.
  Proof.
    revert pretr PREIR cst PREC k id WFC MS TOTAL. induction STAR; intros.
    { ss. eexists. econs 1. }
    rename H into STEP. subst t. ss.
    hexploit ir_to_clight_step; eauto. intros; des.
    - hexploit IHSTAR.
      { eapply istar_trans. eapply PREIR. econs 2. eapply STEP. econs 1. all: ss. }
      { rewrite unbundle_trace_app. eapply star_trans. eapply PREC. eapply H. ss. rewrite app_nil_r. ss. }
      eauto. eauto.
      { rewrite <- app_assoc. ss. }
      intros (cst' & INDSTAR).
      exists cst'. eapply star_trans. eapply H. eapply INDSTAR. ss.
    - subst s2. inv STAR.
      + ss. rewrite app_nil_r. eauto.
      + inv H0.
  Qed.

  Theorem ir_to_clight
          (ge_i: Asm.genv) (ge_c: Clight.genv)
          (WFGE: wf_ge ge_i)
          ist cst
          ttr cnts pars k id
          (BOUND: Z.of_nat (Datatypes.length ttr) < Int64.modulus)
          (WFC: wf_c_state ge_i ge_c [] ttr cnts id cst)
          (MS: match_state ge_i ge_c k ttr cnts pars id ist cst)
          ist'
          (STAR: istar (ir_step) ge_i ist ttr ist')
    :
    exists cst', star step1 ge_c cst (unbundle_trace ttr) cst'.
  Proof. eapply ir_to_clight_aux. eauto. 4,5,6,7: eauto. all: eauto. econs 1. econs 1. Qed.

End PROOF.
