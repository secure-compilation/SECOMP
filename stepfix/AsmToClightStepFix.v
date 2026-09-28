(* asm_to_clight and backtranslation_proof WITHOUT the admitted step_fix_fix.

   The proof script of asm_to_clight is copied verbatim from
   security/BacktranslationProof2.v on this branch (fix-13-ccs-backtranslation,
   that is, ccs-backtranslation with PR #19), lines 1305-1465.  Its single use of
   step_fix_fix ("eapply step_fix_fix. eauto.") is replaced by a hypothesis
   about the program p and prefix tr at hand:

   - stepfix_runs p tr: every Asm run from an initial state with trace tr is
     also a step_fix run (the instance of step_fix_fix for this p and tr);
   - stepfix_prefix p tr: from every initial state there is SOME step_fix run
     with trace tr (weaker; enough because the proof uses the end state of
     the run only to feed asm_to_ir, and clears it afterwards).

   The script is otherwise unchanged (plus one "destruct" for the second
   variant).  Print Assumptions shows that step_fix_fix is not used. *)
Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.
Require Import Split.
Require Import Tactics.
Require Import riscV.Asm.
Require Import BtBasics BtInfoAsm BtInfoAsmBound MemoryDelta MemoryWeak.
Require Import Ctypes Clight.
Require Import Backtranslation BacktranslationAux BacktranslationProof.
Require Import RSC.
Require Import BacktranslationProof2.

Definition stepfix_runs (p: Asm.program) (tr: trace) : Prop :=
  forall s s',
    Asm.initial_state p s ->
    star (Asm.step (comp_of_main p)) (Genv.globalenv p) s tr s' ->
    star (step_fix (comp_of_main p)) (Genv.globalenv p) s tr s'.

Definition stepfix_prefix (p: Asm.program) (tr: trace) : Prop :=
  forall s, Asm.initial_state p s ->
    exists s', star (step_fix (comp_of_main p)) (Genv.globalenv p) s tr s'.

Section STEPFIX.

  Hypothesis EFO: external_functions_observable.
  Hypothesis IAO: inline_assembly_observable.

  Lemma asm_to_clight_stepfix_runs
        (p: Asm.program)
        (WFP: wf_program p)
        (WFPP: wf_program_public p)
        (WFMAIN: wf_main p)
        (WFMAINSIG: wf_main_sig p)
        (WFINIT: exists (s : Asm.state), Asm.initial_state p s)
    :
    forall tr,
      (Z.of_nat (length tr) < Int64.modulus) ->
      asm_program_does_prefix p tr ->
      stepfix_runs p tr ->
      exists btr,
        clight_program_does_prefix (gen_program btr p) tr /\
          unbundle_trace btr = tr.
  Proof.
    i. rename H into BOUND, H0 into H, H1 into STEPFIX.
    eapply semantics_has_initial_trace_prefix_implies_cut in H.
    2:{ apply sd_traces. apply semantics_determinate. }
    inv H; cycle 1.
    { exfalso. ss. des. eapply H0. eapply WFINIT. }
    clear WFINIT. ss. des. hexploit ir_has_initial_state; eauto. intros (ist & IR_INIT).
    hexploit match_state_initial_state; eauto. intros (m0 & j & INIT_MEM_A & MS_I).
    hexploit asm_to_ir.
    { eapply wf_program_wf_ge; eauto. }
    { eapply wf_asm_initial_state; eauto. }
    { eapply STEPFIX; eauto. }
    { eapply MS_I. }
    intros (btr & ist' & UTR & ISTAR). esplits. 2: eauto.
    eapply semantics_has_initial_trace_cut_implies_prefix.
    hexploit exists_initial_state; eauto. instantiate (1:=btr).
    intros (f_cur & m_c & INIT_C & F_MAIN).
    econs 1; ss. eapply INIT_C. eapply star_state_behaves_cut.
    eexists. split.
    { econs 2. 2: econs 1. 2: traceEq. eapply step_internal_function.
      instantiate (3:=empty_env). instantiate (2:=@PTree.empty _). instantiate (1:=m_c).
      des. econs; ss. all: try rewrite F_MAIN; try rewrite F_MAIN0; try rewrite F_MAIN1; ss.
      econs. econs. econs.
    }
    clear dependent s. clear dependent s'. clear dependent m0. clear beh' j.
    inv IR_INIT. clarify. des. inv INIT_C. rewrite gen_program_prog_main_eq in *.
    remember (AST.prog_main p) as id_cur. clear Heqid_cur.
    hexploit gen_program_match_find_def; eauto. intros MFD.
    hexploit Genv.find_invert_symbol. eapply H. intros INV_A.
    dup H0. rewrite Genv.find_funct_ptr_iff in H2. specialize (MFD _ _ _ H2 INV_A).
    des_ifs. rename Heq into CNT_CUR. rename Heq0 into PAR_CUR.
    assert (b = cur).
    { eapply gen_program_symbs_find in H; eauto. ss.
      subst ge0. setoid_rewrite H5 in H. clarify. ss.
    }
    subst b. ss. rewrite <- Genv.find_funct_ptr_iff in MFD.
    assert (f_cur = (gen_function (Genv.globalenv p) (funs_data_of_defs (AST.prog_defs p)) i l (get_id_tr btr id_cur) f)).
    { subst ge0. setoid_rewrite H6 in MFD. clarify. }
    clear MFD.
    hexploit gen_program_match_genv; eauto. instantiate (1:=btr). intros MGENV.

    hexploit ir_to_clight.
    { eapply wf_program_wf_ge; eauto. }
    { eapply funs_data_of_defs_wf_fds; eauto. }
    4: eapply ISTAR.
    { hexploit bundle_trace_bounded; auto. apply ISTAR. clear - BOUND. i. lia. }
    { instantiate (1:=State f_cur (fn_body f_cur) Kstop empty_env (PTree.empty val) m_c).
      instantiate (1:=id_cur).
      instantiate (1:=(get_cnt_ids (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)))).
      instantiate (1:= globalenv (gen_program btr p)). ss. splits.
      - unfold wf_counters. split.
        { eapply gen_counter_defs_cnt_ids_inj; eauto. }
        i. assert (PDM: (prog_defmap p) ! id = Some gd).
        { rewrite Genv.find_def_symbol. esplits; eauto. }
        hexploit gen_counter_defs_inv; eauto. eapply in_prog_defmap; eauto. intros GETCNT.
        esplits.
        { unfold get_cnt_ids. rewrite PTree.gmap. rewrite GETCNT. ss. }
        set (id + next_id (AST.prog_defs p))%positive as id_cnt.
        unfold wf_counter. splits.
        { ss. assert (NIN: ~ In id_cnt (Genv.genv_public (Genv.globalenv (gen_program btr p)))).
          { ii. destruct MGENV as ((MS0 & MS1 & MS2) & EQP).
            replace (Genv.genv_public (Genv.globalenv (gen_program btr p))) with
              (AST.prog_public p) in H10.
            2:{ rewrite Genv.globalenv_public. ss. }
            apply WFPP in H10. apply list_in_map_inv in H10. des. destruct x; ss; clarify.
            apply next_id_lt in H11. lia.
          }
          unfold Genv.public_symbol. des_ifs.
          eapply (pred_dec_false (in_dec ident_eq _ _) true false) in NIN. des_ifs.
        }
        ss. assert (PDM_C: (prog_defmap (gen_program btr p)) ! id_cnt = Some (gen_counter (comp_of gd))).
        { apply prog_defmap_norepet. apply gen_program_list_norepet; auto.
          unfold gen_program. ss. unfold gen_prog_defs. apply in_or_app. right.
          apply PTree.elements_correct in GETCNT. apply (in_map snd) in GETCNT. ss.
        }
        apply Genv.find_def_symbol in PDM_C. des.
        hexploit Genv.init_mem_characterization_gen. eapply H4.
        intros GI. specialize (GI _ _ PDM_C0). ss. des.
        specialize (GI1 eq_refl). specialize (GI2 eq_refl). des.
        esplits; eauto.
        unfold Mem.valid_access. splits; auto. 2: apply Z.divide_0_r.
        eapply Mem.loadbytes_can_access_block_inj; eauto.
      - esplits; eauto. econs.
      - unfold wf_c_stmt. i. subst f_cur. ss. rewrite CNT_CUR in H8. clarify.
        replace (comp_of (gen_function (Genv.globalenv p) (funs_data_of_defs (AST.prog_defs p)) cnt [] (get_id_tr btr id_cur) f)) with
          (Asm.fn_comp f).
        2:{ ss. }
        apply match_symbs_code_bundle_trace. apply MGENV.
      - ii. des_ifs.
      - unfold not_global_blks. unfold empty_env. ss. unfold blocks_of_env2, blocks_of_env. ss.
      - unfold wf_c_nb. ss. erewrite Genv.init_mem_genv_next. reflexivity. auto.
    }
    { instantiate (1:= gen_params (next_id (map snd (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p))))) (AST.prog_defs p)).
      ss. splits.
      - auto.
      - assert (INCR: inject_incr (meminj_public (Genv.globalenv p)) (Mem.flat_inj (Mem.nextblock m0))).
        { clear - H1. ii. unfold meminj_public in H. des_ifs. ss.
          apply Genv.invert_find_symbol in Heq. unfold Genv.find_symbol in Heq.
          apply Genv.genv_symb_range in Heq. apply Genv.init_mem_genv_next in H1.
          unfold Mem.flat_inj. rewrite H1 in Heq. des_ifs.
        }
        unfold match_mem. splits; eauto.
        + eapply genv_init_mem_inj; eauto.
        + clear - INCR. ii. unfold inject_incr in INCR.
          destruct (meminj_public (Genv.globalenv p) b) eqn:CASES; auto.
          exfalso. destruct p0. specialize (INCR _ _ _ CASES). unfold Mem.flat_inj in INCR.
          des_ifs. unfold Plt in *. lia.
      - unfold match_cur_fun. ss. splits; ss. eauto.
      - eapply gen_program_match_find_def; eauto.
      - econs; auto.
      - unfold match_params. splits.
        + apply gen_params_wf.
        + ii. hexploit in_gds_exists_params. 2: eauto.
          { setoid_rewrite Genv.find_def_symbol. esplits; eauto.
            rewrite <- Genv.find_funct_ptr_iff. eauto.
          }
          i. des. rewrite H10 in H11. clarify.
        + ii. ss. hexploit Genv.find_symbol_inversion. apply H8. intros INDEF.
          apply list_in_map_inv in H10. des. destruct x; ss; clarify.
          hexploit gen_params_le. apply H9. apply H11. intros GT.
          clear - WFP INDEF GT. unfold gen_program, prog_defs_names in INDEF. ss.
          apply list_in_map_inv in INDEF. des. destruct x; ss; clarify.
          apply next_id_lt in INDEF0. unfold gen_prog_defs in INDEF0.
          assert (MAX: (max_id 
              (map
                 (fun '(id, gd) =>
                  (id,
                  gen_progdef (Genv.globalenv p) (funs_data_of_defs (AST.prog_defs p)) (get_id_tr btr id) gd
                    (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)) ! id
                    (gen_params
                       (next_id
                          (map snd
                             (PTree.elements
                                (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)))))
                       (AST.prog_defs p)) ! id)) (AST.prog_defs p) ++
               map snd
               (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)))) <=
          max_id (map snd
                      (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)))))%positive).
          { apply max_id0_app. 2: lia. clear - WFP. i. rewrite map_map in H.
            apply list_in_map_inv in H. des. destruct x; ss; clarify.
            rewrite map_map.
            hexploit gen_counter_defs_inv; eauto. intros.
            apply PTree.elements_correct in H.
            apply (in_map (fun x : positive * (ident * globdef fundef type) => fst (snd x))) in H.
            ss. eexists. split. apply H. lia.
          }
          rewrite next_id_is_succ_max_id in INDEF0, GT. lia.
      - ii. setoid_rewrite PTree.gmap in H8. unfold option_map in H8. des_ifs.
        hexploit gen_counter_defs_lt; eauto. intros LT.
        unfold Mem.flat_inj in H10. des_ifs. erewrite <- Genv.init_mem_genv_next in p0; eauto.
        hexploit Genv.find_symbol_inversion. apply H9. intros INDEFS.
        ss. hexploit genv_find_symbol_gen_program_cases. eauto. eapply H9. i. des.
        + unfold Plt in p0. lia.
        + clear - LT H3. apply list_in_map_inv in H3. des. destruct x; ss; clarify.
          hexploit next_id_lt; eauto. i. lia.
    }
    intros (cst' & STAR_C). hexploit state_behaves_exists. intros (beh2 & BEH2).
    esplits; eauto.
  Qed.


  Lemma asm_to_clight_stepfix_prefix
        (p: Asm.program)
        (WFP: wf_program p)
        (WFPP: wf_program_public p)
        (WFMAIN: wf_main p)
        (WFMAINSIG: wf_main_sig p)
        (WFINIT: exists (s : Asm.state), Asm.initial_state p s)
    :
    forall tr,
      (Z.of_nat (length tr) < Int64.modulus) ->
      asm_program_does_prefix p tr ->
      stepfix_prefix p tr ->
      exists btr,
        clight_program_does_prefix (gen_program btr p) tr /\
          unbundle_trace btr = tr.
  Proof.
    i. rename H into BOUND, H0 into H, H1 into STEPFIX.
    eapply semantics_has_initial_trace_prefix_implies_cut in H.
    2:{ apply sd_traces. apply semantics_determinate. }
    inv H; cycle 1.
    { exfalso. ss. des. eapply H0. eapply WFINIT. }
    clear WFINIT. ss. des. hexploit ir_has_initial_state; eauto. intros (ist & IR_INIT).
    hexploit match_state_initial_state; eauto. intros (m0 & j & INIT_MEM_A & MS_I).
    match goal with | [ HI: Asm.initial_state p ?s0 |- _ ] => destruct (STEPFIX _ HI) as (s_fix & STAR_FIX) end.
    hexploit asm_to_ir.
    { eapply wf_program_wf_ge; eauto. }
    { eapply wf_asm_initial_state; eauto. }
    { eapply STAR_FIX. }
    { eapply MS_I. }
    intros (btr & ist' & UTR & ISTAR). esplits. 2: eauto.
    eapply semantics_has_initial_trace_cut_implies_prefix.
    hexploit exists_initial_state; eauto. instantiate (1:=btr).
    intros (f_cur & m_c & INIT_C & F_MAIN).
    econs 1; ss. eapply INIT_C. eapply star_state_behaves_cut.
    eexists. split.
    { econs 2. 2: econs 1. 2: traceEq. eapply step_internal_function.
      instantiate (3:=empty_env). instantiate (2:=@PTree.empty _). instantiate (1:=m_c).
      des. econs; ss. all: try rewrite F_MAIN; try rewrite F_MAIN0; try rewrite F_MAIN1; ss.
      econs. econs. econs.
    }
    clear dependent s. clear dependent s'. clear dependent m0. clear beh' j.
    inv IR_INIT. clarify. des. inv INIT_C. rewrite gen_program_prog_main_eq in *.
    remember (AST.prog_main p) as id_cur. clear Heqid_cur.
    hexploit gen_program_match_find_def; eauto. intros MFD.
    hexploit Genv.find_invert_symbol. eapply H. intros INV_A.
    dup H0. rewrite Genv.find_funct_ptr_iff in H2. specialize (MFD _ _ _ H2 INV_A).
    des_ifs. rename Heq into CNT_CUR. rename Heq0 into PAR_CUR.
    assert (b = cur).
    { eapply gen_program_symbs_find in H; eauto. ss.
      subst ge0. setoid_rewrite H5 in H. clarify. ss.
    }
    subst b. ss. rewrite <- Genv.find_funct_ptr_iff in MFD.
    assert (f_cur = (gen_function (Genv.globalenv p) (funs_data_of_defs (AST.prog_defs p)) i l (get_id_tr btr id_cur) f)).
    { subst ge0. setoid_rewrite H6 in MFD. clarify. }
    clear MFD.
    hexploit gen_program_match_genv; eauto. instantiate (1:=btr). intros MGENV.

    hexploit ir_to_clight.
    { eapply wf_program_wf_ge; eauto. }
    { eapply funs_data_of_defs_wf_fds; eauto. }
    4: eapply ISTAR.
    { hexploit bundle_trace_bounded; auto. apply ISTAR. clear - BOUND. i. lia. }
    { instantiate (1:=State f_cur (fn_body f_cur) Kstop empty_env (PTree.empty val) m_c).
      instantiate (1:=id_cur).
      instantiate (1:=(get_cnt_ids (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)))).
      instantiate (1:= globalenv (gen_program btr p)). ss. splits.
      - unfold wf_counters. split.
        { eapply gen_counter_defs_cnt_ids_inj; eauto. }
        i. assert (PDM: (prog_defmap p) ! id = Some gd).
        { rewrite Genv.find_def_symbol. esplits; eauto. }
        hexploit gen_counter_defs_inv; eauto. eapply in_prog_defmap; eauto. intros GETCNT.
        esplits.
        { unfold get_cnt_ids. rewrite PTree.gmap. rewrite GETCNT. ss. }
        set (id + next_id (AST.prog_defs p))%positive as id_cnt.
        unfold wf_counter. splits.
        { ss. assert (NIN: ~ In id_cnt (Genv.genv_public (Genv.globalenv (gen_program btr p)))).
          { ii. destruct MGENV as ((MS0 & MS1 & MS2) & EQP).
            replace (Genv.genv_public (Genv.globalenv (gen_program btr p))) with
              (AST.prog_public p) in H10.
            2:{ rewrite Genv.globalenv_public. ss. }
            apply WFPP in H10. apply list_in_map_inv in H10. des. destruct x; ss; clarify.
            apply next_id_lt in H11. lia.
          }
          unfold Genv.public_symbol. des_ifs.
          eapply (pred_dec_false (in_dec ident_eq _ _) true false) in NIN. des_ifs.
        }
        ss. assert (PDM_C: (prog_defmap (gen_program btr p)) ! id_cnt = Some (gen_counter (comp_of gd))).
        { apply prog_defmap_norepet. apply gen_program_list_norepet; auto.
          unfold gen_program. ss. unfold gen_prog_defs. apply in_or_app. right.
          apply PTree.elements_correct in GETCNT. apply (in_map snd) in GETCNT. ss.
        }
        apply Genv.find_def_symbol in PDM_C. des.
        hexploit Genv.init_mem_characterization_gen. eapply H4.
        intros GI. specialize (GI _ _ PDM_C0). ss. des.
        specialize (GI1 eq_refl). specialize (GI2 eq_refl). des.
        esplits; eauto.
        unfold Mem.valid_access. splits; auto. 2: apply Z.divide_0_r.
        eapply Mem.loadbytes_can_access_block_inj; eauto.
      - esplits; eauto. econs.
      - unfold wf_c_stmt. i. subst f_cur. ss. rewrite CNT_CUR in H8. clarify.
        replace (comp_of (gen_function (Genv.globalenv p) (funs_data_of_defs (AST.prog_defs p)) cnt [] (get_id_tr btr id_cur) f)) with
          (Asm.fn_comp f).
        2:{ ss. }
        apply match_symbs_code_bundle_trace. apply MGENV.
      - ii. des_ifs.
      - unfold not_global_blks. unfold empty_env. ss. unfold blocks_of_env2, blocks_of_env. ss.
      - unfold wf_c_nb. ss. erewrite Genv.init_mem_genv_next. reflexivity. auto.
    }
    { instantiate (1:= gen_params (next_id (map snd (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p))))) (AST.prog_defs p)).
      ss. splits.
      - auto.
      - assert (INCR: inject_incr (meminj_public (Genv.globalenv p)) (Mem.flat_inj (Mem.nextblock m0))).
        { clear - H1. ii. unfold meminj_public in H. des_ifs. ss.
          apply Genv.invert_find_symbol in Heq. unfold Genv.find_symbol in Heq.
          apply Genv.genv_symb_range in Heq. apply Genv.init_mem_genv_next in H1.
          unfold Mem.flat_inj. rewrite H1 in Heq. des_ifs.
        }
        unfold match_mem. splits; eauto.
        + eapply genv_init_mem_inj; eauto.
        + clear - INCR. ii. unfold inject_incr in INCR.
          destruct (meminj_public (Genv.globalenv p) b) eqn:CASES; auto.
          exfalso. destruct p0. specialize (INCR _ _ _ CASES). unfold Mem.flat_inj in INCR.
          des_ifs. unfold Plt in *. lia.
      - unfold match_cur_fun. ss. splits; ss. eauto.
      - eapply gen_program_match_find_def; eauto.
      - econs; auto.
      - unfold match_params. splits.
        + apply gen_params_wf.
        + ii. hexploit in_gds_exists_params. 2: eauto.
          { setoid_rewrite Genv.find_def_symbol. esplits; eauto.
            rewrite <- Genv.find_funct_ptr_iff. eauto.
          }
          i. des. rewrite H10 in H11. clarify.
        + ii. ss. hexploit Genv.find_symbol_inversion. apply H8. intros INDEF.
          apply list_in_map_inv in H10. des. destruct x; ss; clarify.
          hexploit gen_params_le. apply H9. apply H11. intros GT.
          clear - WFP INDEF GT. unfold gen_program, prog_defs_names in INDEF. ss.
          apply list_in_map_inv in INDEF. des. destruct x; ss; clarify.
          apply next_id_lt in INDEF0. unfold gen_prog_defs in INDEF0.
          assert (MAX: (max_id 
              (map
                 (fun '(id, gd) =>
                  (id,
                  gen_progdef (Genv.globalenv p) (funs_data_of_defs (AST.prog_defs p)) (get_id_tr btr id) gd
                    (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)) ! id
                    (gen_params
                       (next_id
                          (map snd
                             (PTree.elements
                                (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)))))
                       (AST.prog_defs p)) ! id)) (AST.prog_defs p) ++
               map snd
               (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)))) <=
          max_id (map snd
                      (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)))))%positive).
          { apply max_id0_app. 2: lia. clear - WFP. i. rewrite map_map in H.
            apply list_in_map_inv in H. des. destruct x; ss; clarify.
            rewrite map_map.
            hexploit gen_counter_defs_inv; eauto. intros.
            apply PTree.elements_correct in H.
            apply (in_map (fun x : positive * (ident * globdef fundef type) => fst (snd x))) in H.
            ss. eexists. split. apply H. lia.
          }
          rewrite next_id_is_succ_max_id in INDEF0, GT. lia.
      - ii. setoid_rewrite PTree.gmap in H8. unfold option_map in H8. des_ifs.
        hexploit gen_counter_defs_lt; eauto. intros LT.
        unfold Mem.flat_inj in H10. des_ifs. erewrite <- Genv.init_mem_genv_next in p0; eauto.
        hexploit Genv.find_symbol_inversion. apply H9. intros INDEFS.
        ss. hexploit genv_find_symbol_gen_program_cases. eauto. eapply H9. i. des.
        + unfold Plt in p0. lia.
        + clear - LT H3. apply list_in_map_inv in H3. des. destruct x; ss; clarify.
          hexploit next_id_lt; eauto. i. lia.
    }
    intros (cst' & STAR_C). hexploit state_behaves_exists. intros (beh2 & BEH2).
    esplits; eauto.
  Qed.


  Theorem backtranslation_proof_stepfix_prefix
          (p: Asm.program)
          (WF: asm_program_is_wf p)
    :
    forall tr,
      (Z.of_nat (length tr) < Int64.modulus) ->
      asm_program_does_prefix p tr ->
      stepfix_prefix p tr ->
      exists p_c,
        clight_program_does_prefix p_c tr.
  Proof.
    unfold asm_program_is_wf in WF. des. i.
    hexploit asm_to_clight_stepfix_prefix; eauto.
    { rr. esplits; eauto. }
    { rr. i. rewrite WF1 in H2. clarify. }
    { eexists. econs; eauto. }
    i. des. eauto.
  Qed.

End STEPFIX.

Print Assumptions asm_to_clight_stepfix_runs.
Print Assumptions asm_to_clight_stepfix_prefix.
Print Assumptions backtranslation_proof_stepfix_prefix.
