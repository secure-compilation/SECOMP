Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import Tactics.
Require Import riscV.Asm.
Require Import BtBasics BtInfoAsm MemoryDelta MemoryWeak.
Require Import Ctypes Clight.
Require Import Backtranslation BacktranslationAux BacktranslationProof.
Require Import RSC.


Section GENPROOFS.

  Lemma next_id_lt
        A (l: list (ident * A))
        id a
        (IN: In (id, a) l)
    :
    Pos.lt id (next_id l).
  Proof.
  Admitted.

  Lemma gen_counter_defs_lt
        m agds
        id cnt cd
        (GET: (gen_counter_defs m agds) ! id = Some (cnt, cd))
    :
    (Pos.lt m cnt).
  Proof.
  Admitted.

  Lemma gen_params_lt
        m agds
        id ps
        (GET: (gen_params m agds) ! id = Some ps)
        p t
        (IN: In (p, t) ps)
    :
    Pos.lt m p.
  Proof.
  Admitted.

  Lemma gen_params_wf
        m agds
    :
    wf_params_of (gen_params m agds).
  Proof.
  Admitted.

  (* Lemma gen_params_wf_sig *)
  (*       m agds *)
  (*   : *)
  (*   wf_params_of_sig (gen_params m agds). *)
  (* Proof. *)
  (* Admitted. *)

End GENPROOFS.
(* Genv.initmem_inject: forall [F V : Type] {CF : has_comp F} (p : AST.program F V) [m : mem], Genv.init_mem p = Some m -> Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m *)
(* Genv.alloc_globals_neutral: *)
(*   forall [F V : Type] {CF : has_comp F} (ge : Genv.t F V) [thr : block], *)
(*   (forall (id : ident) (b : block), Genv.find_symbol ge id = Some b -> Plt b thr) -> *)
(*   forall (gl : list (ident * globdef F V)) (m m' : mem), Genv.alloc_globals ge m gl = Some m' -> Mem.inject_neutral thr m -> Ple (Mem.nextblock m') thr -> Mem.inject_neutral thr m' *)

Definition wf_program_public {F V} (p: AST.program F V) :=
  forall id, In id (AST.prog_public p) -> In id (map fst (AST.prog_defs p)).



Section PROOFGENV.

  Lemma gen_prog_defs_props_1
        (a_ge: Senv.t) tr (gds: list (ident * globdef Asm.fundef unit))
        (gen_gds1: list (ident * globdef Clight.fundef type))
        cnts params
        (GEN: gen_gds1 = (map (fun '(id, gd) => (id, gen_progdef a_ge (get_id_tr tr id) gd (cnts ! id) (params ! id))) gds))
    :
    Forall (fun '(id, gd_c) =>
              exists gd_a, (In (id, gd_a) gds) /\ (gd_c = gen_progdef a_ge (get_id_tr tr id) gd_a (cnts ! id) (params ! id)))
           gen_gds1.
  Proof.
    subst gen_gds1. rewrite Forall_map. apply Forall_forall. i. des_ifs. esplits; eauto.
  Qed.

  Lemma gen_prog_defs_inv_1
        (a_ge: Senv.t) tr (gds: list (ident * globdef Asm.fundef unit))
        (gen_gds1: list (ident * globdef Clight.fundef type))
        cnts params
        (GEN: gen_gds1 = (map (fun '(id, gd) => (id, gen_progdef a_ge (get_id_tr tr id) gd (cnts ! id) (params ! id))) gds))
        id gd
        (IN: In (id, gd) gds)
    :
    In (id, gen_progdef a_ge (get_id_tr tr id) gd (cnts ! id) (params ! id)) gen_gds1.
  Proof.
    eapply (in_map (fun '(id0, gd0) => (id0, gen_progdef a_ge (get_id_tr tr id0) gd0 cnts ! id0 params ! id0))) in IN. clarify.
  Qed.

  Lemma gen_counter_defs_props
        (gds: list (ident * globdef Asm.fundef unit))
        cnts x0
        (CNTS: cnts = gen_counter_defs x0 gds)
    :
    Forall (fun '(id, (cnt, gd_c)) =>
              (cnt = (id + x0)%positive) /\ (exists gd_a, (In (id, gd_a) gds) /\ (gd_c = gen_counter (comp_of gd_a))))
           (PTree.elements cnts).
  Proof.
    subst. rewrite Forall_forall. i. destruct x as (id & (cnt & gd_c)). unfold gen_counter_defs in H.
    apply PTree.elements_complete in H. apply PTree_Properties.in_of_list in H.
    apply list_in_map_inv in H. des. des_ifs. splits; auto. esplits; eauto.
  Qed.

  Lemma gen_counter_defs_inv
        (gds: list (ident * globdef Asm.fundef unit))
        (NR: list_norepet (map fst gds))
        cnts x0
        (CNTS: cnts = gen_counter_defs x0 gds)
        id gd
        (IN: In (id, gd) gds)
    :
    cnts ! id = Some ((id + x0)%positive, gen_counter (comp_of gd)).
  Proof.
    subst. unfold gen_counter_defs. apply PTree_Properties.of_list_norepet.
    { rewrite map_map.
      match goal with
      | [|- list_norepet (map ?f gds)] => assert (f = fst)
      end.
      { extensionalities s. des_ifs. }
      rewrite H. auto.
    }
    { eapply (in_map (fun '(id0, gd0) => (id0, ((id0 + x0)%positive, gen_counter (comp_of gd0))))) in IN. auto. }
  Qed.

  Lemma gen_counter_defs_inj
        (gds: list (ident * globdef Asm.fundef unit))
        (NR: list_norepet (map fst gds))
        cnts x0
        (CNTS: cnts = gen_counter_defs x0 gds)
    :
    forall (id0 id1 : positive) (cnt : ident) gd0 gd1,
      cnts ! id0 = Some (cnt, gd0) -> cnts ! id1 = Some (cnt, gd1) -> (id0 = id1 /\ gd0 = gd1).
  Proof.
    i. hexploit gen_counter_defs_props. eauto. i. rewrite Forall_forall in H1.
    pose proof (PTree.elements_correct _ _ H) as IN1. pose proof (PTree.elements_correct _ _ H0) as IN2.
    hexploit (H1 _ IN1). hexploit (H1 _ IN2). clear H1. i. des. clarify. apply Pos.add_reg_r in H2. subst id1. clarify.
    rewrite H. split; auto.
  Qed.

  Definition get_cnt_ids (cnts0: PTree.t (ident * globdef fundef type)): cnt_ids :=
    PTree.map (fun id '(cnt, _) => cnt) cnts0.

  Lemma gen_counter_defs_cnt_ids_inj
        (gds: list (ident * globdef Asm.fundef unit))
        (NR: list_norepet (map fst gds))
        cnts0 x0
        (CNTS0: cnts0 = gen_counter_defs x0 gds)
        (cnts: cnt_ids)
        (CNTS: cnts = get_cnt_ids cnts0)
    :
    forall (id0 id1 : positive) (cnt : ident),
      cnts ! id0 = Some cnt -> cnts ! id1 = Some cnt -> id0 = id1.
  Proof.
    i. subst. unfold get_cnt_ids in *. rewrite PTree.gmap in H0, H. unfold option_map in *. des_ifs.
    hexploit gen_counter_defs_inj. eauto. eauto. apply Heq0. apply Heq. intros (EQ & _). auto.
  Qed.

  Lemma in_prog_defs_gen_program
        p_a btr gds
        (GDS: gds = AST.prog_defs p_a)
        id gd_a
        (IN: In (id, gd_a) gds)
    :
    exists gd_c,
      (In (id, gd_c) (prog_defs (gen_program btr p_a))) /\
        (let m0 := next_id gds in
         let cnts := gen_counter_defs m0 gds in
         let cnt_defs := map snd (PTree.elements cnts) in
         let m1 := next_id cnt_defs in
         let params := gen_params m1 gds in
         gd_c = gen_progdef (Genv.globalenv p_a) (get_id_tr btr id) gd_a (cnts ! id) (params ! id)).
  Proof.
    ss. esplits. 2: eauto. unfold gen_prog_defs. apply in_or_app. left. subst.
    eapply (in_map (fun '(id0, gd) =>
                      (id0, gen_progdef (Genv.globalenv p_a) (get_id_tr btr id0) gd
                                        (gen_counter_defs (next_id (AST.prog_defs p_a)) (AST.prog_defs p_a)) ! id0
                                        (gen_params (next_id (map snd (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p_a)) (AST.prog_defs p_a)))))
                                                    (AST.prog_defs p_a)) ! id0))) in IN. ss.
  Qed.

  Lemma genv_find_symbol_add_global_other
        F V (ge0: Genv.t F V)
        (gd: (ident * globdef F V))
        id
        (NEQ: fst gd <> id)
    :
    Genv.find_symbol (Genv.add_global ge0 gd) id = Genv.find_symbol ge0 id.
  Proof. unfold Genv.add_global, Genv.find_symbol. ss. rewrite PTree.gso; auto. Qed.

  Lemma genv_find_symbol_add_globals_other
        F V (ge0: Genv.t F V)
        (gds: list (ident * globdef F V))
        id
        (NEQ: Forall (fun '(id0, _) => id0 <> id) gds)
    :
    Genv.find_symbol (Genv.add_globals ge0 gds) id = Genv.find_symbol ge0 id.
  Proof.
    move NEQ after ge0. revert_until NEQ. induction NEQ; i; ss. rewrite IHNEQ.
    des_ifs. eapply genv_find_symbol_add_global_other. ss.
  Qed.

  Lemma genv_find_def_add_globals
        F V
        (gds: list (ident * globdef F V))
        ge0 b
        (BLK: (b < Genv.genv_next ge0)%positive)
    :
    Genv.find_def (Genv.add_globals ge0 gds) b = Genv.find_def ge0 b.
  Proof.
    revert_until gds. induction gds; ii; ss.
    destruct a as (idx & gdx). rewrite IHgds.
    2:{ ss. lia. }
    unfold Genv.find_def, Genv.add_global. ss. rewrite PTree.gso; auto.
    { ii. lia. }
  Qed.

  Lemma genv_find_def_add_globals_2
        F V
        (gds: list (ident * globdef F V))
        ge0 id gda
    :
    Genv.find_def (Genv.add_globals (Genv.add_global ge0 (id, gda)) gds) (Genv.genv_next ge0) = Some gda.
  Proof.
    rewrite genv_find_def_add_globals.
    { unfold Genv.find_def, Genv.add_global. ss. rewrite PTree.gss. auto. }
    { ss. lia. }
  Qed.

  Lemma genv_find_symbol_add_globals_some
        F V
        (gds: list (ident * globdef F V))
        id
        (IN: In id (map (fun x => fst x) gds))
        (ge0: Genv.t F V) b
        (FIND: Genv.find_symbol (Genv.add_globals ge0 gds) id = Some b)
    :
    exists gd id0, (Genv.find_def (Genv.add_globals ge0 gds) b = Some gd) /\ (In (id0, gd) gds).
  Proof.
    revert_until gds. induction gds; i; ss.
    destruct a as (ida & gda). ss. des; clarify.
    - destruct (in_dec Pos.eq_dec id (map fst gds)).
      + specialize (IHgds _ i _ _ FIND). des. esplits; eauto.
      + clear IHgds. rewrite genv_find_symbol_add_globals_other in FIND.
        * unfold Genv.find_symbol, Genv.add_global in FIND. ss. rewrite PTree.gss in FIND. clarify.
          exists gda, id. split; auto. apply genv_find_def_add_globals_2.
        * apply Forall_forall. i. destruct x as (idx & gdx). ii. subst. apply n. apply (in_map fst) in H. ss.
    - specialize (IHgds _ IN _ _ FIND). des. esplits; eauto.
  Qed.

  Lemma genv_find_symbol_add_globals_map
        F0 V0 F1 V1
        id b l
        (ge0: Genv.t F0 V0) (ge1: Genv.t F1 V1)
        (NB: (Genv.genv_next ge0) = (Genv.genv_next ge1))
        (FIND: Genv.find_symbol (Genv.add_globals ge0 l) id = Some b)
        gd
        (IN: In (id, gd) l)
        f f'
        (FUN: f' = fun '(id, x) => (id, f (id, x)))
    :
    Genv.find_symbol (Genv.add_globals ge1 (map f' l)) id = Some b.
  Proof.
    subst f'. revert_until l. induction l; i; ss.
    destruct a as (id0 & gd0); ss. des.
    { clarify. destruct (in_dec Pos.eq_dec id (map fst l)).
      { eapply list_in_map_inv in i. des. destruct x as (id' & gd'). ss. subst id'. eapply IHl; eauto.
        unfold Genv.genv_next, Genv.add_global. rewrite NB. auto.
      }
      { clear IHl. rewrite genv_find_symbol_add_globals_other.
        - rewrite genv_find_symbol_add_globals_other in FIND.
          + unfold Genv.find_symbol, Genv.add_global in *. ss. rewrite PTree.gss in *. rewrite <- NB. auto.
          + apply Forall_forall. i. des_ifs. ii. subst i. apply n. apply (in_map fst) in H. ss.
        - rewrite Forall_map. apply Forall_forall. i. des_ifs. ii. subst i. apply n. apply (in_map fst) in H. ss.
      }
    }
    { eapply IHl; eauto. unfold Genv.genv_next, Genv.add_global. rewrite NB. auto. }
  Qed.

  Lemma gen_program_symbs_find
        p_a btr
        p_c ge_a ge_c
        (P_C: p_c = gen_program btr p_a)
        (GE_A: ge_a = Genv.globalenv p_a)
        (GE_C: ge_c = globalenv p_c)
    :
    symbs_find ge_a ge_c.
  Proof.
    subst p_c ge_a ge_c. ii. ss. hexploit Genv.find_symbol_inversion. eapply H. intros IN_A.
    unfold prog_defs_names in IN_A. apply list_in_map_inv in IN_A. des. destruct x as (id0 & gd_a). ss. subst id0.
    unfold Genv.globalenv. ss. unfold gen_prog_defs. rewrite Genv.add_globals_app. rewrite genv_find_symbol_add_globals_other.
    { eapply genv_find_symbol_add_globals_map; eauto. ss. extensionalities. des_ifs. f_equal.
      instantiate (1:= fun '(i, g) => 
                         gen_progdef (Genv.globalenv p_a) (get_id_tr btr i) g (gen_counter_defs (next_id (AST.prog_defs p_a)) (AST.prog_defs p_a)) ! i
                                     (gen_params (next_id (map snd (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p_a)) (AST.prog_defs p_a)))))
                                                 (AST.prog_defs p_a)) ! i). ss.
    }
    { hexploit gen_counter_defs_props. eauto. intros FA.
      eapply Forall_map. eapply Forall_impl. 2: eapply FA. clear FA. ss. i. des_ifs. des; ss; clarify.
      assert (BIG: (id < next_id (AST.prog_defs p_a))%positive).
      { eapply next_id_lt; eauto. }
      lia.
    }
  Qed.

  Lemma gen_program_symbs_public
        p_a btr
        p_c ge_a ge_c
        (WFPP: wf_program_public p_a)
        (P_C: p_c = gen_program btr p_a)
        (GE_A: ge_a = Genv.globalenv p_a)
        (GE_C: ge_c = globalenv p_c)
    :
    symbs_public ge_a ge_c.
  Proof.
    subst p_c ge_a ge_c. ss. unfold symbs_public. i. ss. unfold Genv.public_symbol.
    rewrite ! Genv.globalenv_public. destruct (Genv.find_symbol (Genv.globalenv p_a) id) eqn:FIND_A.
    { eapply gen_program_symbs_find in FIND_A; auto. ss. rewrite FIND_A. ss. }
    des_ifs. destruct (in_dec ident_eq id (AST.prog_public (gen_program btr p_a))); ss. exfalso.
    apply WFPP in i. apply list_in_map_inv in i. des. destruct x; clarify.
    apply Genv.find_symbol_exists in i0. des. ss. clarify.
  Qed.

  Lemma pos_neq_dec (id: positive): forall id0, {id0 <> id} + {~ id0 <> id}.
  Proof. i. destruct (Pos.eq_dec id0 id); clarify; auto. Qed.

  Lemma genv_find_symbol_gen_cases
        (p_a: Asm.program) btr
        id b
        (FIND: Genv.find_symbol (Genv.globalenv (gen_program btr p_a)) id = Some b)
    :
    (Genv.find_symbol (Genv.globalenv p_a) id = Some b) \/
      (Genv.find_symbol (Genv.globalenv p_a) id = None /\
         exists cp, Genv.find_def (Genv.globalenv (gen_program btr p_a)) b = Some (gen_counter cp)).
  Proof.
    destruct (Genv.find_symbol (Genv.globalenv p_a) id) eqn:FIND_A.
    { left. eapply gen_program_symbs_find in FIND_A; eauto. ss. setoid_rewrite FIND in FIND_A. clarify. }
    { right. split; auto.
      unfold Genv.globalenv in *. ss. unfold gen_prog_defs in *. rewrite Genv.add_globals_app in FIND.
      destruct (Forall_Exists_dec _ (pos_neq_dec id) (map fst (map snd (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p_a)) (AST.prog_defs p_a)))))).
      - exfalso.
        rewrite genv_find_symbol_add_globals_other in FIND.
        2:{ rewrite Forall_map in f. eapply Forall_impl. 2: apply f. ss. i. des_ifs. }
        set ({|
              prog_defs := (map
                              (fun '(id, gd) =>
                                 (id,
                                   gen_progdef (Genv.globalenv p_a) (get_id_tr btr id) gd
                                               (gen_counter_defs (next_id (AST.prog_defs p_a)) (AST.prog_defs p_a)) ! id
                                               (gen_params
                                                  (next_id (map snd (PTree.elements (gen_counter_defs (next_id (AST.prog_defs p_a)) (AST.prog_defs p_a)))))
                                                  (AST.prog_defs p_a)) ! id)) (AST.prog_defs p_a));
              prog_public := AST.prog_public p_a;
              prog_main := AST.prog_main p_a;
              prog_pol := AST.prog_pol p_a;
              prog_types := [];
              prog_comp_env := PTree.empty composite;
              prog_comp_env_eq := (fun (_ : bundle_trace) (_ : Asm.program) => Backtranslation.gen_program_obligation_1) btr p_a
              |}) as p_t.
        hexploit Genv.find_symbol_find_def_inversion.
        { instantiate (3:=p_t). unfold Genv.globalenv. subst p_t. ss. eapply FIND. }
        intros (g & FIND_C_DEF).
        assert (PDM: (prog_defmap p_t) ! id = Some g).
        { rewrite Genv.find_def_symbol. esplits; eauto. }
        unfold prog_defmap in PDM. apply PTree_Properties.in_of_list in PDM. subst p_t; ss.
        apply list_in_map_inv in PDM. des. destruct x as (idx & gdx). clarify.
        apply Genv.find_symbol_exists in PDM0. des. unfold Genv.globalenv in PDM0. rewrite FIND_A in PDM0. clarify.
      - rewrite map_map in e. rewrite Exists_exists in e. des. apply Classical_Prop.NNPP in e0. subst x.
        hexploit genv_find_symbol_add_globals_some.
        2:{ eapply FIND. }
        { rewrite map_map. auto. }
        intros. des. hexploit gen_counter_defs_props.
        { instantiate (1:=(AST.prog_defs p_a)). instantiate (1:=(next_id (AST.prog_defs p_a))). auto. }
        intros FA. rewrite Forall_forall in FA. apply list_in_map_inv in H0. des. specialize (FA x H1). des_ifs. des; clarify.
        ss. clarify. rewrite Genv.add_globals_app. eauto.
    }
  Qed.

  Lemma in_gds_exists_cnt
        gds id gd_i
        (FD: (PTree_Properties.of_list gds) ! id = Some gd_i)
        x
    :
    exists cnt, (get_cnt_ids (gen_counter_defs x gds)) ! id = Some cnt /\ (x < cnt)%positive.
  Proof.
    unfold get_cnt_ids, gen_counter_defs.
    assert (IN: In id (map fst (map (fun '(id0, gd) => (id0, ((id0 + x)%positive, gen_counter (comp_of gd)))) gds))).
    { apply PTree_Properties.in_of_list in FD. rewrite map_map.
      apply (in_map (fun x0 : positive * globdef Asm.fundef unit => fst (let '(id0, gd) := x0 in (id0, ((id0 + x)%positive, gen_counter (comp_of gd)))))) in FD. ss.
    }
    apply PTree_Properties.of_list_dom in IN. des. destruct v.
    rewrite PTree.gmap. setoid_rewrite IN. ss. esplits; eauto.
    apply PTree_Properties.in_of_list in IN. apply list_in_map_inv in IN. des. des_ifs. lia.
  Qed.

  Lemma Forall_numbering0
        A (l: list A)
    :
    forall x1 x2, (x1 <= x2)%positive -> Forall (fun '(id, _) => (x1 <= id)%positive) (numbering x2 l).
  Proof. induction l; i; ss. econs. auto. eapply IHl. lia. Qed.

  Lemma Forall_numbering
        A (l: list A)
    :
    forall x, Forall (fun '(id, _) => (x <= id)%positive) (numbering x l).
  Proof. i. eapply Forall_numbering0. lia. Qed.

  Lemma map_snd_numbering
        A (l: list A)
    :
    forall x, l = map snd (numbering x l).
  Proof. induction l; i; ss. f_equal. eauto. Qed.

  Lemma in_gds_exists_params
        gds id gd_i
        (FD: (PTree_Properties.of_list gds) ! id = Some gd_i)
        (NR: list_norepet (map fst gds))
        x
    :
    exists ps, (gen_params x gds) ! id = Some ps /\
            Forall (fun '(id, _) => (x <= id)%positive) ps /\
            (match gd_i with
             | Gfun fd => map typ_to_type (sig_args (funsig fd)) = map snd ps
             | Gvar _ => ps = []
             end).
  Proof.
    unfold gen_params.
    assert (IN: In id (map fst (map (fun '(id0, gd) =>
           match gen_params_one x gd with
           | Some ps0 => (id0, ps0)
           | None => (id0, [])
           end) gds))).
    { apply PTree_Properties.in_of_list in FD. rewrite map_map.
      apply (in_map (fun x0 : PTree.elt * globdef Asm.fundef unit =>
                       fst (let '(id0, gd) := x0 in
            match gen_params_one x gd with
            | Some ps0 => (id0, ps0)
            | None => (id0, [])
            end))) in FD. des_ifs.
    }
    apply PTree_Properties.of_list_dom in IN. des. rename v into ps.
    setoid_rewrite IN. exists ps. split; auto.
    apply PTree_Properties.in_of_list in IN. apply list_in_map_inv in IN. des. des_ifs; ss.
    - unfold gen_params_one in Heq. des_ifs. split.
      apply Forall_numbering; eauto.
      hexploit PTree_Properties.of_list_norepet. eauto. apply IN0. intros GET.
      rewrite FD in GET; clarify. eapply map_snd_numbering.
    - unfold gen_params_one in Heq. des_ifs.
      hexploit PTree_Properties.of_list_norepet. eauto. apply IN0. intros GET.
      rewrite FD in GET; clarify.
    - unfold gen_params_one in Heq. des_ifs.
      hexploit PTree_Properties.of_list_norepet. eauto. apply IN0. intros GET.
      rewrite FD in GET; clarify.
  Qed.

  Lemma in_asm_in_gen
        p_a btr
        p_c ge_a ge_c
        (P_C: p_c = gen_program btr p_a)
        (GE_A: ge_a = Genv.globalenv p_a)
        (GE_C: ge_c = globalenv p_c)
        id gd_a
        (FD: (prog_defmap p_a) ! id = Some gd_a)
        gds
        (GDS: gds = AST.prog_defs p_a)
        x0 cnt
        (X0: x0 = next_id gds)
        (IN_CNT : (get_cnt_ids (gen_counter_defs x0 gds)) ! id = Some cnt)
        x1 ps
        (X1: x1 = next_id (map snd (PTree.elements (gen_counter_defs x0 gds))))
        (IN_PS : (gen_params x1 gds) ! id = Some ps)
        (NR_GEN: list_norepet (prog_defs_names p_c))
    :
    (prog_defmap p_c) ! id =
      Some (gen_globdef ge_a cnt ps (get_id_tr btr id) gd_a).
  Proof.
    subst. apply in_prog_defmap in FD. eapply in_prog_defs_gen_program in FD; eauto.
    des. assert (FD': In (id, gd_c) (AST.prog_defs (gen_program btr p_a))).
    { eapply FD. }
    hexploit prog_defmap_norepet. 2: eapply FD'. auto.
    intros EQ. rewrite EQ. clear EQ FD'. ss. subst gd_c.
    unfold gen_progdef.
    rewrite IN_PS. unfold get_cnt_ids in IN_CNT. rewrite PTree.gmap in IN_CNT.
    destruct ((gen_counter_defs (next_id (AST.prog_defs p_a)) (AST.prog_defs p_a)) ! id) eqn:CNT; ss.
    destruct p. clarify.
  Qed.

  Lemma gen_counter_defs_list_norepet
        x gds
        (NR: list_norepet (map fst gds))
    :
    list_norepet (map (fun x => fst (snd x)) (PTree.elements (gen_counter_defs x gds))).
  Proof.
    eapply list_map_norepet.
    { hexploit PTree.elements_keys_norepet. intros A. apply list_map_norepet_rev in A. eauto. }
    i. destruct x0 as (idx & (cntx & gdx)). destruct y as (idy & (cnty & gdy)).
    apply PTree.elements_complete in H, H0. ss.
    destruct (Pos.eqb_spec idx idy).
    { subst. rewrite H0 in H. clarify. }
    { destruct (Pos.eqb_spec cntx cnty); auto.
      subst. hexploit gen_counter_defs_inj. eauto. 2: apply H. 2: apply H0. eauto.
      i. des; clarify.
    }
  Qed.

  Lemma gen_counter_defs_list_disjoint
        gds x
        (BOUND: ((next_id gds) <= x)%positive)
    :
    list_disjoint (map fst gds)
                  (map (fun x => fst (snd x)) (PTree.elements (gen_counter_defs x gds))).
  Proof.
    ii. subst. apply list_in_map_inv in H, H0. des. destruct x1, x0. ss. clarify.
    destruct p0 as (cnt & g_cnt). ss. rename p into id.
    apply PTree.elements_complete in H1. apply gen_counter_defs_lt in H1.
    hexploit next_id_lt. apply H2. i. lia.
  Qed.

  Lemma gen_program_list_norepet
        p_a btr
        (NR: list_norepet (prog_defs_names p_a))
    :
    list_norepet (prog_defs_names (gen_program btr p_a)).
  Proof.
    unfold prog_defs_names, gen_program in *. ss. unfold gen_prog_defs.
    rewrite map_app. rewrite ! map_map.
    match goal with
    | [|- list_norepet (?l ++ _)] => assert (EQ: l = map fst (AST.prog_defs p_a))
    end.
    { f_equal. extensionalities x. destruct x; ss. }
    rewrite EQ. clear EQ. rewrite list_norepet_app. splits; auto.
    apply gen_counter_defs_list_norepet; auto. 
    apply gen_counter_defs_list_disjoint; auto.  lia.
  Qed.

  Lemma gen_program_match_find_def
        p_a btr
        p_c ge_a ge_c
        (P_C: p_c = gen_program btr p_a)
        (GE_A: ge_a = Genv.globalenv p_a)
        (GE_C: ge_c = globalenv p_c)
        gds
        (GDS: gds = AST.prog_defs p_a)
        x0 cnts
        (X0: x0 = next_id gds)
        (CNTS: cnts = get_cnt_ids (gen_counter_defs x0 gds))
        x1 pars
        (X1: x1 = next_id (map snd (PTree.elements (gen_counter_defs x0 gds))))
        (PARS: pars = gen_params x1 gds)
        (NR: list_norepet (prog_defs_names p_a))
    :
    match_find_def ge_a ge_c cnts pars btr.
  Proof.
    subst. ii. assert (FD: (prog_defmap p_a) ! id = Some gd_i).
    { rewrite Genv.find_def_symbol. apply Senv.invert_find_symbol in H0. ss. esplits; eauto. }
    unfold prog_defmap in FD. set (AST.prog_defs p_a) as gds in *.
    hexploit in_gds_exists_cnt. eapply FD. intros (cnt & IN_CNT).
    hexploit in_gds_exists_params. eapply FD. apply NR. intros (ps & IN_PS).
    des. rewrite IN_CNT, IN_PS.
    hexploit in_asm_in_gen. 4: apply FD. 6: apply IN_CNT. 7: apply IN_PS. all: eauto.
    { apply gen_program_list_norepet. auto. }
    instantiate (1:=btr). intros FD_C. rewrite Genv.find_def_symbol in FD_C. des.
    apply Senv.invert_find_symbol in H0. ss. eapply gen_program_symbs_find in H0; eauto.
    ss. setoid_rewrite FD_C in H0. clarify.
  Qed.

  Lemma gen_program_symbs_volatile
        p_a btr
        p_c ge_a ge_c
        (P_C: p_c = gen_program btr p_a)
        (GE_A: ge_a = Genv.globalenv p_a)
        (GE_C: ge_c = globalenv p_c)
        (NR: list_norepet (prog_defs_names p_a))
    :
    symbs_volatile ge_a ge_c.
  Proof.
    unfold symbs_volatile. i. unfold Senv.block_is_volatile. ss.
    unfold Genv.block_is_volatile. destruct (Genv.find_var_info ge_a b) eqn:VAR_A.
    { rewrite Genv.find_var_info_iff in VAR_A. hexploit wf_ge_block_to_id. 2: eapply VAR_A.
      { subst ge_a. apply wf_program_wf_ge. ss. }
      intros (id & INV_A).
      hexploit gen_program_match_find_def; eauto. intros MFD.
      unfold match_find_def in MFD. specialize (MFD _ _ _ VAR_A INV_A). des_ifs.
      2:{ ss. rewrite <- Genv.find_var_info_iff in MFD. rewrite MFD in Heq. ss. }
      ss. rewrite Genv.find_var_info_iff in Heq. rewrite MFD in Heq. clarify.
    }
    { des_ifs. rewrite Genv.find_var_info_iff in Heq.
      hexploit @genv_def_to_ident. 3: eapply Heq. eapply gen_program_list_norepet; eauto. ss.
      intros (id & INV). apply Genv.invert_find_symbol in INV.
      hexploit genv_find_symbol_gen_cases. apply INV. intros CASES. des.
      { exfalso. unfold Genv.find_var_info in VAR_A. des_ifs.
        2:{ apply Genv.find_symbol_find_def_inversion in CASES. des. clarify. }
        apply Genv.find_invert_symbol in CASES. hexploit gen_program_match_find_def; eauto.
        intros MFD. unfold match_find_def in MFD. specialize (MFD _ _ _ Heq0 CASES).
        des_ifs. rewrite Heq in MFD. ss.
      }
      setoid_rewrite Heq in CASES0. clarify.
    }
  Qed.

  Lemma gen_program_eq_policy
        p_a btr
        p_c ge_a ge_c
        (P_C: p_c = gen_program btr p_a)
        (GE_A: ge_a = Genv.globalenv p_a)
        (GE_C: ge_c = globalenv p_c)
    :
    eq_policy ge_a ge_c.
  Proof.
    subst. unfold eq_policy. ss. unfold Genv.globalenv. ss.
    rewrite ! Genv.genv_pol_add_globals. ss.
  Qed.

  Lemma gen_program_match_genv
        p_a btr
        p_c ge_a ge_c
        (P_C: p_c = gen_program btr p_a)
        (GE_A: ge_a = Genv.globalenv p_a)
        (GE_C: ge_c = globalenv p_c)
        (WFPP: wf_program_public p_a)
        (NR: list_norepet (prog_defs_names p_a))
    :
    match_genv ge_a ge_c.
  Proof.
    unfold match_genv, match_symbs. splits.
    eapply gen_program_symbs_public; eauto.
    eapply gen_program_symbs_find; eauto.
    eapply gen_program_symbs_volatile; eauto.
    eapply gen_program_eq_policy; eauto.
  Qed.

End PROOFGENV.


Section PROOFINIT.

  Lemma gen_counter_defs_alloc
        x0 gds cnts
        (CNTS: cnts = gen_counter_defs x0 gds)
        (ge: genv)
    :
    Forall (fun (idg: ident * (globdef fundef type)) =>
              let (_, y) := idg in
              match y with
              | Gfun _ => False
              | Gvar v =>
                  Genv.init_data_list_aligned 0 (gvar_init v) /\
                    (forall (i : ident) (o : ptrofs), In (Init_addrof i o) (gvar_init v) -> exists b : block, Genv.find_symbol ge i = Some b)
              end) (map snd (PTree.elements cnts)).
  Proof.
    apply Forall_forall. intros (idx & gdx) IN. hexploit (gen_counter_defs_props _ _ _ CNTS).
    intros FA. rewrite Forall_forall in FA. apply list_in_map_inv in IN. des.
    destruct x as (id & (cnt & gd)). ss. clarify. specialize (FA _ IN0). ss. des.
    subst. ss. splits; auto. apply Z.divide_0_r. i. des; ss.
  Qed.

  Lemma genv_store_init_data_eq
        (ge_a: Asm.genv) (ge_c: Clight.genv)
        (SF: symbs_find ge_a ge_c)
        a m b z cp m'
        (SOME: Genv.store_init_data ge_a m b z a cp = Some m')
    :
    Genv.store_init_data ge_c m b z a cp = Some m'.
  Proof.
    destruct a; ss. destruct (Genv.find_symbol ge_a i) eqn:FIND; ss.
    apply SF in FIND. setoid_rewrite FIND. ss.
  Qed.

  Lemma genv_store_init_data_list_eq
        (ge_a: Asm.genv) (ge_c: Clight.genv)
        (SF: symbs_find ge_a ge_c)
        l m b z cp m'
        (SOME: Genv.store_init_data_list ge_a m b z l cp = Some m')
    :
    Genv.store_init_data_list ge_c m b z l cp = Some m'.
  Proof.
    revert_until l. induction l; i; ss.
    destruct (Genv.store_init_data ge_a m b z a cp) eqn:MEM; ss.
    eapply genv_store_init_data_eq in MEM; eauto. rewrite MEM. eauto.
  Qed.

  Lemma gen_progdef_exists_alloc_global
        (ge_a: Asm.genv) (ge_c: Clight.genv)
        (SF: symbs_find ge_a ge_c)
        m0 id gd m1
        (AG: Genv.alloc_global ge_a m0 (id, gd) = Some m1)
        btr cnt ps
    :
    Genv.alloc_global ge_c m0 (id, gen_progdef ge_a btr gd (Some cnt) (Some ps)) = Some m1.
  Proof.
    ss. destruct cnt as (cnt & cnt_def). destruct gd; ss.
    { replace (comp_of (gen_fundef ge_a cnt ps btr f)) with (comp_of f).
      2:{ unfold gen_fundef. des_ifs. }
      ss.
    }
    { replace (Genv.perm_globvar (gen_globvar v)) with (Genv.perm_globvar v).
      2:{ ss. }
      destruct (Mem.alloc m0 (gvar_comp v) 0 (init_data_list_size (gvar_init v))) as (ma & b).
      destruct (store_zeros ma b 0 (init_data_list_size (gvar_init v)) (gvar_comp v)); ss.
      destruct (Genv.store_init_data_list ge_a m b 0 (gvar_init v) (gvar_comp v)) eqn:MEM; ss.
      hexploit genv_store_init_data_list_eq; eauto. intros EQ. rewrite EQ. ss.
    }
  Qed.

  Lemma gen_program_exists_init_mem_1_aux
        (ge_a: Asm.genv) (ge_c: Clight.genv)
        (SF: symbs_find ge_a ge_c)
        (gds: list (ident * globdef Asm.fundef unit))
        m0 m_a
        (MEMA : Genv.alloc_globals ge_a m0 gds = Some m_a)
        btr cnts pars
        (CNTS: forall id, In id (map fst gds) -> exists cnt, cnts ! id = Some cnt)
        (PARS: forall id, In id (map fst gds) -> exists ps, pars ! id = Some ps)
    :
    Genv.alloc_globals ge_c m0
                       (map (fun '(id, gd) => (id, gen_progdef ge_a (get_id_tr btr id) gd cnts ! id pars ! id)) gds) = Some m_a.
  Proof.
    revert_until gds. induction gds; i; ss. eauto.
    destruct (Genv.alloc_global ge_a m0 a) eqn:ALLOC; ss.
    destruct a as (id & gd).
    hexploit CNTS. left; ss. intros (cnt & GET_CNT).
    hexploit PARS. left; ss. intros (ps & GET_PS).
    rewrite GET_CNT, GET_PS.
    hexploit gen_progdef_exists_alloc_global. 2: eapply ALLOC. eauto.
    intros ALLOC2. rewrite ALLOC2.
    eapply IHgds; eauto.
  Qed.

  Lemma gen_program_exists_init_mem_1
        p btr
        p_c ge_a ge_c
        (P_C: p_c = gen_program btr p)
        (GE_A: ge_a = Genv.globalenv p)
        (GE_C: ge_c = globalenv p_c)
        (NR: list_norepet (map fst (AST.prog_defs p)))
        m0 m_a
        (MEMA : Genv.alloc_globals ge_a m0 (AST.prog_defs p) = Some m_a)
    :
    Genv.alloc_globals ge_c m0
                       (map
                          (fun '(id, gd) =>
                             (id,
                               gen_progdef ge_a (get_id_tr btr id) gd
                                           (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)) ! id
                                           (gen_params
                                              (next_id
                                                 (map snd
                                                      (PTree.elements
                                                         (gen_counter_defs (next_id (AST.prog_defs p)) (AST.prog_defs p)))))
                                              (AST.prog_defs p)) ! id)) (AST.prog_defs p)) = Some m_a.
  Proof.
    eapply gen_program_exists_init_mem_1_aux; auto.
    { subst. eapply gen_program_symbs_find; auto. }
    eauto.
    { i. apply PTree_Properties.of_list_dom in H. des.
      eapply in_gds_exists_cnt in H. des. unfold get_cnt_ids in H. rewrite PTree.gmap in H.
      unfold option_map in H. des_ifs. eauto.
    }
    { i. apply PTree_Properties.of_list_dom in H. des.
      eapply in_gds_exists_params in H; auto. des. eauto.
    }
  Qed.

  Lemma gen_program_exists_init_mem
        btr (p: Asm.program)
        m_a
        (MEMA: Genv.init_mem p = Some m_a)
        (NR: list_norepet (map fst (AST.prog_defs p)))
    :
    exists m_c, Genv.init_mem (gen_program btr p) = Some m_c.
  Proof.
    unfold Genv.init_mem in *. ss. unfold gen_prog_defs.
    hexploit gen_program_exists_init_mem_1; auto. eauto. apply MEMA.
    intros ALLOC1. erewrite <- Genv.alloc_globals_app.
    2:{ apply ALLOC1. }

    TODO


Genv.alloc_global_exists:
  forall [F V : Type] {CF : has_comp F} (ge : Genv.t F V) (m : mem) (idg : ident * globdef F V),
  (let (_, y) := idg in
   match y with
   | Gfun _ => True
   | Gvar v =>
       Genv.init_data_list_aligned 0 (gvar_init v) /\
       (forall (i : ident) (o : ptrofs), In (Init_addrof i o) (gvar_init v) -> exists b : block, Genv.find_symbol ge i = Some b)
   end) -> exists m' : mem, Genv.alloc_global ge m idg = Some m'

  Definition wf_c_state (ge: Clight.genv) (tr ttr: bundle_trace) (cnts: cnt_ids) id (cst: Clight.state) :=
    match cst with
    | State f stmt k_c e le m_c =>
        wf_counters ge m_c tr cnts /\
          ( (wf_c_nb ge m_c))
    | _ => False
    end.
(forall (id : ident) (b : block) (f : function),
 Genv.find_symbol ge id = Some b ->
 Genv.find_funct_ptr ge b = Some (Internal f) ->
 exists cnt : ident,
   cnts ! id = Some cnt /\ wf_counter ge m (comp_of f) (Datatypes.length (get_id_tr tr id)) cnt)
     : genv -> mem -> bundle_trace -> cnt_ids -> Prop
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

Genv.alloc_globals = 
fun (F V : Type) (CF : has_comp F) (ge : Genv.t F V) =>
fix alloc_globals (m : mem) (gl : list (ident * globdef F V)) {struct gl} : option mem :=
  match gl with
  | [] => Some m
  | g :: gl' => match Genv.alloc_global ge m g with
                | Some m' => alloc_globals m' gl'
                | None => None
                end
  end
      : forall F V : Type, has_comp F -> Genv.t F V -> mem -> list (ident * globdef F V) -> option mem

Genv.alloc_globals_app:
  forall [F V : Type] {CF : has_comp F} (ge : Genv.t F V) (gl1 gl2 : list (ident * globdef F V)) (m : mem) [m1 : mem],
  Genv.alloc_globals ge m gl1 = Some m1 -> Genv.alloc_globals ge m1 gl2 = Genv.alloc_globals ge m (gl1 ++ gl2)

Genv.init_mem = 
fun (F V : Type) (CF : has_comp F) (p : AST.program F V) => Genv.alloc_globals (Genv.globalenv p) Mem.empty (AST.prog_defs p)
     : forall F V : Type, has_comp F -> AST.program F V -> option mem

Genv.globals_initialized = 
fun (F V : Type) (ge g : Genv.t F V) (m : mem) =>
forall (b : block) (gd : globdef F V),
Genv.find_def g b = Some gd ->
match gd with
| Gfun _ =>
    Mem.perm m b 0 Cur Nonempty /\
    (forall (ofs : Z) (k : perm_kind) (p : permission), Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty)
| Gvar v =>
    Mem.range_perm m b 0 (init_data_list_size (gvar_init v)) Cur (Genv.perm_globvar v) /\
    (forall (ofs : Z) (k : perm_kind) (p : permission),
     Mem.perm m b ofs k p -> 0 <= ofs < init_data_list_size (gvar_init v) /\ perm_order (Genv.perm_globvar v) p) /\
    (gvar_volatile v = false -> Genv.load_store_init_data ge m b 0 (gvar_init v) (Some (gvar_comp v))) /\
    (gvar_volatile v = false ->
     Mem.loadbytes m b 0 (init_data_list_size (gvar_init v)) (Some (gvar_comp v)) =
     Some (Genv.bytes_of_init_data_list ge (gvar_init v)))
end
     : forall F V : Type, Genv.t F V -> Genv.t F V -> mem -> Prop
wf_counter = 
fun (ge : Senv.t) (m : mem) (cp : compartment) (n : nat) (cnt : ident) =>
Senv.public_symbol ge cnt = false /\
(exists b : block,
   Senv.find_symbol ge cnt = Some b /\
   Mem.valid_access m Mint64 b 0 Writable (Some cp) /\
   Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (nat64 n)))
     : Senv.t -> mem -> compartment -> nat -> ident -> Prop







Variant ir_initial_state (p : Asm.program) : ir_state -> Prop :=
    ir_initial_state_intro : forall (cur : block) (m0 : mem),
                             let ge := Genv.globalenv p in
                             Genv.find_symbol ge (AST.prog_main p) = Some cur ->
                             (exists f : Asm.function, Genv.find_funct_ptr ge cur = Some (AST.Internal f)) ->
                             Genv.init_mem p = Some m0 -> ir_initial_state p (Some (cur, m0, [])).
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p (Callstate f nil Kstop m0).
  Definition wf_c_state (ge: Clight.genv) (tr ttr: bundle_trace) (cnts: cnt_ids) id (cst: Clight.state) :=
    match cst with
    | State f stmt k_c e le m_c =>
        wf_counters ge m_c tr cnts /\
          (exists m_c', Mem.free_list m_c (blocks_of_env ge e) (comp_of f) = Some m_c' /\ wf_c_cont ge m_c' k_c) /\
          wf_c_stmt ge (comp_of f) cnts id ttr stmt /\
          (wf_env ge e /\ (not_global_blks (ge) (blocks_of_env2 ge e)) /\ (wf_c_nb ge m_c))
    | _ => False
    end.
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



  Definition asm_program_does_prefix (p: Asm.program) (t: trace) :=
    semantics_has_initial_trace_prefix (Asm.semantics p) t.
  Definition clight_program_does_prefix (p: Clight.program) (t: trace) :=
    semantics_has_initial_trace_prefix (Clight.semantics1 p) t.

  Theorem asm_to_clight
          (p: Asm.program) (ast: Asm.state)
          (WFP: wf_program p)
          (WFPP: wf_program_public p)
          (WFMAIN: wf_main p)
          (WFMAINSIG: wf_main_sig p)
          (WFINIT: exists (s : Asm.state), Asm.initial_state p s)
    (* (WF: exists (s: Smallstep.state (semantics p)), Smallstep.initial_state (semantics p) s) *)
    :
    forall tr, asm_program_does_prefix p tr ->
          exists btr,
            clight_program_does_prefix (gen_program btr p) tr /\
              unbundle_trace btr = tr.
  Proof.
    i. eapply semantics_has_initial_trace_prefix_implies_cut in H.
    2:{ apply sd_traces. apply semantics_determinate. }
    inv H; cycle 1.
    { exfalso. ss. des. eapply H0. eapply WFINIT. }
    clear WFINIT. ss. des. hexploit ir_has_initial_state; eauto. intros (ist & IR_INIT).
    hexploit match_state_initial_state; eauto. intros (m0 & j & INIT_MEM_A & MS_I).
    hexploit asm_to_ir.
    { eapply wf_program_wf_ge; eauto. }
    { eapply wf_asm_initial_state; eauto. }
    { assert (star (step_fix (comp_of_main p)) (Genv.globalenv p) s tr s').
      { admit. (* fix asm step *) }
      eapply H.
    }
    { eapply MS_I. }
    intros (btr & ist' & UTR & ISTAR). esplits. 2: eauto.
    eapply semantics_has_initial_trace_cut_implies_prefix.
    assert (INIT_C: exists cst, Clight.initial_state (gen_program btr p) cst).
    { admit. }
    des. hexploit ir_to_clight.
    { eapply wf_program_wf_ge; eauto. }
    4: eapply ISTAR.
    { admit. }
    { admit. }
    { admit. }
    intros CSTAR. des. econs 1; ss.
    { admit. }
    hexploit state_behaves_exists. intros (beh2 & BEH2).
    esplits.
    { admit. }
    { eapply BEH2. }

  Admitted.
  Qed.

    TODO

    Lemma gen_program_exists_initial_state
          (p: Asm.program) btr
  (ist : ir_state)
  (IR_INIT : ir_initial_state p ist)
      :
      

(* state_behaves_exists: forall (L : Smallstep.semantics) (s : Smallstep.state L), exists beh : program_behavior, state_behaves L s beh *)
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p (Callstate f nil Kstop m0).
  Definition wf_c_state (ge: Clight.genv) (tr ttr: bundle_trace) (cnts: cnt_ids) id (cst: Clight.state) :=
    match cst with
    | State f stmt k_c e le m_c =>
        wf_counters ge m_c tr cnts /\
          (exists m_c', Mem.free_list m_c (blocks_of_env ge e) (comp_of f) = Some m_c' /\ wf_c_cont ge m_c' k_c) /\
          wf_c_stmt ge (comp_of f) cnts id ttr stmt /\
          (wf_env ge e /\ (not_global_blks (ge) (blocks_of_env2 ge e)) /\ (wf_c_nb ge m_c))
    | _ => False
    end.
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

Variant ir_initial_state (p : Asm.program) : ir_state -> Prop :=
    ir_initial_state_intro : forall (cur : block) (m0 : mem),
                             let ge := Genv.globalenv p in
                             Genv.find_symbol ge (AST.prog_main p) = Some cur ->
                             (exists f : Asm.function, Genv.find_funct_ptr ge cur = Some (AST.Internal f)) ->
                             Genv.init_mem p = Some m0 -> ir_initial_state p (Some (cur, m0, [])).
   Theorem ir_to_clight
          (ge_i: Asm.genv) (ge_c: Clight.genv)
          (WFGE: wf_ge ge_i)
          ist cst
          ttr cnts pars k id
          (BOUND: Z.of_nat (Datatypes.length ttr) < Int64.modulus)
          (WFC: wf_c_state ge_c [] ttr cnts id cst)
          (MS: match_state ge_i ge_c k ttr cnts pars id ist cst)
          ist'
          (STAR: istar (ir_step) ge_i ist ttr ist')
    :
    exists cst', star step1 ge_c cst (unbundle_trace ttr) cst'.



| step_internal_function : forall (f : function) (vargs : list val) (k : cont) (m : mem) (e : env) (le : temp_env) (m1 : mem),
                             function_entry f vargs m e le m1 ->
                             step ge function_entry (Callstate (Internal f) vargs k m) E0 (State f (fn_body f) k e le m1)
Inductive function_entry1 (ge : genv) (f : function) (vargs : list val) (m : mem) (e : env) (le : temp_env) (m' : mem) : Prop :=
    function_entry1_intro : forall m1 : mem,
                            list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
                            alloc_variables ge (comp_of f) empty_env m (fn_params f ++ fn_vars f) e m1 ->
                            bind_parameters ge (comp_of f) e m1 (fn_params f) vargs m' ->
                            le = create_undef_temps (fn_temps f) -> function_entry1 ge f vargs m e le m'.
Complements.clight_program_has_initial_trace = 
fun (p : program) (t : trace) => forall beh : program_behavior, program_behaves (semantics1 p) beh -> behavior_prefix t beh
     : program -> trace -> Prop

End PROOFINIT.
