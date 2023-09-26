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
    (* In (id, ((id + x0)%positive, gen_counter (comp_of gd))) (PTree.elements cnts). *)
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

(*   Lemma genv_find_symbol_add_globals_some *)
(*         F V *)
(*         (gds: list (ident * globdef F V)) *)
(*         id *)
(*         (IN: In id (map (fun x => fst x) gds)) *)
(*         (ge0: Genv.t F V) b *)
(*         (FIND: Genv.find_symbol (Genv.add_globals ge0 gds) id = Some b) *)
(*     : *)
(*     exists gd id0, (Genv.find_def (Genv.add_globals ge0 gds) b = Some gd) /\ (In (id0, gd) gds). *)
        
        
        
(* list_in_map_inv: forall [A B : Type] (f : A -> B) (l : list A) (y : B), In y (map f l) -> exists x : A, y = f x /\ In x l *)
        
        
(* Genv.find_def_symbol: *)
(*   forall [F V : Type] (p : AST.program F V) (id : positive) (g : globdef F V), *)
(*   (prog_defmap p) ! id = Some g <-> *)
(*   (exists b : block, Genv.find_symbol (Genv.globalenv p) id = Some b /\ Genv.find_def (Genv.globalenv p) b = Some g) *)


(*       eapply Genv.find_symbol_find_def_inversion in FIND. des. *)
(*       apply Genv.find_def_inversion in FIND. des. *)
      
(* Genv.find_symbol_find_def_inversion: *)
(*   forall [F V : Type] (p : AST.program F V) (x : ident) [b : block], *)
(*   Genv.find_symbol (Genv.globalenv p) x = Some b -> exists g : globdef F V, Genv.find_def (Genv.globalenv p) b = Some g *)
(* Genv.find_def_inversion: *)
(*   forall [F V : Type] (p : AST.program F V) (b : block) [g : globdef F V], *)
(*   Genv.find_def (Genv.globalenv p) b = Some g -> exists id : ident, In (id, g) (AST.prog_defs p) *)

(* Genv.find_symbol_exists: *)
(*   forall [F V : Type] (p : AST.program F V) (id : ident) (g : globdef F V), *)
(*   In (id, g) (AST.prog_defs p) -> exists b : block, Genv.find_symbol (Genv.globalenv p) id = Some b *)
      
(*     unfold Genv.globalenv, gen_program, gen_prog_defs in FIND; ss. *)
(*     destruct ( *)

        
(*         apply Genv.find_symbol_inversion in FIND_C. unfold prog_defs_names in FIND_C. apply list_in_map_inv in FIND_C. *)
(*         des. destruct x as (idx & gd). ss. subst idx. unfold gen_prog_defs in FIND_C0. apply in_app_or in FIND_C0. des. *)
(*         - left.  *)

  (*           Lemma genv_find_symbol_only_in_gen *)
  (*                 (p_a: Asm.program) btr *)
  (*                 id *)
  (*                 (FIND_A: Genv.find_symbol (Genv.globalenv p_a) id = None) *)
  (*                 b *)
  (*                 (FIND_C: Genv.find_symbol (Genv.globalenv (gen_program btr p_a)) id = Some b) *)
  (*             : *)
  (*             exists cp, Genv.find_def (Genv.globalenv (gen_program btr p_a)) b = Some (gen_counter cp). *)
  (*           Proof. *)

  TODO
  
match_find_def = 
fun (ge_i : Asm.genv) (ge_c : genv) (cnts : cnt_ids) (pars : params_of) (tr : bundle_trace) =>
forall (b : block) (gd_i : globdef Asm.fundef unit) (id : ident),
Genv.find_def ge_i b = Some gd_i ->
Senv.invert_symbol ge_i b = Some id ->
match cnts ! id with
| Some cnt =>
    match pars ! id with
    | Some params => Genv.find_def ge_c b = Some (gen_globdef ge_i cnt params (get_id_tr tr id) gd_i)
    | None => False
    end
| None => False
end
     : Asm.genv -> genv -> cnt_ids -> params_of -> bundle_trace -> Prop

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

      TODO

      hexploit (genv_def_to_some_ident _ NR). eauto. eauto.
      i. des. 
      
wf_ge_block_to_id:
  forall (F V : Type) (ge : Genv.t F V),
  wf_ge ge ->
  forall (b : block) (gd : globdef F V), Genv.find_def ge b = Some gd -> exists id : ident, Genv.invert_symbol ge b = Some id

    destruct (Genv.find_symbol (Genv.globalenv (gen_program btr p_a))

    hexploit genv_find_symbol_gen_cases. 

Genv.find_symbol_find_def_inversion:
  forall [F V : Type] (p : AST.program F V) (x : ident) [b : block],
  Genv.find_symbol (Genv.globalenv p) x = Some b -> exists g : globdef F V, Genv.find_def (Genv.globalenv p) b = Some g
Genv.find_var_info_iff:
  forall [F V : Type] (ge : Genv.t F V) (b : block) (v : globvar V),
  Genv.find_var_info ge b = Some v <-> Genv.find_def ge b = Some (Gvar v)
genv_def_to_some_ident:
  forall {F V : Type} (p : AST.program F V),
  list_norepet (prog_defs_names p) ->
  forall ge : Genv.t F V,
  ge = Genv.globalenv p ->
  forall (b : block) (gd : globdef F V),
  Genv.find_def ge b = Some gd ->
  exists (id : ident) (b' : block), Genv.find_symbol ge id = Some b' /\ Genv.find_def ge b' = Some gd
    

Genv.block_is_volatile = 
fun (F V : Type) (ge : Genv.t F V) (b : block) =>
match Genv.find_var_info ge b with
| Some gv => gvar_volatile gv
| None => false
end
     : forall F V : Type, Genv.t F V -> block -> bool
  Lemma genv_find_symbol_gen_cases
        (p_a: Asm.program) btr
        id b
        (FIND: Genv.find_symbol (Genv.globalenv (gen_program btr p_a)) id = Some b)
    :
    (Genv.find_symbol (Genv.globalenv p_a) id = Some b) \/
      (Genv.find_symbol (Genv.globalenv p_a) id = None /\
         exists cp, Genv.find_def (Genv.globalenv (gen_program btr p_a)) b = Some (gen_counter cp)).
  Proof.

    
Record program (F V : Type) : Type := mkprogram
  { prog_defs : list (ident * globdef F V);  prog_public : list ident;  prog_main : ident;  prog_pol : Policy.t }.

      unfold gen_program.
ListDec.In_dec: forall [A : Type], (forall x y : A, {x = y} + {x <> y}) -> forall (a : A) (l : list A), {In a l} + {~ In a l}
SetoidList.InA_alt:
  forall [A : Type] (eqA : A -> A -> Prop) (x : A) (l : list A), SetoidList.InA eqA x l <-> (exists y : A, eqA x y /\ In y l)
in_dec: forall [A : Type], (forall x y : A, {x = y} + {x <> y}) -> forall (a : A) (l : list A), {In a l} + {~ In a l}

Genv.globalenv_public: forall [F V : Type] (p : AST.program F V), Genv.genv_public (Genv.globalenv p) = AST.prog_public p



wf_counters = 
fun (ge : genv) (m : mem) (tr : bundle_trace) (cnts : cnt_ids) =>
(forall (id0 id1 : positive) (cnt : ident),
 cnts ! id0 = Some cnt -> cnts ! id1 = Some cnt -> id0 = id1) /\
(forall (id : ident) (b : block) (f : function),
 Genv.find_symbol ge id = Some b ->
 Genv.find_funct_ptr ge b = Some (Internal f) ->
 exists cnt : ident,
   cnts ! id = Some cnt /\
   wf_counter ge m (comp_of f) (Datatypes.length (get_id_tr tr id)) cnt)
     : genv -> mem -> bundle_trace -> cnt_ids -> Prop
  
Forall_map: forall [A B : Type] (f : A -> B) (P : B -> Prop) (l : list A), Forall P (map f l) <-> Forall (fun x : A => P (f x)) l
Forall_image:
  forall [A B : Type] (f : A -> B) (l : list B),
  Forall (fun y : B => exists x : A, y = f x) l <-> (exists l' : list A, l = map f l')

  Lemma gen_prog_defs_props
        (a_ge: Senv.t) tr (gds: list (ident * globdef Asm.fundef unit))
        (gen_gds: list (ident * globdef Clight.fundef type))
        cnts params
        (GEN: gen_gds = (map (fun '(id, gd) => (id, gen_progdef a_ge (get_id_tr tr id) gd (cnts ! id) (params ! id))) gds) ++ cnt_defs)
    :
    Forall (fun '(id, gd_c) =>
              ((id < r_cnt) ->
               exists gd_a, (In (id, gd_a) gds) /\ (gd_c = gen_progdef a_ge (get_id_tr tr id) gd_a (cnts ! id) (params ! id))) /\
                (r_cnt <= id
    
    
        
        

  (* Lemma gen_program_genv *)
  (*       btr (p_a: Asm.program) (p_c: Clight.program) *)
  (*       (P_C: p_c = gen_program btr p_a) *)
  (*   : *)
    

    
  Definition gen_prog_defs (a_ge: Senv.t) tr (gds: list (ident * globdef Asm.fundef unit)): list (ident * globdef Clight.fundef type) :=
    let m0 := next_id gds in
    let cnts := gen_counter_defs m0 gds in
    let cnt_defs := map snd (PTree.elements cnts) in
    let m1 := next_id cnt_defs in
    let params := gen_params m1 gds in
    (map (fun '(id, gd) => (id, gen_progdef a_ge (get_id_tr tr id) gd (cnts ! id) (params ! id))) gds) ++ cnt_defs.


Genv.find_symbol_exists:
  forall [F V : Type] (p : AST.program F V) (id : ident) (g : globdef F V),
  In (id, g) (AST.prog_defs p) -> exists b : block, Genv.find_symbol (Genv.globalenv p) id = Some b
Genv.find_symbol_inversion:
  forall [F V : Type] (p : AST.program F V) (x : ident) [b : block],
  Genv.find_symbol (Genv.globalenv p) x = Some b -> In x (prog_defs_names p)


Genv.globalenv = 
fun (F V : Type) (p : AST.program F V) =>
Genv.add_globals (Genv.empty_genv F V (AST.prog_public p) (AST.prog_pol p)) (AST.prog_defs p)
     : forall F V : Type, AST.program F V -> Genv.t F V

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
    
                  
    let cnts := gen_counter_defs m0 gds in
    let cnt_defs := map snd (PTree.elements cnts) in
wf_counter = 
fun (ge : Senv.t) (m : mem) (cp : compartment) (n : nat) (cnt : ident) =>
Senv.public_symbol ge cnt = false /\
(exists b : block,
   Senv.find_symbol ge cnt = Some b /\
   Mem.valid_access m Mint64 b 0 Writable (Some cp) /\ Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (nat64 n)))
     : Senv.t -> mem -> compartment -> nat -> ident -> Prop

gen_counter_defs = 
fun (m : positive) (gds : list (ident * globdef Asm.fundef unit)) =>
fold_left
  (fun (pt : PTree.tree (positive * globdef fundef type)) '(id, gd) => PTree.set id ((id + m)%positive, gen_counter (comp_of gd)) pt)
  gds (PTree.empty (positive * globdef fundef type))
     : positive -> list (ident * globdef Asm.fundef unit) -> PTree.t (ident * globdef fundef type)

Genv.alloc_global_exists:
  forall [F V : Type] {CF : has_comp F} (ge : Genv.t F V) (m : mem) (idg : ident * globdef F V),
  (let (_, y) := idg in
   match y with
   | Gfun _ => True
   | Gvar v =>
       Genv.init_data_list_aligned 0 (gvar_init v) /\
       (forall (i : ident) (o : ptrofs), In (Init_addrof i o) (gvar_init v) -> exists b : block, Genv.find_symbol ge i = Some b)
   end) -> exists m' : mem, Genv.alloc_global ge m idg = Some m'


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
  Lemma c_exists_init_mem
        btr (p: Asm.program)
        m_a
        (MEMA: Genv.init_mem p = Some m_a)
    :
    exists m_c, Genv.init_mem (gen_program btr p) = Some m_c.



  Definition gen_prog_defs (a_ge: Senv.t) tr (gds: list (ident * globdef Asm.fundef unit)): list (ident * globdef Clight.fundef type) :=
    let m0 := next_id gds in
    let cnts := gen_counter_defs m0 gds in
    let cnt_defs := map snd (PTree.elements cnts) in
    let m1 := next_id cnt_defs in
    let params := gen_params m1 gds in
    (map (fun '(id, gd) => (id, gen_progdef a_ge (get_id_tr tr id) gd (cnts ! id) (params ! id))) gds) ++ cnt_defs.

  Program Definition gen_program tr (a_p: Asm.program): Clight.program :=
    let a_ge := Genv.globalenv a_p in
    @Build_program _
                   (gen_prog_defs a_ge tr a_p.(AST.prog_defs))
                   (AST.prog_public a_p)
                   (AST.prog_main a_p)
                   (AST.prog_pol a_p)
                   []
                   (@PTree.empty composite)
                   _.





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
