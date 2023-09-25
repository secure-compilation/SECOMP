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


Section PROOFINIT.

  Definition asm_program_does_prefix (p: Asm.program) (t: trace) :=
    semantics_has_initial_trace_prefix (Asm.semantics p) t.
  Definition clight_program_does_prefix (p: Clight.program) (t: trace) :=
    semantics_has_initial_trace_prefix (Clight.semantics1 p) t.

  (* Lemma behaves_star_prefix *)
  (*       L beh *)
  (*       (s: Smallstep.state L) *)
  (*       (BEH: state_behaves L s beh) *)
  (*       tr *)
  (*       (PRE: behavior_prefix tr beh) *)
  (*   : *)
  (*   exists s', Star L s tr s'. *)
  (* Proof. *)

  (* Admitted. *)

  Theorem asm_to_clight
          (p: Asm.program) (ast: Asm.state)
          (WFP: wf_program p)
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
    eapply semantics_has_initial_trace_cut_implies_prefix. econs 1; ss.

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
