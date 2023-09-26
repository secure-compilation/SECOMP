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
