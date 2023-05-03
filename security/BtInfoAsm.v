Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import riscV.Machregs.
Require Import riscV.Asm.
Require Import Complements.

Section HASINIT.
  Import Smallstep.

  Variant semantics_has_initial_trace_cut (L: Smallstep.semantics) (t: trace) : Prop :=
    | semantics_cut_runs :
      forall s, (initial_state L s) -> (exists s' beh', ((star (step L) (globalenv L)) s t s') /\ (state_behaves L s' beh')) -> semantics_has_initial_trace_cut _ t
    | semantics_cut_goes_initially_wrong : (forall s : state L, ~ initial_state L s) -> (t = nil) -> semantics_has_initial_trace_cut _ t.

  Definition semantics_has_initial_trace_prefix (L: Smallstep.semantics) (t: trace): Prop :=
    exists beh, (program_behaves L beh) /\ (behavior_prefix t beh).

  Lemma semantics_has_initial_trace_cut_implies_prefix
        L t
        (HAS: semantics_has_initial_trace_cut L t)
    :
    semantics_has_initial_trace_prefix L t.
  Proof.
    inversion HAS.
    - destruct H0 as (s' & beh' & STAR & BEH). red. exists (behavior_app t beh'). split.
      + econstructor 1. eauto. eapply state_behaves_app; eauto.
      + red. eauto.
    - subst. red. eexists. split.
      + econstructor 2. eauto.
      + red. exists (Goes_wrong E0). reflexivity.
  Qed.

  (* semantics_determinate: forall p : program, determinate (Asm.semantics p) *)
  (* sd_traces: forall [L : semantics], determinate L -> single_events L *)

  Lemma state_behaves_app_inv_one
        L s1 beh t beh'
        (SE: single_events L)
        (BEH: state_behaves L s1 beh)
        (APP: beh = behavior_app t beh')
        (ONE: (Datatypes.length t = 1)%nat)
    :
    exists s2, (Star L s1 t s2) /\ (state_behaves L s2 beh').
  Proof.
    destruct t; simpl in *. congruence. destruct t; simpl in *. 2: congruence. clear ONE.
    inv BEH.
    - destruct beh'; simpl in *; try congruence. inv H1.
      remember (e :: t0) as tr. revert e t0 i SE Heqtr H0. induction H; intros.
      { inv Heqtr. }
      subst. assert (SE0: single_events L) by auto. specialize (SE _ _ _ H). inv SE.
      + destruct t1; simpl in *. congruence. destruct t1; simpl in *. 2: congruence.
        inv Heqtr. exists s2. split. econstructor 2. eauto. econstructor 1. traceEq.
        econstructor; eauto.
      + destruct t1; simpl in *. 2: lia. clear H3.
        specialize (IHstar _ _ _ SE0 Heqtr H2). destruct IHstar as (s2' & STAR & TERM).
        exists s2'. split; auto. econstructor 2. eauto. eauto. traceEq.
    - destruct beh'; simpl in *; try congruence. inv H1.
      remember (e :: t0) as tr. revert e t0 SE Heqtr H0. induction H; intros.
      { inv Heqtr. }
      subst. assert (SE0: single_events L) by auto. specialize (SE _ _ _ H). inv SE.
      + destruct t1; simpl in *. congruence. destruct t1; simpl in *. 2: congruence.
        inv Heqtr. exists s2. split. econstructor 2. eauto. econstructor 1. traceEq.
        econstructor; eauto.
      + destruct t1; simpl in *. 2: lia. clear H3.
        specialize (IHstar _ _ SE0 Heqtr H2). destruct IHstar as (s2' & STAR & TERM).
        exists s2'. split; auto. econstructor 2. eauto. eauto. traceEq.
    - destruct beh'; simpl in *; try congruence. inv H0.
      inv H. revert e t SE T H2 H4 H0. induction H1; intros. congruence.
      subst. assert (SE0: single_events L) by auto. specialize (SE _ _ _ H). inv SE.
      + destruct t1; simpl in *. congruence. destruct t1; simpl in *. 2: congruence.
        clear H5. inv H3. destruct t2.
        * exists s3. split. econstructor 2. eauto. eauto. traceEq.
          econstructor. auto.
        * exists s2. split. econstructor 2. eauto. econstructor 1. traceEq.
          econstructor. econstructor. eauto. intros F. inv F. auto.
      + destruct t1; simpl in *. 2: lia. clear H5.
        specialize (IHstar _ _ SE0 _ H2 H4 H3). destruct IHstar as (s2' & STAR & TERM).
        exists s2'. split; auto. econstructor 2. eauto. eauto. traceEq.
    - destruct beh'; simpl in *; try congruence. inv H2.
      remember (e :: t0) as tr. revert e t0 SE Heqtr H0 H1. induction H; intros.
      { inv Heqtr. }
      subst. assert (SE0: single_events L) by auto. specialize (SE _ _ _ H). inv SE.
      + destruct t1; simpl in *. congruence. destruct t1; simpl in *. 2: congruence.
        clear H4. inv Heqtr. exists s2. split. econstructor 2. eauto. econstructor 1. traceEq.
        econstructor; eauto.
      + destruct t1; simpl in *. 2: lia. clear H4.
        specialize (IHstar _ _ SE0 Heqtr H2 H3). destruct IHstar as (s2' & STAR & TERM).
        exists s2'. split; auto. econstructor 2. eauto. eauto. traceEq.
  Qed.

  Lemma state_behaves_app_inv
        L s1 beh t beh'
        (SE: single_events L)
        (BEH: state_behaves L s1 beh)
        (APP: beh = behavior_app t beh')
    :
    exists s2, (Star L s1 t s2) /\ (state_behaves L s2 beh').
  Proof.
    revert s1 beh beh' SE BEH APP. induction t; intros.
    { rewrite behavior_app_E0 in APP. subst beh'. exists s1. split; auto. econstructor 1. }
    replace (a :: t) with ((a :: E0) ++ t) in *.
    2:{ simpl. auto. }
    rewrite behavior_app_assoc in APP. exploit state_behaves_app_inv_one.
    3: eapply APP. all: eauto.
    intros (s2 & STAR & NEXTBEH). specialize (IHt _ _ beh' SE NEXTBEH).
    exploit IHt; auto. intros (s3 & STAR2 & TERM).
    exists s3. split; auto. eapply star_trans; eauto.
  Qed.

  Lemma semantics_has_initial_trace_prefix_implies_cut
        L t
        (SE: single_events L)
        (HAS: semantics_has_initial_trace_prefix L t)
    :
    semantics_has_initial_trace_cut L t.
  Proof.
    inversion HAS. destruct H as [BEH (beh' & APP)]. subst x. inversion BEH; clear BEH.
    - subst beh. econstructor 1. eauto. exploit state_behaves_app_inv; eauto.
      intros (s2 & STAR & BEH). exists s2, beh'. auto.
    - econstructor 2. auto. destruct beh'; simpl in *; try congruence. inv H.
      symmetry in H2; apply Eapp_E0_inv in H2. destruct H2; auto.
  Qed.

End HASINIT.


Section INFORMATIVE.
  Import Smallstep.

  (* At CROSS-COMP calls, if fundef is ext, set to is_cross_ext. Otherwise is_not_ext. *)
  (* Similar at return. *)
  (* When a Event_call is is_cross_ext, do not back-translate the following Event_syscall and Event_return. *)
  Variant cross_ext := | is_cross_ext | not_cross_ext.

  (* Additional information *)
  Variant info_kind :=
    (* Get information for cross-comp calls and returns *)
    | info_call (ce: cross_ext) (sg: signature)
    | info_return (sg: signature)
    (* Get information for inter-comp external calls or builtins *)
    | info_external (b: block) (sg: signature)
    | info_builtin (ef: external_function)
    (* | info_default *)
  .

  (* Informative events *)
  Definition ievent := (event * info_kind)%type.
  Definition itrace := list ievent.

  Definition iE0: itrace := nil.

  (* Informative to original *)
  Definition iev_to_ev (ie: ievent) : event := (fst ie).
  Definition itr_to_tr (ies: itrace) : trace := map iev_to_ev ies.

  (* Informative behavior *)
  (* CoInductive itraceinf : Type :=  iEconsinf : ievent -> itraceinf -> itraceinf. *)
  (* CoFixpoint itri_to_tri (itri: itraceinf): traceinf := *)
  (*   match itri with iEconsinf hd tl => Econsinf (iev_to_ev hd) (itri_to_tri tl) end. *)

  (* Definition itri_to_tri_obs (itri: itraceinf) := *)
  (*   match itri with iEconsinf hd tl => iEconsinf hd tl end. *)

  (* Lemma itri_to_tri_obs_eq: forall itri, itri_to_tri_obs itri = itri. *)
  (* Proof. destruct itri; reflexivity. Qed. *)

  (* Fixpoint iEappinf (t: itrace) (T: itraceinf) {struct t} : itraceinf := *)
  (*   match t with *)
  (*   | nil => T *)
  (*   | ev :: t' => iEconsinf ev (iEappinf t' T) *)
  (*   end. *)


  (* Inductive iprogram_behavior : Type := *)
  (*   iTerminates : itrace -> int -> iprogram_behavior *)
  (* | iDiverges : itrace -> iprogram_behavior *)
  (* | iReacts : itraceinf -> iprogram_behavior *)
  (* | iGoes_wrong : itrace -> iprogram_behavior. *)

  (* Definition iph_to_pb (ipb: iprogram_behavior): program_behavior := *)
  (*   match ipb with *)
  (*   | iTerminates itr r => Terminates (itr_to_tr itr) r *)
  (*   | iDiverges itr => Diverges (itr_to_tr itr) *)
  (*   | iReacts itri => Reacts (itri_to_tri itri) *)
  (*   | iGoes_wrong itr => Goes_wrong (itr_to_tr itr) *)
  (*   end. *)

  Inductive istar {genv state : Type} (step : genv -> state -> itrace -> state -> Prop) (ge : genv) : state -> itrace -> state -> Prop :=
    istar_refl : forall s : state, istar step ge s nil s
  | istar_step : forall (s1 : state) (t1 : itrace) (s2 : state) (t2 : itrace) (s3 : state) (t : itrace),
      step ge s1 t1 s2 -> istar step ge s2 t2 s3 -> t = t1 ++ t2 -> istar step ge s1 t s3.


  (* Record isemantics : Type := *)
  (*   iSemantics_gen *)
  (*     { istate : Type; *)
  (*       igenvtype : Type; *)
  (*       istep : igenvtype -> istate -> itrace -> istate -> Prop; *)
  (*       iinitial_state : istate -> Prop; *)
  (*       ifinal_state : istate -> int -> Prop; *)
  (*       iglobalenv : igenvtype; *)
  (*       isymbolenv : Senv.t *)
  (*     }. *)

  (* Definition sem_to_isem (L: Smallstep.semantics) (istep: (genvtype L) -> (state L) -> itrace -> (state L) -> Prop) : isemantics := *)
  (*   iSemantics_gen _ _ istep (initial_state L) (final_state L) (globalenv L) (symbolenv L). *)

  CoInductive iforever_silent (genv state : Type) (step : genv -> state -> itrace -> state -> Prop) (ge : genv) : state -> Prop :=
    iforever_silent_intro : forall s1 s2 : state, step ge s1 nil s2 -> iforever_silent _ _ step ge s2 -> iforever_silent _ _ step ge s1.

  CoInductive iforever_reactive (genv state : Type) (step : genv -> state -> itrace -> state -> Prop) (ge : genv) : state -> itraceinf -> Prop :=
    iforever_reactive_intro : forall (s1 s2 : state) (t : itrace) (T : itraceinf),
        istar step ge s1 t s2 -> t <> nil -> iforever_reactive _ _ step ge s2 T -> iforever_reactive _ _ step ge s1 (iEappinf t T).

  Definition inostep := fun (genv state : Type) (step : genv -> state -> itrace -> state -> Prop) (ge : genv) (s : state) => forall (t : itrace) (s' : state), ~ step ge s t s'.

  Inductive istate_behaves (L : semantics) (istep: (genvtype L) -> (state L) -> itrace -> (state L) -> Prop) (s : state L): itrace -> program_behavior -> Prop :=
    istate_terminates : forall (t : itrace) (s' : state L) (r : int),
        (istar istep (globalenv L)) s t s' -> final_state L s' r -> istate_behaves L istep s t (Terminates (itr_to_tr t) r)
  | istate_diverges : forall (t : itrace) (s' : state L),
      (istar (istep) (globalenv L)) s t s' -> (forever_silent _ _ (step L) (globalenv L)) s' -> istate_behaves L istep s t (Diverges (itr_to_tr t))
  | istate_reacts : forall (t: itrace) (T : traceinf),
      (iforever_reactive _ _ (istep L) (iglobalenv L)) s T -> istate_behaves L istep s t (Reacts T)
  | istate_goes_wrong : forall (t : itrace) (s' : istate L),
      (istar (istep L) (iglobalenv L)) s t s' -> (inostep _ _ (istep L) (iglobalenv L)) s' -> (forall r : int, ~ ifinal_state L s' r) -> istate_behaves L s (iGoes_wrong t).

  Inductive iprogram_behaves (L : semantics) (istep: (genvtype L) -> (state L) -> itrace -> (state L) -> Prop): itrace -> program_behavior -> Prop :=
    iprogram_runs : forall (s : state L) (t: itrace) (beh : iprogram_behavior),
        initial_state L s -> istate_behaves L istep s t beh -> iprogram_behaves L t beh
  | iprogram_goes_initially_wrong : (forall s : state L, ~ initial_state L s) -> iprogram_behaves L nil (Goes_wrong nil).

  Definition semantics_has_initial_trace_informative (L: semantics) (istep: (genvtype L) -> (state L) -> itrace -> (state L) -> Prop) (t: itrace): Prop :=
    exists beh, (iprogram_behaves L istep t beh).

End INFORMATIVE.


Lemma iE0_left: forall t, iE0 ++ t = t.
Proof. auto. Qed.

Lemma iE0_right: forall t, t ++ iE0 = t.
Proof. intros. unfold iE0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma iEapp_assoc: forall (t1 t2 t3: itrace), (t1 ++ t2) ++ t3 = t1 ++ (t2 ++ t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma iEapp_E0_inv: forall t1 t2, t1 ++ t2 = iE0 -> t1 = iE0 /\ t2 = iE0.
Proof. eapply (@app_eq_nil ievent). Qed.

Lemma iE0_left_inf: forall T, iEappinf iE0 T = T.
Proof. auto. Qed.

Lemma iEappinf_assoc: forall t1 t2 T, iEappinf (t1 ++ t2) T = iEappinf t1 (iEappinf t2 T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

#[global]
Hint Rewrite iE0_left iE0_right iEapp_assoc
             iE0_left_inf iEappinf_assoc: itrace_rewrite.

Ltac isubstTraceHyp :=
  match goal with
  | [ H: (@eq itrace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac idecomposeTraceEq :=
  match goal with
  | [ |- (_ ++ _) = (_ ++ _) ] =>
      apply (f_equal2 app); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac itraceEq :=
  repeat isubstTraceHyp; autorewrite with itrace_rewrite; idecomposeTraceEq.


Section AUX.

  Definition ibehavior_app (t: itrace) (beh: iprogram_behavior): iprogram_behavior :=
    match beh with
    | iTerminates t1 r => iTerminates (t ++ t1) r
    | iDiverges t1 => iDiverges (t ++ t1)
    | iReacts T => iReacts (iEappinf t T)
    | iGoes_wrong t1 => iGoes_wrong (t ++ t1)
    end.

  Lemma ibehavior_app_assoc:
    forall t1 t2 beh,
      ibehavior_app (t1 ++ t2) beh = ibehavior_app t1 (ibehavior_app t2 beh).
  Proof.
    intros. destruct beh; simpl; f_equal; itraceEq.
  Qed.

  Lemma ibehavior_app_E0:
    forall beh, ibehavior_app iE0 beh = beh.
  Proof.
    destruct beh; auto.
  Qed.

  Definition ibehavior_prefix (t: itrace) (beh: iprogram_behavior) : Prop :=
    exists beh', beh = ibehavior_app t beh'.

End AUX.


Section ASMISTEP.

  Variable cpm: compartment.
  Variable ge: genv.

  (* Parameter low_half: genv -> ident -> ptrofs -> ptrofs. *)
  (* Parameter high_half: genv -> ident -> ptrofs -> val. *)

  (* Axiom low_high_half: *)
  (*   forall id ofs, *)
  (*   Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs. *)

  Inductive asm_istep: state -> itrace -> state -> Prop :=
  | exec_asm_istep_internal:
    forall b ofs f i rs m rs' m' b' ofs' st cp,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      forall (COMP: comp_of f = cp),
        exec_instr ge f i rs m cp = Next rs' m' ->
        sig_call i = None ->
        is_return i = false ->
        forall (NEXTPC: rs' PC = Vptr b' ofs'),
        forall (ALLOWED: cp = Genv.find_comp_ignore_offset ge (Vptr b' ofs')),
          asm_istep (State st rs m) nil (State st rs' m')
  | exec_asm_istep_internal_call:
    forall b ofs f i sig rs m rs' m' b' ofs' cp st st' args t it,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f i rs m cp = Next rs' m' ->
      sig_call i = Some sig ->
      forall (NEXTPC: rs' PC = Vptr b' ofs'),
      forall (ALLOWED: Genv.allowed_call ge (comp_of f) (Vptr b' ofs')),
      forall (CURCOMP: Genv.find_comp_ignore_offset ge (Vptr b Ptrofs.zero) = cp),
      (* Is a call, we update the stack *)
      forall (STUPD: update_stack_call ge st sig cp rs' = Some st'),
      forall (ARGS: call_arguments rs' m' sig args),
      (* Is a call, we check whether we are allowed to pass pointers *)
      forall (NO_CROSS_PTR:
          Genv.type_of_call ge (comp_of f) (Genv.find_comp_ignore_offset ge (Vptr b' ofs')) = Genv.CrossCompartmentCall ->
          List.Forall not_ptr args),
      forall (EV: call_trace ge (comp_of f) (Genv.find_comp_ignore_offset ge (Vptr b' ofs')) (Vptr b' ofs')
                        args (sig_args sig) t),
      forall (INFO: let ce := match (Genv.find_funct_ptr ge b', Genv.type_of_call ge (comp_of f) (Genv.find_comp_ignore_offset ge (Vptr b' ofs'))) with
                         | (Some (External ef), Genv.CrossCompartmentCall) => is_cross_ext
                         | _ => not_cross_ext
                         end in
               it = map (fun e => (e, info_call ce sig)) t),
        asm_istep (State st rs m) it (State st' rs' m')
  | exec_asm_istep_internal_return:
    forall b ofs f i rs m rs' cp m' st,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f i rs m cp = Next rs' m' ->
      is_return i = true ->
      forall (CURCOMP: Genv.find_comp_ignore_offset ge (rs PC) = cp),
      (* We attempt a return, so we go to a ReturnState*)
      (* The only condition is the following: we are currently in the compartment stored in the callee compartment field *)
      (*      of the top stack frame*)
      forall (REC_CURCOMP: Genv.find_comp_ignore_offset ge (rs PC) = callee_comp cpm st),
        (* forall (NEXTCOMP: Genv.find_comp_ignore_offset ge (rs' PC) = cp'), *)
        asm_istep (State st rs m) nil (ReturnState st rs' m')
  | exec_asm_istep_return:
    forall st st' rs m sg t rec_cp rec_cp' cp' it,
      rs PC <> Vnullptr -> (* this condition is there to stop the execution 1 asm_istep earlier, to make the proof easier *)
      forall (REC_CURCOMP: callee_comp cpm st = rec_cp),
      forall (REC_NEXTCOMP: call_comp ge st = rec_cp'),
      forall (NEXTCOMP: Genv.find_comp_ignore_offset ge (rs PC) = cp'),
      (* We only impose conditions on when returns can be executed for cross-compartment *)
      (*          returns. These conditions are that we restore the previous RA and SP *)
      forall (PC_RA: rec_cp <> cp' -> rs PC = asm_parent_ra st),
      forall (RESTORE_SP: rec_cp <> cp' -> rs SP = asm_parent_sp st),
      (* forall (RETURN_FROM_CP: cp <> cp' -> cp = callee_comp st), *)
      (* Note that in the same manner, this definition only updates the stack when doing *)
      (*        cross-compartment returns *)
      forall (STUPD: update_stack_return ge st rec_cp rs = Some st'),
      (* We do not return a pointer *)
      forall (SIG_STACK: sig_of_call st = sg),
      forall (NO_CROSS_PTR:
          (Genv.type_of_call ge cp' rec_cp = Genv.CrossCompartmentCall ->
           not_ptr (return_value rs sg))),
      forall (EV: return_trace ge cp' rec_cp (return_value rs sg) (sig_res sg) t),
      forall (INFO: it = map (fun e => (e, info_return sg)) t),
        asm_istep (ReturnState st rs m) it (State st' rs m)
  | exec_asm_istep_builtin:
    forall b ofs f ef args res rs m vargs t vres rs' m' st it,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge (comp_of f) vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                       (undef_regs (map preg_of (destroyed_by_builtin ef))
                                   (rs #X1 <- Vundef #X31 <- Vundef))) ->
      forall (INFO: it = map (fun e => (e, info_builtin ef)) t),
        asm_istep (State st rs m) it (State st rs' m')
  | exec_asm_istep_external:
    forall b ef args res rs m t rs' m' cp st it,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      forall COMP: Genv.find_comp_ignore_offset ge (rs RA) = cp, (* compartment that is calling the external function *)
        external_call ef ge cp args m t res m' ->
        extcall_arguments rs m (ef_sig ef) args ->
        rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
        (* These steps behave like returns. So we do the same as in the [exec_asm_istep_internal_return] case. *)
        forall (REC_CURCOMP: Genv.find_comp_ignore_offset ge (rs PC) = callee_comp cpm st),
        forall (INFO: it = map (fun e => (e, info_external b (ef_sig ef))) t),
          asm_istep (State st rs m) it (ReturnState st rs' m').

End ASMISTEP.


Section ASMISEM.

  Definition iasm_program_has_initial_trace :=
    fun (p : program) (t : itrace) =>
      let isem := sem_to_isem (semantics p) (asm_istep (prog_main p)) in
      exists beh : iprogram_behavior, (iprogram_behaves isem beh) /\ (ibehavior_prefix t beh).

  

End ASMISEM.
