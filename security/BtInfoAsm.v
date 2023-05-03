Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import riscV.Machregs.
Require Import riscV.Asm.
Require Import Complements.

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

  (* Informative to original *)
  Definition iev_to_ev (ie: ievent) : event := (fst ie).
  Definition itr_to_tr (ies: itrace) : trace := map iev_to_ev ies.

  (* Informative behavior *)
  CoInductive itraceinf : Type :=  iEconsinf : ievent -> itraceinf -> itraceinf.
  CoFixpoint itri_to_tri (itri: itraceinf): traceinf :=
    match itri with iEconsinf hd tl => Econsinf (iev_to_ev hd) (itri_to_tri tl) end.

  Definition itri_to_tri_obs (itri: itraceinf) :=
    match itri with iEconsinf hd tl => iEconsinf hd tl end.

  Lemma itri_to_tri_obs_eq: forall itri, itri_to_tri_obs itri = itri.
  Proof. destruct itri; reflexivity. Qed.

  Inductive iprogram_behavior : Type :=
    iTerminates : itrace -> int -> iprogram_behavior
  | iDiverges : itrace -> iprogram_behavior
  | iReacts : itraceinf -> iprogram_behavior
  | iGoes_wrong : itrace -> iprogram_behavior.

  Definition iph_to_pb (ipb: iprogram_behavior): program_behavior :=
    match ipb with
    | iTerminates itr r => Terminates (itr_to_tr itr) r
    | iDiverges itr => Diverges (itr_to_tr itr)
    | iReacts itri => Reacts (itri_to_tri itri)
    | iGoes_wrong itr => Goes_wrong (itr_to_tr itr)
    end.

  Inductive istar {genv state : Type} (step : genv -> state -> itrace -> state -> Prop) (ge : genv) : state -> itrace -> state -> Prop :=
    istar_refl : forall s : state, istar step ge s nil s
  | istar_step : forall (s1 : state) (t1 : itrace) (s2 : state) (t2 : itrace) (s3 : state) (t : itrace),
      step ge s1 t1 s2 -> istar step ge s2 t2 s3 -> t = t1 ++ t2 -> istar step ge s1 t s3.


  Record isemantics : Type :=
    iSemantics_gen
      { istate : Type;
        igenvtype : Type;
        istep : igenvtype -> istate -> itrace -> istate -> Prop;
        iinitial_state : istate -> Prop;
        ifinal_state : istate -> int -> Prop;
        iglobalenv : igenvtype;
        isymbolenv : Senv.t
      }.

  Definition sem_to_isem (L: Smallstep.semantics) (istep: (genvtype L) -> (state L) -> itrace -> (state L) -> Prop) : isemantics :=
    iSemantics_gen _ _ istep (initial_state L) (final_state L) (globalenv L) (symbolenv L).

  CoInductive forever_silent (genv state : Type) (step : genv -> state -> trace -> state -> Prop) (ge : genv) : state -> Prop :=
    forever_silent_intro : forall s1 s2 : state, step ge s1 E0 s2 -> forever_silent step ge s2 -> forever_silent step ge s1.

  Inductive istate_behaves (L : isemantics) (s : istate L) : iprogram_behavior -> Prop :=
    istate_terminates : forall (t : itrace) (s' : istate L) (r : int),
        (istar (istep L) (iglobalenv L)) s t s' -> ifinal_state L s' r -> istate_behaves L s (iTerminates t r)
  | istate_diverges : forall (t : itrace) (s' : istate L),
      (istar (istep L) (iglobalenv L)) s t s' -> (forever_silent (istep L) (iglobalenv L)) s' -> istate_behaves L s (iDiverges t).
  | istate_reacts : forall T : itraceinf, forever_reactive L s T -> state_behaves L s (Reacts T)
  | istate_goes_wrong : forall (t : trace) (s' : Smallstep.state L), Star L s t s' -> Nostep L s' -> (forall r : int, ~ Smallstep.final_state L s' r) -> state_behaves L s (Goes_wrong t).


asm_program_has_initial_trace = fun (p : program) (t : trace) => forall beh : program_behavior, program_behaves (semantics p) beh -> behavior_prefix t beh
     : program -> trace -> Prop
Inductive program_behaves (L : Smallstep.semantics) : program_behavior -> Prop :=
    program_runs : forall (s : Smallstep.state L) (beh : program_behavior), Smallstep.initial_state L s -> state_behaves L s beh -> program_behaves L beh
  | program_goes_initially_wrong : (forall s : Smallstep.state L, ~ Smallstep.initial_state L s) -> program_behaves L (Goes_wrong E0).
Inductive state_behaves (L : Smallstep.semantics) (s : Smallstep.state L) : program_behavior -> Prop :=
    state_terminates : forall (t : trace) (s' : Smallstep.state L) (r : int), Star L s t s' -> Smallstep.final_state L s' r -> state_behaves L s (Terminates t r)
  | state_diverges : forall (t : trace) (s' : Smallstep.state L), Star L s t s' -> Forever_silent L s' -> state_behaves L s (Diverges t)
  | state_reacts : forall T : traceinf, Forever_reactive L s T -> state_behaves L s (Reacts T)
| state_goes_wrong : forall (t : trace) (s' : Smallstep.state L), Star L s t s' -> Nostep L s' -> (forall r : int, ~ Smallstep.final_state L s' r) -> state_behaves L s (Goes_wrong t).

End INFORMATIVE.


Section ASMISTEP.

  Variable cpm: compartment.
  Variable ge: genv.

  (* Parameter low_half: genv -> ident -> ptrofs -> ptrofs. *)
  (* Parameter high_half: genv -> ident -> ptrofs -> val. *)

  (* Axiom low_high_half: *)
  (*   forall id ofs, *)
  (*   Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs. *)

  Inductive istep: state -> itrace -> state -> Prop :=
  | exec_istep_internal:
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
          istep (State st rs m) nil (State st rs' m')
  | exec_istep_internal_call:
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
        istep (State st rs m) it (State st' rs' m')
  | exec_istep_internal_return:
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
        istep (State st rs m) nil (ReturnState st rs' m')
  | exec_istep_return:
    forall st st' rs m sg t rec_cp rec_cp' cp' it,
      rs PC <> Vnullptr -> (* this condition is there to stop the execution 1 istep earlier, to make the proof easier *)
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
        istep (ReturnState st rs m) it (State st' rs m)
  | exec_istep_builtin:
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
        istep (State st rs m) it (State st rs' m')
  | exec_istep_external:
    forall b ef args res rs m t rs' m' cp st it,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      forall COMP: Genv.find_comp_ignore_offset ge (rs RA) = cp, (* compartment that is calling the external function *)
        external_call ef ge cp args m t res m' ->
        extcall_arguments rs m (ef_sig ef) args ->
        rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
        (* These steps behave like returns. So we do the same as in the [exec_istep_internal_return] case. *)
        forall (REC_CURCOMP: Genv.find_comp_ignore_offset ge (rs PC) = callee_comp cpm st),
        forall (INFO: it = map (fun e => (e, info_external b (ef_sig ef))) t),
          istep (State st rs m) it (ReturnState st rs' m').

  Inductive istar {genv state : Type} (step : genv -> state -> itrace -> state -> Prop) (ge : genv) : state -> itrace -> state -> Prop :=
    istar_refl : forall s : state, istar step ge s nil s
  | istar_step : forall (s1 : state) (t1 : itrace) (s2 : state) (t2 : itrace) (s3 : state) (t : itrace),
      step ge s1 t1 s2 -> istar step ge s2 t2 s3 -> t = t1 ++ t2 -> istar step ge s1 t s3.

End ASMISTEP.


Section INFOASM.

  Variable cpm: compartment.

  Inductive istate_behaves (L : Smallstep.semantics) (s : Smallstep.state L) : iprogram_behavior -> Prop :=
    istate_terminates : forall (t : itrace) (s' : Smallstep.state L) (r : int),
        (istar (istep cpm) (globalenv L)) s t s' -> Smallstep.final_state L s' r -> istate_behaves L s (iTerminates t r).
  | istate_diverges : forall (t : itrace) (s' : Smallstep.state L), (istar istep (globalenv L)) s t s' -> (forever_silent istep (globalenv L)) s' -> istate_behaves L s (iDiverges t)
  | istate_reacts : forall T : itraceinf, forever_reactive L s T -> state_behaves L s (Reacts T)
  | istate_goes_wrong : forall (t : trace) (s' : Smallstep.state L), Star L s t s' -> Nostep L s' -> (forall r : int, ~ Smallstep.final_state L s' r) -> state_behaves L s (Goes_wrong t).


asm_program_has_initial_trace = fun (p : program) (t : trace) => forall beh : program_behavior, program_behaves (semantics p) beh -> behavior_prefix t beh
     : program -> trace -> Prop
Inductive program_behaves (L : Smallstep.semantics) : program_behavior -> Prop :=
    program_runs : forall (s : Smallstep.state L) (beh : program_behavior), Smallstep.initial_state L s -> state_behaves L s beh -> program_behaves L beh
  | program_goes_initially_wrong : (forall s : Smallstep.state L, ~ Smallstep.initial_state L s) -> program_behaves L (Goes_wrong E0).
Inductive state_behaves (L : Smallstep.semantics) (s : Smallstep.state L) : program_behavior -> Prop :=
    state_terminates : forall (t : trace) (s' : Smallstep.state L) (r : int), Star L s t s' -> Smallstep.final_state L s' r -> state_behaves L s (Terminates t r)
  | state_diverges : forall (t : trace) (s' : Smallstep.state L), Star L s t s' -> Forever_silent L s' -> state_behaves L s (Diverges t)
  | state_reacts : forall T : traceinf, Forever_reactive L s T -> state_behaves L s (Reacts T)
| state_goes_wrong : forall (t : trace) (s' : Smallstep.state L), Star L s t s' -> Nostep L s' -> (forall r : int, ~ Smallstep.final_state L s' r) -> state_behaves L s (Goes_wrong t).

End INFOASM.
