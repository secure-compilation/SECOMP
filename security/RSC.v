Require Import String.
Require Import Coqlib Maps Errors.
Require Import AST Linking Smallstep Events Behaviors.
Require Import Split.

(* TODO: Change everything to start from Clight instead of C. *)
Require Import Clight Asm.
Require Import Compiler Complements.

Section Split.

    Definition clight_has_side (s: split) (lr: side) (p: Clight.program) :=
      List.Forall (fun '(id, gd) =>
                     match gd with
                     | Gfun (Ctypes.Internal f) => s (comp_of f) = lr
                     | _ => True
                     end)
        (Ctypes.prog_defs p).

    Definition asm_has_side (s: split) (lr: side) (p: Asm.program) :=
      List.Forall (fun '(id, gd) =>
                     match gd with
                     | Gfun (Internal f) => s (comp_of f) = lr
                     | _ => True
                     end)
        (prog_defs p).

    Definition clight_compatible (s: split) (p p': Clight.program) :=
      clight_has_side s Left p /\ clight_has_side s Right p'.

    Definition asm_compatible (s: split) (p p': Asm.program) :=
      asm_has_side s Left p /\ asm_has_side s Right p'.

    Lemma link_compatible: forall s p p',
        clight_compatible s p p' ->
        Ctypes.prog_pol p = Ctypes.prog_pol p' ->
        exists W, link p p' = Some W.
    Proof.
      admit.
    Admitted.

End Split.

Section RSC.

  Variable pol: Policy.t.
  Variable s: split.

  Variable p: Clight.program.
  Hypothesis pol_p: Ctypes.prog_pol p = pol.
  Hypothesis p_Left: clight_has_side s Left p.

  Variable p_compiled: Asm.program.

  Variable Ct: Asm.program.
  Hypothesis pol_Ct: prog_pol Ct = pol.
  Hypothesis Ct_Right: asm_has_side s Right Ct.

  Variable W_t: Asm.program.

  Hypothesis p_p_compiled: transf_clight_program p = OK p_compiled.
  (* TODO: move to Compiler.v file *)
  Lemma transf_clight_program_pol: forall p p',
      transf_clight_program p = OK p' ->
      Ctypes.prog_pol p = prog_pol p'.
  Proof.
    admit.
  Admitted.

  Lemma transf_clight_program_side: forall p p' lr,
      transf_clight_program p = OK p' ->
      clight_has_side s lr p <-> asm_has_side s lr p'.
  Proof.
    admit.
  Admitted.

  Lemma transf_clight_program_compatible: forall p1 p1' p2 p2',
      match_prog_Clight p1 p1' ->
      match_prog_Clight p2 p2' ->
      (* transf_c_program p1 = OK p1' -> *)
      (* transf_c_program p2 = OK p2' -> *)
      clight_compatible s p1 p2 <-> asm_compatible s p1' p2'.
  Proof.
    admit.
  Admitted.

  Hypothesis W_t_is_Ct_p_compiled: link p_compiled Ct = Some W_t.
  (* TODO: move to Linker.v *)
  Lemma link_pol: forall p p' p'',
      link p p' = Some p'' ->
      prog_pol p = prog_pol p''.
  Proof.
    admit.
  Admitted.

  (* TODO: What does blame mean? *)
  Axiom c_program_blame: Clight.program -> Clight.program -> trace -> Prop.

  Axiom backtranslation: Policy.t -> split -> trace -> Clight.program * Clight.program.
  Axiom backtranslation_correct:
    forall pol s t p C,
      backtranslation pol s t = (p, C) ->
      clight_compatible s p C /\
      exists W, link p C = Some W /\
             clight_program_has_initial_trace W t.

  Axiom backtranslation_compiles:
    forall pol s t p C,
      backtranslation pol s t = (p, C) ->
      exists p_compiled C_compiled,
        transf_clight_program p = OK p_compiled /\
          transf_clight_program C = OK C_compiled.

  Axiom backtranslation_pol: forall pol s t,
      Ctypes.prog_pol (fst (backtranslation pol s t)) = pol /\
      Ctypes.prog_pol (snd (backtranslation pol s t)) = pol.

  Axiom forward_correctness:
    forall W W' t,
      match_prog_Clight W W' ->
      clight_program_has_initial_trace W t ->
      asm_program_has_initial_trace W' t.


  Axiom recomposition:
    forall W W'' p1 p2 p1'' p2'' t,
      link p1 p2 = Some W ->
      link p1'' p2'' = Some W'' ->
      asm_compatible s p1 p2 ->
      asm_compatible s p1'' p2'' ->
      asm_program_has_initial_trace W t ->
      asm_program_has_initial_trace W'' t ->
      exists W',
        link p1 p2'' = Some W' /\
          asm_program_has_initial_trace W' t.

  Axiom backward_correctness:
    forall W W' t,
      (* transf_c_program W = OK W' -> *)
      match_prog_Clight W W' ->
      asm_program_has_initial_trace W' t ->
      (clight_program_has_initial_trace W t \/
         exists m, trace_prefix m t /\ m <> t /\ program_behaves (Clight.semantics1 W) (Goes_wrong m)).

  Definition comp_of_event_or_default (e: event) (cp: compartment) :=
    match e with
    | Event_syscall _ _ _ => cp
    | Event_vload _ _ _ _ => cp
    | Event_vstore _ _ _ _ => cp
    | Event_annot _ _ => cp
    | Event_call _ cp' _ _ => cp'
    | Event_return _ cp' _ => cp'
    end.

  Fixpoint last_comp_in_trace' (t: trace) (cp: compartment): compartment :=
    match t with
    | nil => cp
    | e :: t' => last_comp_in_trace' t' (comp_of_event_or_default e cp)
    end.

  Definition last_comp_in_trace (t: trace): compartment :=
    last_comp_in_trace' t default_compartment.

  Definition blame_on_program (t: trace) :=
    s (last_comp_in_trace t) = Left.

  Axiom blame:
    forall W W' p1 p2 C t m,
      link p1 C = Some W ->
      link p2 C = Some W' ->
      clight_program_has_initial_trace W' t ->
      trace_prefix m t ->
      m <> t ->
      program_behaves (Clight.semantics1 W) (Goes_wrong m) ->
      blame_on_program m.

  Theorem RSC:
    forall (t: trace),
      asm_program_has_initial_trace W_t t ->
      exists (Cs: Clight.program) (W: Clight.program),
        link p Cs = Some W /\
        (clight_program_has_initial_trace W t \/
         exists (m: trace), trace_prefix m t /\ m <> t /\
                         program_behaves (Clight.semantics1 W) (Goes_wrong m) /\ blame_on_program m).
  Proof.
    intros t H.
    (* Backtranslation *)
    destruct (backtranslation pol s t) as [p' Cs] eqn:split_bt.
    pose proof (backtranslation_correct pol s t p' Cs split_bt) as bt_does_t.
    destruct bt_does_t as [bt_compat [Wbt [link_bt bt_does_t]]].

    exists Cs.
    destruct (link_compatible s p Cs) as [W link_p_Cs].
    split; [eauto | now destruct bt_compat].
    pose proof (backtranslation_pol pol s t) as [? bt_pol].
    rewrite split_bt in bt_pol; simpl in bt_pol.
    rewrite bt_pol, pol_p; eauto.
    exists W; split; eauto.

    (* Forward compiler correctness *)
    pose proof (backtranslation_compiles pol s t p' Cs split_bt) as bt_compiles.
    destruct bt_compiles as [p'_compiled [Cs_compiled [p'_compiles Cs_compiles]]].
    destruct (@transf_link _ _ _ _ _ (pass_match_link (compose_passes CLightCompCert's_passes))
                p' Cs p'_compiled Cs_compiled Wbt link_bt
                (transf_clight_program_match _ _ p'_compiles) (transf_clight_program_match _ _ Cs_compiles)) as [Wbt_compiled [Wbt_compiles ?]].
    simpl in Wbt_compiled.
    assert (W_compiled_t: asm_program_has_initial_trace Wbt_compiled t).
    { eapply forward_correctness; eauto. }

    (* Recomposition *)
    pose proof (recomposition W_t Wbt_compiled) as recomp.
    exploit recomp; eauto.
    { split; [eapply transf_clight_program_side; eauto | eauto]. }
    { split; [eapply transf_clight_program_side; eauto | eapply transf_clight_program_side; eauto].
    now destruct bt_compat. now destruct bt_compat. }
    clear recomp.
    intros [W' [link_W' W'_t]].

    (* Backward compiler correctness *)
    assert (W_W': match_prog_Clight W W').
    { destruct (@transf_link _ _ _ _ _ (pass_match_link (compose_passes CLightCompCert's_passes))
                p Cs p_compiled Cs_compiled W link_p_Cs
                (transf_clight_program_match _ _ p_p_compiled) (transf_clight_program_match _ _ Cs_compiles)) as [W'' [R G]].
      assert (W'' = W') by now simpl in *; congruence. subst W''.
      eauto. }
    exploit backward_correctness; eauto.
    intros [G | [m [prefix_m_t [m_not_t W_behaves_m]]]]; [now left | right].
    exists m; split; [| split; [| split]]; eauto.
    eapply blame with (W' := Wbt); eauto.
  Qed.

End RSC.
