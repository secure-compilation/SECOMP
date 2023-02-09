Require Import String.
Require Import Coqlib Maps Errors.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Csyntax Asm.
Require Import Compiler Complements.

Section Split.

  Variant side := Left | Right.

  Definition split := compartment -> side.

  Fixpoint unlink_prog_defs_left (s: split) (defs: list (ident * globdef (Ctypes.fundef Csyntax.function) Ctypes.type)):
    list (ident * globdef (Ctypes.fundef Csyntax.function) Ctypes.type) :=
    match defs with
    | nil => nil
    | (id, d) :: defs' =>
        match d with
        | Gfun (Ctypes.Internal f) =>
            match s (Csyntax.fn_comp f) with
            | Left => (id, Gfun (Ctypes.Internal f)) :: (unlink_prog_defs_left s defs')
            | Right => (id, Gfun (Ctypes.External (EF_external ""
                                                    (Csyntax.fn_comp f)
                                                    {| sig_args := map (fun '(x, ty) => Ctypes.typ_of_type ty) (fn_params f);
                                                      sig_res := Ctypes.typ_of_type (fn_return f);
                                                      sig_cc := fn_callconv f|})
                      (Ctypes.type_of_params (Csyntax.fn_params f)) (fn_return f) (fn_callconv f))) ::
                        (unlink_prog_defs_left s defs')
            end
        | Gfun (Ctypes.External f tys ty cc) => (id, Gfun (Ctypes.External f tys ty cc)) :: (unlink_prog_defs_left s defs')
        | Gvar v => (id, Gvar v) :: (unlink_prog_defs_left s defs')
        end
    end
    .

  Fixpoint unlink_prog_defs_right (s: split) (defs: list (ident * globdef (Ctypes.fundef Csyntax.function) Ctypes.type)):
    list (ident * globdef (Ctypes.fundef Csyntax.function) Ctypes.type) :=
    match defs with
    | nil => nil
    | (id, d) :: defs' =>
        match d with
        | Gfun (Ctypes.Internal f) =>
            match s (Csyntax.fn_comp f) with
            | Right => (id, Gfun (Ctypes.Internal f)) :: (unlink_prog_defs_left s defs')
            | Left => (id, Gfun (Ctypes.External (EF_external ""
                                                    (Csyntax.fn_comp f)
                                                    {| sig_args := map (fun '(x, ty) => Ctypes.typ_of_type ty) (fn_params f);
                                                      sig_res := Ctypes.typ_of_type (fn_return f);
                                                      sig_cc := fn_callconv f|})
                      (Ctypes.type_of_params (Csyntax.fn_params f)) (fn_return f) (fn_callconv f))) ::
                        (unlink_prog_defs_left s defs')
            end
        | Gfun (Ctypes.External f tys ty cc) => (id, Gfun (Ctypes.External f tys ty cc)) :: (unlink_prog_defs_left s defs')
        | Gvar v => (id, Gvar v) :: (unlink_prog_defs_left s defs')
        end
    end
    .

  Definition unlink (s: split) (p: Csyntax.program): Csyntax.program * Csyntax.program :=
    ({| Ctypes.prog_defs := unlink_prog_defs_left s (Ctypes.prog_defs p);
       Ctypes.prog_public := Ctypes.prog_public p;
       Ctypes.prog_main := Ctypes.prog_main p;
       Ctypes.prog_pol := Ctypes.prog_pol p;
       Ctypes.prog_types := Ctypes.prog_types p;
       Ctypes.prog_comp_env := Ctypes.prog_comp_env p;
       Ctypes.prog_comp_env_eq := Ctypes.prog_comp_env_eq p;
    |},
    {| Ctypes.prog_defs := unlink_prog_defs_right s (Ctypes.prog_defs p);
       Ctypes.prog_public := Ctypes.prog_public p;
       Ctypes.prog_main := Ctypes.prog_main p;
       Ctypes.prog_pol := Ctypes.prog_pol p;
       Ctypes.prog_types := Ctypes.prog_types p;
       Ctypes.prog_comp_env := Ctypes.prog_comp_env p;
       Ctypes.prog_comp_env_eq := Ctypes.prog_comp_env_eq p;
    |}).

    Lemma link_unlink (s: split):
      forall p p1 p2,
        unlink s p = (p1, p2) ->
        link p1 p2 = Some p.
    Proof.
      intros.
      Local Transparent Ctypes.Linker_program Ctypes.link_program Linker_prog.
      unfold link, Ctypes.Linker_program, Ctypes.link_program, link, Linker_prog; simpl.
      rewrite link_prog_succeeds; simpl.
      - destruct p1, p2; inv H. simpl. admit.
      - destruct p1, p2; inv H; reflexivity.
      - destruct p1, p2; inv H. unfold prog_defmap; simpl.
        remember (Ctypes.prog_defs p) as l. clear Heql.
        induction l.
        + intros; simpl in *. inv H.
        + intros. apply PTree_Properties.in_of_list in H, H0.
          (* I would like to prove that (id, gd1) and (id, gd2) are necessarily found at the same
           position in the list. I need to prove some kind of uniqueness of the definitions, but I couldn't
           find what I need to prove that. *)
          admit.
      - destruct p1, p2; inv H. simpl. now rewrite Policy.eqb_refl.
    Admitted.

Section RSC.

  Variable pol: Policy.t.
  Variable s: split.

  Variable p: Csyntax.program.
  Hypothesis pol_p: Ctypes.prog_pol p = pol.

  Variable p_compiled: Asm.program.

  Variable Ct: Asm.program.
  Hypothesis pol_Ct: prog_pol Ct = pol.

  Variable W_t: Asm.program.

  Hypothesis p_p_compiled: transf_c_program p = OK p_compiled.
  (* TODO: move to Compiler.v file *)
  Lemma transf_c_program_pol: forall p p',
      transf_c_program p = OK p' ->
      Ctypes.prog_pol p = prog_pol p'.
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
  Axiom c_program_blame: Csyntax.program -> Csyntax.program -> trace -> Prop.

  Axiom backtranslation: Policy.t -> trace -> Csyntax.program.
  Axiom backtranslation_correct:
    forall pol t,
      c_program_has_initial_trace (backtranslation pol t) t.
  Axiom backtranslation_pol: forall pol t,
      Ctypes.prog_pol (backtranslation pol t) = pol.
  Axiom backtranslation_compile: forall pol t,
      exists W_compiled,
        transf_c_program (backtranslation pol t) = OK W_compiled.

  Axiom split_along_interface: Csyntax.program -> Csyntax.program -> Asm.program -> (Csyntax.program * Csyntax.program).
  Axiom split_along_interface_correct_1:
    forall W ps pt p p',
      split_along_interface W ps pt = (p, p') ->
      exists W', link ps p' = Some W'.

  Axiom split_along_interface_compilation_correct:
    forall W W_compiled ps pt p p',
      split_along_interface W ps pt = (p, p') ->
      transf_c_program W = OK W_compiled ->
      exists p_compiled p'_compiled,
        transf_c_program p = OK p_compiled /\
        transf_c_program p' = OK p'_compiled /\
        link p_compiled p'_compiled = Some W_compiled.

  Axiom compatible: Asm.program -> Asm.program -> Asm.program -> Asm.program -> Prop.
  Axiom recomposition:
    forall W W'' p1 p2 p1'' p2'' t,
      link p1 p2 = Some W ->
      link p1'' p2'' = Some W'' ->
      compatible p1 p2 p1'' p2'' ->
      asm_program_has_initial_trace W t ->
      asm_program_has_initial_trace W'' t ->
      exists W',
        link p1 p2'' = Some W' /\
          asm_program_has_initial_trace W' t.

  Axiom backward_correctness:
    forall W W' t,
      transf_c_program W = OK W' ->
      asm_program_has_initial_trace W' t ->
      (c_program_has_initial_trace W t \/ exists m, trace_prefix m t /\ c_program_blame W p m).

  Theorem RSC:
    forall (t: trace),
      asm_program_has_initial_trace W_t t ->
      exists (Cs: Csyntax.program) (W: Csyntax.program),
        link p Cs = Some W /\
        (c_program_has_initial_trace W t \/
         exists (m: trace), trace_prefix m t /\ c_program_blame W p m).
  Proof.
    intros t H.
    set (W_bt := backtranslation pol t).
    destruct (split_along_interface W_bt p Ct) as (p', Cs) eqn:split_bt; subst W_bt.
    exists Cs.
    exploit split_along_interface_correct_1; eauto.
    intros [W link_W].
    exists W; split; eauto.

    (* Backtranslation *)
    destruct (backtranslation_compile pol t) as [W_compiled W_bt_compiled].
    assert (W_compiled_t: asm_program_has_initial_trace W_compiled t).
    { intros beh W_compiled_beh.
      eapply transf_c_program_preserves_initial_trace; eauto.
      now apply backtranslation_correct. }

    (* Split the compilation of the back-translation *)
    exploit split_along_interface_compilation_correct; eauto.
    intros [p'_compiled [Cs_compiled [p'_p'_compiled [Cs_Cs_compiled link_W_compiled]]]].

    (* Recomposition *)
    pose proof (recomposition W_t W_compiled) as recomp.
    exploit recomp; eauto.
    { (* We should define what [compatible] means and add it to the axioms of [split], but this seems
       tedious, so I'm leaving it for later. *) admit. }
    clear recomp.
    intros [W' [link_W' W'_t]].

    (* Backward compiler correctness *)
    assert (W_W': transf_c_program W = OK W').
    { admit. (* This comes from commutativity of linking and compilation: transf_link *) }
    exploit backward_correctness; eauto.
  Admitted.
