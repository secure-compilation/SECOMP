Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import Ctypes Clight.

Record backtranslation_environment :=
  { local_counter: compartment -> ident }.

Section Backtranslation.

  Variable bt_env: backtranslation_environment.

  Definition ptr_of_id_ofs (id: ident) (ofs: ptrofs): expr :=
    Ebinop Cop.Oadd
      (Eaddrof (Evar id Tvoid) (Tpointer Tvoid noattr))
      (Econst_int (Ptrofs.to_int ofs) (Tint I32 Signed noattr))
      (Tpointer Tvoid noattr).

  Fixpoint list_eventval_to_typelist (vs: list eventval): typelist :=
    match vs with
    | nil => Tnil
    | cons v vs' => Tcons Tvoid (list_eventval_to_typelist vs')
    end. (* TODO: currently this is just a list of Tvoid of the right size. Fix? *)

  Definition eventval_to_expr (v: eventval): expr :=
    match v with
    | EVint i => Econst_int i (Tint I32 Signed noattr)
    | EVlong i => Econst_long i (Tlong Signed noattr)
    | EVfloat f => Econst_float f (Tfloat F32 noattr)
    | EVsingle f => Econst_single f (Tfloat F32 noattr)
    | EVptr_global id ofs => Ebinop Cop.Oadd
                              (Eaddrof (Evar id Tvoid) (Tpointer Tvoid noattr))
                              (Econst_int (Ptrofs.to_int ofs) (Tint I32 Signed noattr))
                              (Tpointer Tvoid noattr)
    end.

  Definition list_eventval_to_list_expr (vs: list eventval): list expr :=
    List.map eventval_to_expr vs.

  (* An [event_syscall] does not need any code, because it is only generated after a call to an external function *)
  Definition code_of_syscall (name: string) (vs: list eventval) (v: eventval) := Sskip.

  Definition code_of_vload (ch: memory_chunk) (id: ident) (ofs: Ptrofs.int) (v: eventval) :=
    Sbuiltin None (EF_vload ch) (Tcons (Tpointer Tvoid noattr) Tnil) (ptr_of_id_ofs id ofs :: nil).

  Definition code_of_vstore (ch: memory_chunk) (id: ident) (ofs: Ptrofs.int) (v: eventval) :=
    Sbuiltin None (EF_vstore ch) (Tcons (Tpointer Tvoid noattr) Tnil) (ptr_of_id_ofs id ofs :: nil).

  Definition code_of_annot (str: string) (vs: list eventval) :=
    Sbuiltin None (EF_annot
                     (Pos.of_nat (List.length (typlist_of_typelist (list_eventval_to_typelist vs))))
                     str
                     (typlist_of_typelist (list_eventval_to_typelist vs))
           ) (list_eventval_to_typelist vs)
           (list_eventval_to_list_expr vs).

  Definition code_of_call (cp cp': compartment) (id: ident) (vs: list eventval) :=
    Scall None (Evar id (Tfunction (list_eventval_to_typelist vs) Tvoid cc_default)) (list_eventval_to_list_expr vs).

  Definition code_of_return (cp cp': compartment) (v: eventval) :=
    Sreturn (Some (eventval_to_expr v)).

  Definition code_of_event (e: event): statement :=
    match e with
    | Event_syscall name vs v => code_of_syscall name vs v
    | Event_vload ch id ofs v => code_of_vload ch id ofs v
    | Event_vstore ch id ofs v => code_of_vstore ch id ofs v
    | Event_annot str vs => code_of_annot str vs
    | Event_call cp cp' id vs => code_of_call cp cp' id vs
    | Event_return cp cp' v => code_of_return cp cp' v
    end.

  Definition type_counter: type := Tint I32 Unsigned noattr.
  Definition type_bool:    type := Tint IBool Signed noattr.

  Definition switch_clause (cp: compartment) (n: Z) (s_then s_else: statement): statement :=
    let one := Econst_int (Int.repr 1%Z) (Tint I32 Unsigned noattr) in
    Sifthenelse (Ebinop Cop.Oeq
                   (Evar (bt_env.(local_counter) cp) type_counter)
                   (Econst_int (Int.repr n) (Tint I32 Unsigned noattr)) type_bool)
                (* if true *)
                (Ssequence
                   (Sassign (Evar (bt_env.(local_counter) cp) type_counter)
                      (Ebinop Cop.Oadd (Evar (bt_env.(local_counter) cp) type_counter) one type_counter))
                   s_then)
                (* if false *)
                s_else.

  Ltac simpl_expr :=
    unfold type_counter; unfold type_bool; simpl;
    repeat (match goal with
            | |- eval_expr _ _ _ _ _ _ _ => econstructor
            | |- eval_lvalue _ _ _ _ _ _ _ _ _ => econstructor
            | |- deref_loc _ _ _ _ _ _ _ => econstructor
            | |- assign_loc _ _ _ _ _ _ _ _ _ => econstructor
            | |- Cop.sem_cmp _ _ _ _ _ _ = Some _ => unfold Cop.sem_cmp
            | |- Cop.sem_add _ _ _ _ _ _ = Some _ => unfold Cop.sem_add
            | |- Cop.sem_binarith _ _ _ _ _ _ _ _ _ = Some _ => unfold Cop.sem_binarith
            | |- match Cop.sem_cast _ ?x ?x _ with | _ => _ end = Some _ => rewrite Cop.cast_val_casted
            | |- Cop.sem_cast _ ?y ?y _ = Some _ => rewrite Cop.cast_val_casted
            | |- Cop.val_casted _ _ => constructor
            | H: ?x = _ |- Cop.bool_val (_ ?x) _ _ = Some _ => rewrite H; try reflexivity
            end; simpl; eauto).

  Ltac take_step := econstructor; [econstructor; simpl_expr | | traceEq]; simpl.

  Lemma switch_clause_spec p (cp: compartment) f (e: env) le m b (n: int) (n': Z) s_then s_else:
    cp = comp_of f ->
    e ! (bt_env.(local_counter) cp) = Some (b, type_counter) ->
    Mem.valid_access m Mint32 b 0 Writable (Some cp) ->
    Mem.loadv Mint32 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vint n) ->
    if Int.eq n (Int.repr n') then
      exists m',
        Mem.storev Mint32 m (Vptr b Ptrofs.zero) (Vint (Int.add n Int.one)) cp = Some m' /\
        (* Memory.store mem (C, Block.local, 0%Z) (Int (Z.succ n)) = Some mem' /\ *)
        Star (Clight.semantics1 p) (State f (switch_clause cp n' s_then s_else) Kstop e le m) E0 (State f s_then Kstop e le m')
    else
        Star (Clight.semantics1 p) (State f (switch_clause cp n' s_then s_else) Kstop e le m) E0 (State f s_else Kstop e le m).
    Proof.
      intros; subst cp.
      destruct (Int.eq n (Int.repr n')) eqn:eq_n_n'.
      - simpl.
        destruct (Mem.valid_access_store m Mint32 b 0%Z (comp_of f) (Vint (Int.add n Int.one))) as [m' m_m']; try assumption.
        exists m'. split; eauto.
        do 4 take_step.
        now apply star_refl.
      - (* take_steps. *)
        take_step. rewrite Int.eq_true; simpl.
        now apply star_refl.
    Qed.

  Definition switch_add_statement cp s res :=
    (Z.pred (fst res), switch_clause cp (Z.pred (fst res)) s (snd res)).

  Definition switch (cp: compartment) (ss: list statement) (s_else: statement): statement :=
    snd (fold_right (switch_add_statement cp) (Z.of_nat (length ss), s_else) ss).

  Lemma fst_switch (cp: compartment) n (s_else: statement) (ss : list statement) :
    fst (fold_right (switch_add_statement cp) (n, s_else) ss) = (n - Z.of_nat (length ss))%Z.
  Proof.
    induction ss as [|s' ss IH]; try now rewrite Z.sub_0_r.
    simpl; lia.
  Qed.

  Lemma switch_spec_else p (cp: compartment) f Kstop (e: env) le m b (n: Z) ss s_else:
    n >= 0 ->
    cp = comp_of f ->
    e ! (bt_env.(local_counter) cp) = Some (b, type_counter) ->
    Mem.valid_access m Mint32 b 0 Writable (Some cp) ->
    Mem.loadv Mint32 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vint (Int.repr n)) ->
    (Z.of_nat (length ss) <= n)%Z ->
    Star (Clight.semantics1 p)
         (State f (switch cp ss s_else) Kstop e le m)
         E0
         (State f s_else Kstop e le m).
  Proof.
    intros; subst cp. unfold switch.
    assert (G: forall n',
               0 <= n' ->
               n' <= n ->
               Z.of_nat (length ss) <= n ->
               Star (Clight.semantics1 p)
                 (State f (snd (fold_right (switch_add_statement (comp_of f)) (n', s_else) ss)) Kstop e le m)
                 E0
                 (State f s_else Kstop e le m)).
    { clear H4.
      intros n' zero_le_n' n'_le_n' ss_le_n.
      induction ss as [|s ss IH]; try apply star_refl.
      simpl. simpl in ss_le_n. rewrite fst_switch, <- Z.sub_succ_r.
      take_step.
      { rewrite Int.eq_false. reflexivity.
        destruct (Z.eqb_spec n (n' - Z.of_nat (S (length ss)))) as [n_eq_0|?]; simpl.
        - lia.
        - (* I think it's not always true. Might need restricton on [n] fitting in 32 bits? *)
          admit. }
      rewrite Int.eq_true; simpl.
      eapply IH. lia. }
    now apply G; lia.
  Admitted.


  Section WithTrace.

    Variable cp: compartment.
    Variable t: trace.
    (* Hypothesis t_cp: forall e \in t, comp_of e = cp. *)
    (* Hypothesis t_small_enoug: length t <= 2^60. *)

    Definition statement_of_trace: statement :=
      switch (map (statement_of_event cp) t) Sskip.




  End WithTrace.

End Backtranslation.

  (* Axiom backtranslation: Policy.t -> split -> trace -> Csyntax.program * Csyntax.program. *)
  (* Axiom backtranslation_correct: *)
  (*   forall pol s t p C, *)
  (*     backtranslation pol s t = (p, C) -> *)
  (*     c_compatible s p C /\ *)
  (*     exists W, link p C = Some W /\ *)
  (*            c_program_has_initial_trace W t. *)

  (* Axiom backtranslation_compiles: *)
  (*   forall pol s t p C, *)
  (*     backtranslation pol s t = (p, C) -> *)
  (*     exists p_compiled C_compiled, *)
  (*       transf_c_program p = OK p_compiled /\ *)
  (*         transf_c_program C = OK C_compiled. *)

  (* Axiom backtranslation_pol: forall pol s t, *)
  (*     Ctypes.prog_pol (fst (backtranslation pol s t)) = pol /\ *)
  (*     Ctypes.prog_pol (snd (backtranslation pol s t)) = pol. *)
