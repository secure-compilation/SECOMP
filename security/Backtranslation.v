Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import Ctypes Clight.

Record backtranslation_environment :=
  { local_counter: compartment -> ident }.

Section Backtranslation.

  Variable bt_env: backtranslation_environment.

  (** switch statement; use to convert a trace to a code **)

  Definition type_counter: type := Tlong Unsigned noattr.
  Definition type_bool:    type := Tint IBool Signed noattr.

  Definition switch_clause (cp: compartment) (n: Z) (s_then s_else: statement): statement :=
    let one := Econst_long Int64.one type_counter in
    Sifthenelse (Ebinop Cop.Oeq
                        (Evar (bt_env.(local_counter) cp) type_counter)
                        (Econst_long (Int64.repr n) type_counter)
                        type_bool)
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

  Lemma switch_clause_spec p (cp: compartment) f (e: env) le m b (n: int64) (n': Z) s_then s_else:
    cp = comp_of f ->
    e ! (bt_env.(local_counter) cp) = Some (b, type_counter) ->
    Mem.valid_access m Mint64 b 0 Writable (Some cp) ->
    Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong n) ->
    if Int64.eq n (Int64.repr n') then
      exists m',
        Mem.storev Mint64 m (Vptr b Ptrofs.zero) (Vlong (Int64.add n Int64.one)) cp = Some m' /\
          Star (Clight.semantics1 p) (State f (switch_clause cp n' s_then s_else) Kstop e le m) E0 (State f s_then Kstop e le m')
    else
      Star (Clight.semantics1 p) (State f (switch_clause cp n' s_then s_else) Kstop e le m) E0 (State f s_else Kstop e le m).
  Proof.
    intros; subst cp.
    destruct (Int64.eq n (Int64.repr n')) eqn:eq_n_n'.
    - simpl.
      destruct (Mem.valid_access_store m Mint64 b 0%Z (comp_of f) (Vlong (Int64.add n Int64.one))) as [m' m_m']; try assumption.
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

  Lemma switch_spec_else
        p (cp: compartment) f (e: env) le m b (n: Z) ss s_else
        (WF: Z.of_nat (length ss) < Int64.modulus)
        (RANGE: Z.of_nat (length ss) <= n < Int64.modulus)
    :
    cp = comp_of f ->
    e ! (bt_env.(local_counter) cp) = Some (b, type_counter) ->
    (* Mem.valid_access m Mint64 b 0 Writable (Some cp) -> *)
    Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (Int64.repr n)) ->
    Star (Clight.semantics1 p)
         (State f (switch cp ss s_else) Kstop e le m)
         E0
         (State f s_else Kstop e le m).
  Proof.
    intros; subst cp. unfold switch. destruct RANGE as [RA1 RA2].
    assert (G: forall n',
               (Z.of_nat (length ss)) <= n' ->
               n' <= n ->
               Star (Clight.semantics1 p)
                 (State f (snd (fold_right (switch_add_statement (comp_of f)) (n', s_else) ss)) Kstop e le m)
                 E0
                 (State f s_else Kstop e le m)).
    { intros n' LE1 LE2.
      induction ss as [|s ss IH]; try apply star_refl.
      simpl. simpl in RA1, LE1. rewrite fst_switch, <- Z.sub_succ_r.
      take_step.
      { rewrite Int64.eq_false. reflexivity. clear - WF RA1 RA2 LE1 LE2.
        destruct (Z.eqb_spec n (n' - Z.of_nat (S (length ss)))) as [n_eq_0|?]; simpl.
        - lia.
        - intros EQ. apply n0; clear n0.
          rewrite <- (Int64.unsigned_repr n).
          rewrite EQ. rewrite Int64.unsigned_repr. lia.
          1: split.
          all: unfold Int64.max_unsigned; try lia.
      }
      rewrite Int.eq_true; simpl.
      eapply IH; lia.
    }
    now apply G; lia.
  Qed.

  Let nat64 n := Int64.repr (Z.of_nat n).

  Lemma switch_spec
        p (cp: compartment) f (e: env) le m b
        ss s ss' s_else
        (WF: Z.of_nat (length (ss ++ s :: ss')) < Int64.modulus)
    :
    cp = comp_of f ->
    e ! (bt_env.(local_counter) cp) = Some (b, type_counter) ->
    Mem.valid_access m Mint64 b 0 Writable (Some cp) ->
    Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (nat64 (length ss))) ->
    exists m',
      Mem.storev Mint64 m (Vptr b Ptrofs.zero) (Vlong (Int64.add (nat64 (length ss)) Int64.one)) cp = Some m' /\
        Star (Clight.semantics1 p)
             (State f (switch cp (ss ++ s :: ss') s_else) Kstop e le m)
             E0
             (State f s Kstop e le m').
  Proof.
    intros.
    assert (Eswitch :
             exists s_else',
               switch cp (ss ++ s :: ss') s_else =
                 switch cp ss (switch_clause cp (Z.of_nat (length ss)) s s_else')).
    { unfold switch. rewrite fold_right_app, app_length. simpl.
      exists (snd (fold_right (switch_add_statement cp) (Z.of_nat (length ss + S (length ss')), s_else) ss')).
      repeat f_equal. rewrite -> surjective_pairing at 1. simpl.
      rewrite fst_switch, Nat.add_succ_r.
      assert (A: Z.pred (Z.of_nat (S (Datatypes.length ss + Datatypes.length ss')) - Z.of_nat (Datatypes.length ss')) = Z.of_nat (Datatypes.length ss)) by lia.
      rewrite A. reflexivity.
    }
    destruct Eswitch as [s_else' ->]. clear s_else. rename s_else' into s_else.
    exploit (switch_clause_spec p cp f e le m b (nat64 (length ss)) (Z.of_nat (length ss)) s s_else); auto.
    unfold nat64. rewrite Int64.eq_true. intro Hcont.
    destruct Hcont as (m' & Hstore & Hstar2).
    exists m'. split; trivial.
    apply (fun H => @star_trans _ _ _ _ _ E0 _ H E0 _ _ Hstar2); trivial.
    assert (WF2: Z.of_nat (Datatypes.length ss) < Int64.modulus).
    { clear - WF. rewrite app_length in WF. lia. }
    eapply switch_spec_else; eauto. split; auto. reflexivity.
  Qed.

  (** converting trace to code **)

  Definition eventval_to_type (v: eventval): type :=
    match v with
    | EVint _ => Tint I32 Signed noattr
    | EVlong _ => Tlong Signed noattr
    | EVfloat _ => Tfloat F64 noattr
    | EVsingle _ => Tfloat F32 noattr
    | EVptr_global id _ => Tpointer Tvoid noattr
    end.

  Definition ptr_of_id_ofs (id: ident) (ofs: ptrofs): expr :=
    if Archi.ptr64
    then
      Ebinop Cop.Oadd
             (Eaddrof (Evar id Tvoid) (Tpointer Tvoid noattr))
             (Econst_long (Ptrofs.to_int64 ofs) (Tlong Signed noattr))
             (Tpointer Tvoid noattr)
    else
      Ebinop Cop.Oadd
             (Eaddrof (Evar id Tvoid) (Tpointer Tvoid noattr))
             (Econst_int (Ptrofs.to_int ofs) (Tint I32 Signed noattr))
             (Tpointer Tvoid noattr).

  Definition eventval_to_expr (v: eventval): expr :=
    match v with
    | EVint i => Econst_int i (Tint I32 Signed noattr)
    | EVlong i => Econst_long i (Tlong Signed noattr)
    | EVfloat f => Econst_float f (Tfloat F64 noattr)
    | EVsingle f => Econst_single f (Tfloat F32 noattr)
    | EVptr_global id ofs => ptr_of_id_ofs id ofs
    end.

  Definition wf_eventval (ge: genv) (v: eventval): Prop :=
    match v with
    | EVptr_global id _ => (Senv.public_symbol ge id = true)
    | _ => True
    end.

  Lemma eventval_to_expr_inv
        ge env cp le m
        ev exp v ty
        (WFEV: wf_eventval ge ev)
        (CONV: eventval_to_expr ev = exp)
        (EVAL: eval_expr ge env cp le m exp v)
        (TYPE: typ_of_type (eventval_to_type ev) = ty)
    :
    eventval_match ge ev ty v.
  Proof.
    subst. destruct ev; simpl in *.
    - inversion EVAL; subst; simpl in *; try constructor. inversion H.
    - inversion EVAL; subst; simpl in *; try constructor. inversion H.
    - inversion EVAL; subst; simpl in *; try constructor. inversion H.
    - inversion EVAL; subst; simpl in *; try constructor. inversion H.
    - unfold ptr_of_id_ofs in EVAL. destruct Archi.ptr64 eqn:ARCH.
      + inversion EVAL; subst; simpl in *; try constructor.
        2:{ inversion H. }
        inversion H5; subst; simpl in *.
        2:{ inversion H. }
        clear H5. inversion H4; subst; simpl in *.
        2:{ inversion H. }
        clear H4. inversion H2; subst; simpl.
        { admit. }
        { inversion H6.
          rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
          rewrite Ptrofs.add_zero_l.
          replace (Ptrofs.of_int64 (Ptrofs.to_int64 i0)) with i0.
          constructor; auto.
          symmetry. apply Ptrofs.of_int64_to_int64. auto.
        }
      + inversion EVAL; subst; simpl in *; try constructor.
        2:{ inversion H. }
        inversion H5; subst; simpl in *.
        2:{ inversion H. }
        clear H5. inversion H4; subst; simpl in *.
        2:{ inversion H. }
        clear H4. inversion H2; subst; simpl.
        { admit. }
        { inversion H6.
          rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
          rewrite Ptrofs.add_zero_l.
          replace (Ptrofs.of_ints (Ptrofs.to_int i0)) with i0.
          constructor; auto.
          symmetry. apply Ptrofs.agree32_of_ints_eq; auto.
          apply Ptrofs.agree32_to_int; auto.
        }
  Qed.

  (* | step_call : forall (f : function) (optid : option ident) (a : expr) (al : list expr) (k : cont) (e : env) (le : temp_env) (m : mem) (tyargs : typelist) (tyres : type) (cconv : calling_convention) *)
  (*                 (vf : val) (vargs : list val) (fd : fundef) (t : trace), *)
  (*     Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres cconv -> *)
  (*     eval_expr ge e (comp_of f) le m a vf -> *)
  (*     eval_exprlist ge e (comp_of f) le m al tyargs vargs -> *)
  (*     Genv.find_funct ge vf = Some fd -> *)
  (*     type_of_fundef fd = Tfunction tyargs tyres cconv -> *)
  (*     Genv.allowed_call ge (comp_of f) vf -> *)
  (*     (Genv.type_of_call ge (comp_of f) (Genv.find_comp ge vf) = Genv.CrossCompartmentCall -> Forall not_ptr vargs) -> *)
  (*     call_trace ge (comp_of f) (Genv.find_comp ge vf) vf vargs (typlist_of_typelist tyargs) t -> *)
  (*     step ge function_entry (State f (Scall optid a al) k e le m) t (Callstate fd vargs (Kcall optid f e le k) m) *)


  Fixpoint list_eventval_to_typelist (vs: list eventval): typelist :=
    match vs with
    | nil => Tnil
    | cons v vs' => Tcons (eventval_to_type v) (list_eventval_to_typelist vs')
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
