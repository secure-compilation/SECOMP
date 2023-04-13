Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import Ctypes Clight.

Record backtranslation_environment :=
  { local_counter: compartment -> ident }.

Section Backtranslation.

  Ltac simpl_expr :=
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

  Variable bt_env: backtranslation_environment.

  Section SWITCH.
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

    Ltac simpl_expr' :=
      unfold type_counter; unfold type_bool; simpl; simpl_expr.

    Ltac take_step' := econstructor; [econstructor; simpl_expr' | | traceEq]; simpl.

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
        do 4 take_step'.
        now apply star_refl.
      - (* take_steps. *)
        take_step'. rewrite Int.eq_true; simpl.
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
        take_step'.
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

  End SWITCH.


  Section CODE.
    (** converting trace to code **)

    Definition wf_env (e: env) id := e ! id = None.

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

    Lemma ptr_of_id_ofs_eval
          id ofs e (ge: genv) b cp le m
          (GE1: wf_env e id)
          (GE2: Genv.find_symbol ge id = Some b)
      :
      eval_expr ge e cp le m (ptr_of_id_ofs id ofs) (Vptr b ofs).
    Proof.
      unfold ptr_of_id_ofs. destruct (Archi.ptr64) eqn:ARCH.
      - eapply eval_Ebinop. eapply eval_Eaddrof. eapply eval_Evar_global; eauto.
        simpl_expr.
        simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.of_int64_to_int64; auto.
      - eapply eval_Ebinop. eapply eval_Eaddrof. eapply eval_Evar_global; eauto.
        simpl_expr.
        simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
        erewrite Ptrofs.agree32_of_ints_eq; auto. apply Ptrofs.agree32_to_int; auto.
    Qed.

    Lemma ptr_of_id_ofs_typeof
          i i0
      :
      typeof (ptr_of_id_ofs i i0) = Tpointer Tvoid noattr.
    Proof. unfold ptr_of_id_ofs. destruct Archi.ptr64; simpl; auto. Qed.

    Definition eventval_to_expr (v: eventval): expr :=
      match v with
      | EVint i => Econst_int i (Tint I32 Signed noattr)
      | EVlong i => Econst_long i (Tlong Signed noattr)
      | EVfloat f => Econst_float f (Tfloat F64 noattr)
      | EVsingle f => Econst_single f (Tfloat F32 noattr)
      | EVptr_global id ofs => ptr_of_id_ofs id ofs
      end.

    Definition wf_eventval_env (e: env) (v: eventval): Prop :=
      match v with
      | EVptr_global id _ => wf_env e id
      | _ => True
      end.

    Definition wf_eventval_pub (ge: genv) (v: eventval): Prop :=
      match v with
      | EVptr_global id _ => (Senv.public_symbol ge id = true)
      | _ => True
      end.

    Definition wf_eventval_ge (ge: genv) (v: eventval): Prop :=
      match v with
      | EVptr_global id _ => (exists b, Genv.find_symbol ge id = Some b)
      | _ => True
      end.

    Lemma wf_eventval_pub_ge
          ge v
      :
      wf_eventval_pub ge v -> wf_eventval_ge ge v.
    Proof. intros H. destruct v; simpl in *; auto. apply Genv.public_symbol_exists in H; auto. Qed.

    Lemma eventval_to_expr_match
          ge env cp le m
          ev exp v ty
          (WFENV: wf_eventval_env env ev)
          (WFGE: wf_eventval_pub ge ev)
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
          { rewrite WFENV in H4. inversion H4. }
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
          { rewrite WFENV in H4. inversion H4. }
          { inversion H6.
            rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
            rewrite Ptrofs.add_zero_l.
            replace (Ptrofs.of_ints (Ptrofs.to_int i0)) with i0.
            constructor; auto.
            symmetry. apply Ptrofs.agree32_of_ints_eq; auto.
            apply Ptrofs.agree32_to_int; auto.
          }
    Qed.

    Definition eventval_to_val (ge: genv) (v: eventval): val :=
      match v with
      | EVint i => Vint i
      | EVlong i => Vlong i
      | EVfloat f => Vfloat f
      | EVsingle f => Vsingle f
      | EVptr_global id ofs => match Senv.find_symbol ge id with
                              | Some b => Vptr b ofs
                              | None => Vundef
                              end
      end.

    Fixpoint list_eventval_to_typelist (vs: list eventval): typelist :=
      match vs with
      | nil => Tnil
      | cons v vs' => Tcons (eventval_to_type v) (list_eventval_to_typelist vs')
      end.

    Definition list_eventval_to_list_expr (vs: list eventval): list expr :=
      List.map eventval_to_expr vs.

    Definition list_eventval_to_list_val (ge: genv) (vs: list eventval): list val :=
      List.map (eventval_to_val ge) vs.

    Lemma eventval_to_expr_val_eval
          ge en cp temp m ev
          (WFENV: wf_eventval_env en ev)
          (WFGE: wf_eventval_ge ge ev)
      :
      eval_expr ge en cp temp m (eventval_to_expr ev) (eventval_to_val ge ev).
    Proof.
      destruct ev; simpl in *; try constructor.
      destruct WFGE as [b WFGE].
      rewrite WFGE. unfold ptr_of_id_ofs. destruct Archi.ptr64 eqn:ARCH.
      - econstructor; try econstructor. eapply eval_Evar_global; eauto.
        simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.of_int64_to_int64; auto.
      - econstructor; try econstructor. eapply eval_Evar_global; eauto.
        simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
        erewrite Ptrofs.agree32_of_ints_eq; auto. apply Ptrofs.agree32_to_int; auto.
    Qed.

    Lemma eventval_to_expr_val_match
          ge env
          ev exp v ty
          (WFENV: wf_eventval_env env ev)
          (WFEV: wf_eventval_pub ge ev)
          (CONV0: eventval_to_expr ev = exp)
          (CONV1: eventval_to_val ge ev = v)
          (TYPE: typ_of_type (eventval_to_type ev) = ty)
      :
      eventval_match ge ev ty v.
    Proof.
      subst. eapply eventval_to_expr_match; eauto. eapply eventval_to_expr_val_eval; eauto. apply wf_eventval_pub_ge; auto.
      Unshelve. exact default_compartment. exact (PTree.empty val). exact Mem.empty.
    Qed.

    Lemma typeof_eventval_to_expr_type
          v
      :
      typeof (eventval_to_expr v) = eventval_to_type v.
    Proof. destruct v; simpl; auto. apply ptr_of_id_ofs_typeof. Qed.

    Lemma sem_cast_eventval
          ge v m
          (WFEV: wf_eventval_ge ge v)
      :
      Cop.sem_cast (eventval_to_val ge v) (typeof (eventval_to_expr v)) (eventval_to_type v) m = Some (eventval_to_val ge v).
    Proof. rewrite typeof_eventval_to_expr_type. destruct v; simpl in *; simpl_expr. destruct WFEV. rewrite H. simpl_expr. Qed.

    Lemma list_eventval_to_expr_val_eval
          ge en cp temp m evs
          (WFENV: Forall (wf_eventval_env en) evs)
          (WFGE: Forall (wf_eventval_ge ge) evs)
      :
      eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_eventval_to_typelist evs) (list_eventval_to_list_val ge evs).
    Proof.
      move evs at top. revert ge en cp temp m WFENV WFGE. induction evs; intros; simpl in *.
      constructor.
      inversion WFENV; clear WFENV; subst. inversion WFGE; clear WFGE; subst.
      econstructor; eauto. eapply eventval_to_expr_val_eval; eauto.
      apply sem_cast_eventval; auto.
    Qed.

    Lemma list_eventval_to_expr_val_match
          ge env
          evs exps vs tys
          (WFENV: Forall (wf_eventval_env env) evs)
          (WFPUB: Forall (wf_eventval_pub ge) evs)
          (CONV0: list_eventval_to_list_expr evs = exps)
          (CONV1: list_eventval_to_list_val ge evs = vs)
          (TYPE: list_eventval_to_typelist evs = tys)
      :
      eventval_list_match ge evs (typlist_of_typelist tys) vs.
    Proof.
      move evs at top. revert ge env exps vs tys WFENV WFPUB CONV0 CONV1 TYPE.
      induction evs; intros; simpl in *; subst. constructor.
      inversion WFENV; clear WFENV; subst. inversion WFPUB; clear WFPUB; subst.
      econstructor; eauto. eapply eventval_to_expr_val_match; eauto.
    Qed.


    (* converting functions *)
    Definition code_of_vload (ch: memory_chunk) (id: ident) (ofs: Ptrofs.int) (v: eventval) :=
      Sbuiltin None (EF_vload ch) (Tcons (Tpointer Tvoid noattr) Tnil) (ptr_of_id_ofs id ofs :: nil).

    Definition code_of_vstore (ch: memory_chunk) (id: ident) (ofs: Ptrofs.int) (v: eventval) :=
      Sbuiltin None (EF_vstore ch) (Tcons (Tpointer Tvoid noattr) (Tcons (eventval_to_type v) Tnil)) ((ptr_of_id_ofs id ofs) :: (eventval_to_expr v) :: nil).

    Definition code_of_annot (str: string) (vs: list eventval) :=
      Sbuiltin None (EF_annot
                       (Pos.of_nat (List.length (typlist_of_typelist (list_eventval_to_typelist vs))))
                       str
                       (typlist_of_typelist (list_eventval_to_typelist vs))
                    ) (list_eventval_to_typelist vs)
               (list_eventval_to_list_expr vs).

    Definition code_of_call (cp cp': compartment) (id: ident) (vs: list eventval) :=
      Scall None (Evar id (Tfunction (list_eventval_to_typelist vs) Tvoid cc_default)) (list_eventval_to_list_expr vs).

    (* An [event_syscall] does not need any code, because it is only generated after a call to an external function *)
    Definition code_of_syscall (name: string) (vs: list eventval) (v: eventval) := Sskip.

    Definition code_of_return (cp cp': compartment) (v: eventval) :=
      Sreturn (Some (eventval_to_expr v)).

    Definition code_of_event (e: event): statement :=
      match e with
      | Event_vload ch id ofs v => code_of_vload ch id ofs v
      | Event_vstore ch id ofs v => code_of_vstore ch id ofs v
      | Event_annot str vs => code_of_annot str vs
      | Event_call cp cp' id vs => code_of_call cp cp' id vs
      | Event_syscall name vs v => code_of_syscall name vs v
      | Event_return cp cp' v => code_of_return cp cp' v
      end.

    (* A while(1)-loop with a big switch inside it *)
    Definition code_of_trace cp (t: trace): statement :=
      Swhile (Econst_int Int.one (Tint I32 Signed noattr)) (switch cp (map code_of_event t) (Sreturn None)).


    (* Properties *)
    Lemma code_of_event_step_vload
          ev
          ch id ofs v
          p f k e le m
          (EV: ev = Event_vload ch id ofs v)
          (* bt should ensure them *)
          (WFENV: wf_env e id)
          b
          (VOL: Senv.block_is_volatile (globalenv p) b = true)
          (GE: Genv.find_symbol (globalenv p) id = Some b)
          (* asm should ensure them *)
          rv
          (MATCH: eventval_match (globalenv p) v (type_of_chunk ch) rv)
      :
        Star (Clight.semantics1 p)
             (State f (code_of_event ev) k e le m)
             (ev :: nil)
             (State f Sskip k e le m).
    Proof.
      subst; simpl in *. unfold code_of_vload.
      destruct Archi.ptr64 eqn:ARCH.
      - econstructor 2.
        3:{ rewrite E0_right. reflexivity. }
        { eapply step_builtin.
          { econstructor; eauto. 3: econstructor.
            - eapply ptr_of_id_ofs_eval; eauto.
            - unfold ptr_of_id_ofs; simpl. rewrite ARCH. simpl. simpl_expr.
          }
          repeat econstructor; eauto.
        }
        econstructor 1.
      - econstructor 2.
        3:{ rewrite E0_right. reflexivity. }
        { eapply step_builtin.
          { econstructor; eauto. 3: econstructor.
            - eapply ptr_of_id_ofs_eval; eauto.
            - unfold ptr_of_id_ofs; simpl. rewrite ARCH. simpl. simpl_expr.
          }
          repeat econstructor; eauto.
        }
        econstructor 1.
    Qed.

    Lemma code_of_event_step_vstore
          ev
          ch id ofs v
          p f k e le m
          (EV: ev = Event_vstore ch id ofs v)
          (* bt should ensure them *)
          (WFENV: wf_env e id)
          b
          (VOL: Senv.block_is_volatile (globalenv p) b = true)
          (GE: Genv.find_symbol (globalenv p) id = Some b)
          (* asm should ensure them *)
          (WFSV1: wf_eventval_env e v)
          (WFSV2: wf_eventval_ge (globalenv p) v)
          (MATCH: eventval_match (globalenv p) v (type_of_chunk ch) (Val.load_result ch (eventval_to_val (globalenv p) v)))
      :
        Star (Clight.semantics1 p)
             (State f (code_of_event ev) k e le m)
             (ev :: nil)
             (State f Sskip k e le m).
    Proof.
      subst; simpl in *. unfold code_of_vstore.
      destruct Archi.ptr64 eqn:ARCH.
      - econstructor 2.
        3:{ rewrite E0_right. reflexivity. }
        { eapply step_builtin.
          { econstructor; eauto.
            { eapply ptr_of_id_ofs_eval; eauto. }
            { unfold ptr_of_id_ofs; simpl. rewrite ARCH. simpl. simpl_expr. }
            econstructor; eauto. 3: econstructor.
            { eapply eventval_to_expr_val_eval; auto. }
            { apply sem_cast_eventval; auto. }
          }
          simpl.
          repeat econstructor; eauto.
        }
        econstructor 1.
      - econstructor 2.
        3:{ rewrite E0_right. reflexivity. }
        { eapply step_builtin.
          { econstructor; eauto.
            { eapply ptr_of_id_ofs_eval; eauto. }
            { unfold ptr_of_id_ofs; simpl. rewrite ARCH. simpl. simpl_expr. }
            econstructor; eauto. 3: econstructor.
            { eapply eventval_to_expr_val_eval; auto. }
            { apply sem_cast_eventval; auto. }
          }
          simpl.
          repeat econstructor; eauto.
        }
        econstructor 1.
    Qed.

    Lemma code_of_event_step_annot
          ev
          str vs
          p f k e le m
          (EV: ev = Event_annot str vs)
          (* bt should ensure them *)
          (WFENV: Forall (wf_eventval_env e) vs)
          (WFPUB: Forall (wf_eventval_pub (globalenv p)) vs)
          (* asm should ensure them *)
      :
        Star (Clight.semantics1 p)
             (State f (code_of_event ev) k e le m)
             (ev :: nil)
             (State f Sskip k e le m).
    Proof.
      subst; simpl in *. unfold code_of_annot.
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { eapply step_builtin.
        { eapply list_eventval_to_expr_val_eval; auto.
          eapply Forall_impl. 2: eauto. intros. apply wf_eventval_pub_ge; auto. }
        repeat econstructor; eauto. eapply list_eventval_to_expr_val_match; eauto.
      }
      econstructor 1.
    Qed.

    Lemma code_of_event_step_call_start
          ev
          cp cp' id vs
          p f k e le m
          ge
          (GE: ge = globalenv p)
          (EV: ev = Event_call cp cp' id vs)
          (* bt should ensure them *)
          (GLOB: e ! id = None)
          b
          (FINDB: Genv.find_symbol ge id = Some b)
          fd
          (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
          (TYPEF: type_of_fundef fd = Tfunction (list_eventval_to_typelist vs) Tvoid cc_default)
          (WFARGS1: Forall (wf_eventval_env e) vs)
          (WFARGS2: Forall (wf_eventval_pub ge) vs)
          (* asm should ensure them *)
          (CP1: cp = comp_of f)
          (CP2: cp' = comp_of fd)
          (NPTR: Forall not_ptr (list_eventval_to_list_val ge vs))
          (CROSS: Genv.type_of_call ge (comp_of f) (comp_of fd) = Genv.CrossCompartmentCall)
          (ALLOW: Genv.allowed_cross_call ge (comp_of f) (Vptr b Ptrofs.zero))
      :
        Star (Clight.semantics1 p)
             (State f (code_of_event ev) k e le m)
             (ev :: nil)
             (Callstate fd (list_eventval_to_list_val ge vs) (Kcall None f e le k) m).
    Proof.
      subst; simpl. unfold code_of_call.
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { eapply step_call; simpl; eauto.
        { eapply eval_Elvalue.
          - eapply eval_Evar_global; eauto.
          - eapply deref_loc_reference. auto.
        }
        { eapply list_eventval_to_expr_val_eval; auto.
          eapply Forall_impl. 2: eauto. intros. apply wf_eventval_pub_ge; auto. }
        red; auto.
        unfold Genv.find_comp. setoid_rewrite FINDF.
        eapply call_trace_cross; eauto. apply Genv.find_invert_symbol; auto.
        eapply (list_eventval_to_expr_val_match (globalenv p)); eauto.
      }
      econstructor 1.
    Qed.

    Lemma code_of_event_step_call_internal
          p f k e le m
          ge
          (GE: ge = globalenv p)
          (* bt should ensure them *)
          fd args f1
          (INTERNAL: fd = Internal f1)
          (* asm should ensure them *)
          (* handle during proving *)
          e1 le1 m1
          (ENTRY: function_entry1 ge f1 args m e1 le1 m1)
      :
        Star (Clight.semantics1 p)
             (Callstate fd args (Kcall None f e le k) m)
             nil
             (State f1 (fn_body f1) (Kcall None f e le k) e1 le1 m1).
    Proof.
      subst; simpl.
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { eapply step_internal_function; eauto. }
      econstructor 1.
    Qed.

    Lemma code_of_event_step_call_external
          p m
          ge
          (GE: ge = globalenv p)
          (* bt should ensure them *)
          fd k args ef targs tres cconv
          (EXTERNAL: fd = External ef targs tres cconv)
          (* asm should ensure them *)
          sev
          vres m1
          (SEM: external_call ef ge (call_comp k) args m (sev :: nil) vres m1)
          (* handle during proving *)
          sname sargs svr
          (SYSEV: sev = Event_syscall sname sargs svr)
      :
        Star (Clight.semantics1 p)
             (Callstate fd args k m)
             (sev :: nil)
             (Returnstate vres k m1 (rettype_of_type tres) (comp_of ef)).
    Proof.
      subst; simpl.
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { eapply step_external_function; eauto. }
      econstructor 1.
    Qed.

    Lemma code_of_event_step_return
          ev
          cp cp' rv
          p f k e le m
          ge
          (GE: ge = globalenv p)
          (EV: ev = Event_return cp' cp rv)
          (* bt should ensure them *)
          (WFRV1: wf_eventval_env e rv)
          (WFRV2: wf_eventval_pub ge rv)
          (RTTYP: fn_return f = eventval_to_type rv)
          (* asm should ensure them *)
          optid f' e' le' k'
          (CONT: call_cont k = Kcall optid f' e' le' k')
          (CP1: cp = comp_of f)
          (CP2: cp' = comp_of f')
          (NPTR: not_ptr (eventval_to_val ge rv))
          (CROSS: Genv.type_of_call ge (comp_of f') (comp_of f) = Genv.CrossCompartmentCall)
          (* handle during proving *)
          m'
          (FREE: Mem.free_list m (blocks_of_env ge e) (comp_of f) = Some m')
      :
      Star (Clight.semantics1 p)
           (State f (code_of_event ev) k e le m)
           (ev :: nil)
           (State f' Sskip k' e' (set_opttemp optid (eventval_to_val ge rv) le') m').
    Proof.
      subst; simpl. unfold code_of_return.
      econstructor 2.
      3:{ rewrite E0_left. reflexivity. }
      { eapply step_return_1; simpl; eauto.
        { eapply eventval_to_expr_val_eval; auto. apply wf_eventval_pub_ge; auto. }
        { rewrite RTTYP. eapply sem_cast_eventval; auto. eapply wf_eventval_pub_ge; eauto. }
      }
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { rewrite CONT. eapply step_returnstate; auto.
        econstructor 2; auto. rewrite RTTYP. eapply eventval_to_expr_val_match; eauto.
        clear. destruct rv; simpl; auto.
      }
      econstructor 1.
    Qed.

  End CODE.


  Section PROJ.
    (** Projection of the trace according to compartments **)

    Definition comp_of_event (e: event): option (compartment * compartment) :=
      match e with
      | Event_call cp cp' id vs => Some (cp, cp')
      | Event_return cp' cp v => Some (cp, cp')
      | _ => None
      end.

    (* Instance has_comp_event: has_comp event := *)

    Definition comp_proj_trace (cp: compartment) (t: trace): compartment * trace :=
      fold_right
        (fun ev '(cp_now, sub) => match comp_of_event ev with
                               | Some (cp_curr, cp_next) => (cp_next, if (Pos.eqb cp_curr cp) then (ev :: sub) else sub)
                               | None => (cp_now, if (Pos.eqb cp_now cp) then (ev :: sub) else sub)
                               end)
        (default_compartment, nil) t.

    Definition comp_subtrace (cp: compartment) (t: trace) :=
      snd (comp_proj_trace cp t).

    Definition code_of_subtrace cp t :=
      code_of_trace cp (comp_subtrace cp t).

    Definition codes_of_subtraces (cps: list compartment) t : PTree.t statement :=
      PTree_Properties.of_list (map (fun cp => (cp, code_of_subtrace cp t)) cps).

    Definition get_cps_from_policy (p: Policy.t): list compartment :=
      map fst (PTree.elements p.(Policy.policy_export)).

  End PROJ.


  Section WELLFORMED.

    Variable p: program.
    Let ge := globalenv p.

    (** Well-formed conditions for the trace, namely from the semantics of Asm **)
    Definition wf_trace_vload ch v :=
      exists rv, eventval_match (globalenv p) v (type_of_chunk ch) rv.


    (** Well-formed conditions for the back-translated program **)
    Definition wf_bt_vload (e: env) id :=
      (wf_env e id) /\
        (exists b, (Genv.find_symbol ge id = Some b) /\ (Senv.block_is_volatile ge b = true)).
      

    Lemma code_of_event_step_vload
          ev
          ch id ofs v
          p f k e le m
          (EV: ev = Event_vload ch id ofs v)
          (* bt should ensure them *)
          (WFENV: wf_env e id)
          b
          (VOL: Senv.block_is_volatile (globalenv p) b = true)
          (GE: Genv.find_symbol (globalenv p) id = Some b)
          (* asm should ensure them *)
          rv
          (MATCH: eventval_match (globalenv p) v (type_of_chunk ch) rv)
      :
        Star (Clight.semantics1 p)
             (State f (code_of_event ev) k e le m)
             (ev :: nil)
             (State f Sskip k e le m).
    Proof.
      subst; simpl in *. unfold code_of_vload.
      destruct Archi.ptr64 eqn:ARCH.
      - econstructor 2.
        3:{ rewrite E0_right. reflexivity. }
        { eapply step_builtin.
          { econstructor; eauto. 3: econstructor.
            - eapply ptr_of_id_ofs_eval; eauto.
            - unfold ptr_of_id_ofs; simpl. rewrite ARCH. simpl. simpl_expr.
          }
          repeat econstructor; eauto.
        }
        econstructor 1.
      - econstructor 2.
        3:{ rewrite E0_right. reflexivity. }
        { eapply step_builtin.
          { econstructor; eauto. 3: econstructor.
            - eapply ptr_of_id_ofs_eval; eauto.
            - unfold ptr_of_id_ofs; simpl. rewrite ARCH. simpl. simpl_expr.
          }
          repeat econstructor; eauto.
        }
        econstructor 1.
    Qed.

    Lemma code_of_event_step_vstore
          ev
          ch id ofs v
          p f k e le m
          (EV: ev = Event_vstore ch id ofs v)
          (* bt should ensure them *)
          (WFENV: wf_env e id)
          b
          (VOL: Senv.block_is_volatile (globalenv p) b = true)
          (GE: Genv.find_symbol (globalenv p) id = Some b)
          (* asm should ensure them *)
          (WFSV1: wf_eventval_env e v)
          (WFSV2: wf_eventval_ge (globalenv p) v)
          (MATCH: eventval_match (globalenv p) v (type_of_chunk ch) (Val.load_result ch (eventval_to_val (globalenv p) v)))
      :
        Star (Clight.semantics1 p)
             (State f (code_of_event ev) k e le m)
             (ev :: nil)
             (State f Sskip k e le m).
    Proof.
      subst; simpl in *. unfold code_of_vstore.
      destruct Archi.ptr64 eqn:ARCH.
      - econstructor 2.
        3:{ rewrite E0_right. reflexivity. }
        { eapply step_builtin.
          { econstructor; eauto.
            { eapply ptr_of_id_ofs_eval; eauto. }
            { unfold ptr_of_id_ofs; simpl. rewrite ARCH. simpl. simpl_expr. }
            econstructor; eauto. 3: econstructor.
            { eapply eventval_to_expr_val_eval; auto. }
            { apply sem_cast_eventval; auto. }
          }
          simpl.
          repeat econstructor; eauto.
        }
        econstructor 1.
      - econstructor 2.
        3:{ rewrite E0_right. reflexivity. }
        { eapply step_builtin.
          { econstructor; eauto.
            { eapply ptr_of_id_ofs_eval; eauto. }
            { unfold ptr_of_id_ofs; simpl. rewrite ARCH. simpl. simpl_expr. }
            econstructor; eauto. 3: econstructor.
            { eapply eventval_to_expr_val_eval; auto. }
            { apply sem_cast_eventval; auto. }
          }
          simpl.
          repeat econstructor; eauto.
        }
        econstructor 1.
    Qed.

    Lemma code_of_event_step_annot
          ev
          str vs
          p f k e le m
          (EV: ev = Event_annot str vs)
          (* bt should ensure them *)
          (WFENV: Forall (wf_eventval_env e) vs)
          (WFPUB: Forall (wf_eventval_pub (globalenv p)) vs)
          (* asm should ensure them *)
      :
        Star (Clight.semantics1 p)
             (State f (code_of_event ev) k e le m)
             (ev :: nil)
             (State f Sskip k e le m).
    Proof.
      subst; simpl in *. unfold code_of_annot.
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { eapply step_builtin.
        { eapply list_eventval_to_expr_val_eval; auto.
          eapply Forall_impl. 2: eauto. intros. apply wf_eventval_pub_ge; auto. }
        repeat econstructor; eauto. eapply list_eventval_to_expr_val_match; eauto.
      }
      econstructor 1.
    Qed.

    Lemma code_of_event_step_call_start
          ev
          cp cp' id vs
          p f k e le m
          ge
          (GE: ge = globalenv p)
          (EV: ev = Event_call cp cp' id vs)
          (* bt should ensure them *)
          (GLOB: e ! id = None)
          b
          (FINDB: Genv.find_symbol ge id = Some b)
          fd
          (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
          (TYPEF: type_of_fundef fd = Tfunction (list_eventval_to_typelist vs) Tvoid cc_default)
          (WFARGS1: Forall (wf_eventval_env e) vs)
          (WFARGS2: Forall (wf_eventval_pub ge) vs)
          (* asm should ensure them *)
          (CP1: cp = comp_of f)
          (CP2: cp' = comp_of fd)
          (NPTR: Forall not_ptr (list_eventval_to_list_val ge vs))
          (CROSS: Genv.type_of_call ge (comp_of f) (comp_of fd) = Genv.CrossCompartmentCall)
          (ALLOW: Genv.allowed_cross_call ge (comp_of f) (Vptr b Ptrofs.zero))
      :
        Star (Clight.semantics1 p)
             (State f (code_of_event ev) k e le m)
             (ev :: nil)
             (Callstate fd (list_eventval_to_list_val ge vs) (Kcall None f e le k) m).
    Proof.
      subst; simpl. unfold code_of_call.
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { eapply step_call; simpl; eauto.
        { eapply eval_Elvalue.
          - eapply eval_Evar_global; eauto.
          - eapply deref_loc_reference. auto.
        }
        { eapply list_eventval_to_expr_val_eval; auto.
          eapply Forall_impl. 2: eauto. intros. apply wf_eventval_pub_ge; auto. }
        red; auto.
        unfold Genv.find_comp. setoid_rewrite FINDF.
        eapply call_trace_cross; eauto. apply Genv.find_invert_symbol; auto.
        eapply (list_eventval_to_expr_val_match (globalenv p)); eauto.
      }
      econstructor 1.
    Qed.

    Lemma code_of_event_step_call_internal
          p f k e le m
          ge
          (GE: ge = globalenv p)
          (* bt should ensure them *)
          fd args f1
          (INTERNAL: fd = Internal f1)
          (* asm should ensure them *)
          (* handle during proving *)
          e1 le1 m1
          (ENTRY: function_entry1 ge f1 args m e1 le1 m1)
      :
        Star (Clight.semantics1 p)
             (Callstate fd args (Kcall None f e le k) m)
             nil
             (State f1 (fn_body f1) (Kcall None f e le k) e1 le1 m1).
    Proof.
      subst; simpl.
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { eapply step_internal_function; eauto. }
      econstructor 1.
    Qed.

    Lemma code_of_event_step_call_external
          p m
          ge
          (GE: ge = globalenv p)
          (* bt should ensure them *)
          fd k args ef targs tres cconv
          (EXTERNAL: fd = External ef targs tres cconv)
          (* asm should ensure them *)
          sev
          vres m1
          (SEM: external_call ef ge (call_comp k) args m (sev :: nil) vres m1)
          (* handle during proving *)
          sname sargs svr
          (SYSEV: sev = Event_syscall sname sargs svr)
      :
        Star (Clight.semantics1 p)
             (Callstate fd args k m)
             (sev :: nil)
             (Returnstate vres k m1 (rettype_of_type tres) (comp_of ef)).
    Proof.
      subst; simpl.
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { eapply step_external_function; eauto. }
      econstructor 1.
    Qed.

    Lemma code_of_event_step_return
          ev
          cp cp' rv
          p f k e le m
          ge
          (GE: ge = globalenv p)
          (EV: ev = Event_return cp' cp rv)
          (* bt should ensure them *)
          (WFRV1: wf_eventval_env e rv)
          (WFRV2: wf_eventval_pub ge rv)
          (RTTYP: fn_return f = eventval_to_type rv)
          (* asm should ensure them *)
          optid f' e' le' k'
          (CONT: call_cont k = Kcall optid f' e' le' k')
          (CP1: cp = comp_of f)
          (CP2: cp' = comp_of f')
          (NPTR: not_ptr (eventval_to_val ge rv))
          (CROSS: Genv.type_of_call ge (comp_of f') (comp_of f) = Genv.CrossCompartmentCall)
          (* handle during proving *)
          m'
          (FREE: Mem.free_list m (blocks_of_env ge e) (comp_of f) = Some m')
      :
      Star (Clight.semantics1 p)
           (State f (code_of_event ev) k e le m)
           (ev :: nil)
           (State f' Sskip k' e' (set_opttemp optid (eventval_to_val ge rv) le') m').
    Proof.
      subst; simpl. unfold code_of_return.
      econstructor 2.
      3:{ rewrite E0_left. reflexivity. }
      { eapply step_return_1; simpl; eauto.
        { eapply eventval_to_expr_val_eval; auto. apply wf_eventval_pub_ge; auto. }
        { rewrite RTTYP. eapply sem_cast_eventval; auto. eapply wf_eventval_pub_ge; eauto. }
      }
      econstructor 2.
      3:{ rewrite E0_right. reflexivity. }
      { rewrite CONT. eapply step_returnstate; auto.
        econstructor 2; auto. rewrite RTTYP. eapply eventval_to_expr_val_match; eauto.
        clear. destruct rv; simpl; auto.
      }
      econstructor 1.
    Qed.

  End WELLFORMED.


  (* TODO *)
  (* Axiom backtranslation: Policy.t -> split -> trace -> Clight.program * Clight.program. *)
  (* Axiom backtranslation_correct: *)
  (*   forall pol s t p C, *)
  (*     backtranslation pol s t = (p, C) -> *)
  (*     clight_compatible s p C /\ *)
  (*     exists W, link p C = Some W /\ *)
  (*            clight_program_has_initial_trace W t. *)

  (* Definition clight_has_side (s: split) (lr: side) (p: Clight.program) := *)
  (*   List.Forall (fun '(id, gd) => *)
  (*                  match gd with *)
  (*                  | Gfun (Ctypes.Internal f) => s (comp_of f) = lr *)
  (*                  | _ => True *)
  (*                  end) *)
  (*               (Ctypes.prog_defs p). *)

  (* Definition clight_compatible (s: split) (p p': Clight.program) := *)
  (*   clight_has_side s Left p /\ clight_has_side s Right p'. *)

  (* Definition clight_program_has_initial_trace (p: Clight.program) (t: trace): Prop := *)
  (*   forall beh, program_behaves (Clight.semantics1 p) beh -> behavior_prefix t beh. *)

  (* Axiom backtranslation_pol: forall pol s t, *)
  (*     Ctypes.prog_pol (fst (backtranslation pol s t)) = pol /\ *)
  (*     Ctypes.prog_pol (snd (backtranslation pol s t)) = pol. *)

  (* Clight.program = Ctypes.program Clight.function *)

  (* old CCS version *)
  Lemma comp_subtrace_app (C: Component.id) (t1 t2: trace) :
    comp_subtrace C (t1 ++ t2) = comp_subtrace C t1 ++ comp_subtrace C t2.
  Proof. apply: filter_cat. Qed.

  Definition procedure_of_trace C P t :=
    expr_of_trace C P (comp_subtrace C t).

  Definition procedures_of_trace (t: trace) : NMap (NMap expr) :=
    mapim (fun C Ciface =>
             let procs :=
                 if C == Component.main then
                   Procedure.main |: Component.export Ciface
                 else Component.export Ciface in
               mkfmapf (fun P => procedure_of_trace C P t) procs)
          intf.

  Definition valid_procedure C P :=
    C = Component.main /\ P = Procedure.main
    \/ exported_procedure intf C P.

  Lemma find_procedures_of_trace_exp (t: trace) C P :
    exported_procedure intf C P ->
    find_procedure (procedures_of_trace t) C P
    = Some (procedure_of_trace C P t).
  Proof.
    intros [CI [C_CI CI_P]].
    unfold find_procedure, procedures_of_trace.
    rewrite mapimE C_CI /= mkfmapfE.
    case: eqP=> _; last by rewrite CI_P.
    by rewrite in_fsetU1 CI_P orbT.
  Qed.

  Lemma find_procedures_of_trace_main (t: trace) :
    find_procedure (procedures_of_trace t) Component.main Procedure.main
    = Some (procedure_of_trace Component.main Procedure.main t).
  Proof.
    rewrite /find_procedure /procedures_of_trace.
    rewrite mapimE eqxx.
    case: (intf Component.main) (has_main)=> [Cint|] //= _.
    by rewrite mkfmapfE in_fsetU1 eqxx.
  Qed.

  Lemma find_procedures_of_trace (t: trace) C P :
    valid_procedure C P ->
    find_procedure (procedures_of_trace t) C P
    = Some (procedure_of_trace C P t).
  Proof.
    by move=> [[-> ->]|?];
    [apply: find_procedures_of_trace_main|apply: find_procedures_of_trace_exp].
  Qed.

  Definition program_of_trace (t: trace) : program :=
    {| prog_interface  := intf;
       prog_procedures := procedures_of_trace t;
       prog_buffers    := mapm (fun _ => inr [Int 0]) intf |}.

  (* old CCS version *)
  

  Section WithTrace.

    Variable cp: compartment.
    Variable t: trace.
    (* Hypothesis t_cp: forall e \in t, comp_of e = cp. *)
    (* Hypothesis t_small_enoug: length t <= 2^60. *)

    Definition statement_of_trace: statement :=
      switch (map (statement_of_event cp) t) Sskip.




  End WithTrace.

End Backtranslation.

  (* Axiom backtranslation: Policy.t -> split -> trace -> Clight.program * Clight.program. *)
  (* Axiom backtranslation_correct: *)
  (*   forall pol s t p C, *)
  (*     backtranslation pol s t = (p, C) -> *)
  (*     clight_compatible s p C /\ *)
  (*     exists W, link p C = Some W /\ *)
  (*            clight_program_has_initial_trace W t. *)

  (* Axiom backtranslation_compiles: *)
  (*   forall pol s t p C, *)
  (*     backtranslation pol s t = (p, C) -> *)
  (*     exists p_compiled C_compiled, *)
  (*       transf_clight_program p = OK p_compiled /\ *)
  (*         transf_clight_program C = OK C_compiled. *)

  (* Axiom backtranslation_pol: forall pol s t, *)
  (*     Ctypes.prog_pol (fst (backtranslation pol s t)) = pol /\ *)
  (*     Ctypes.prog_pol (snd (backtranslation pol s t)) = pol. *)
