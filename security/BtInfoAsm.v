Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import riscV.Machregs.
Require Import riscV.Asm.
Require Import Complements.

Require Import Tactics.
Require Import MemoryWeak MemoryDelta.
Require Import BtBasics.



Section AUX.

  Lemma val_load_result_idem chunk v:
    Val.load_result chunk (Val.load_result chunk v) = Val.load_result chunk v.
  Proof.
    destruct chunk, v; ss.
    all: try (rewrite Int.sign_ext_idem; auto; lia).
    all: try (rewrite Int.zero_ext_idem; auto; lia).
    all: des_ifs.
  Qed.

  Lemma extcall_cases
        ef ge m args
        (ECC: external_call_conds ef ge m args)
        tr rv m'
        (ECALL: external_call ef ge args m tr rv m')
    :
    (external_call_unknowns ef ge m args) \/
      (external_call_known_observables ef ge m args tr rv m') \/
      (external_call_known_silents ef ge m args tr rv m').
  Proof.
    destruct ef; ss; auto. des_ifs; auto. des_ifs; auto.
    - destruct tr; ss; eauto. right; left. esplits; eauto. ss.
    - destruct tr; ss; eauto. right; left. esplits; eauto. ss.
    - inv ECALL. right; right. esplits; eauto. econs; eauto.
    - inv ECALL. right; right. esplits; eauto. econs; eauto.
      right; right. esplits; eauto. econs; eauto.
    - inv ECALL. right; right. esplits; eauto. econs; eauto.
    - destruct tr; ss; eauto. right; left. esplits; eauto. ss.
    - destruct tr; ss; eauto. right; left. esplits; eauto. ss.
    - inv ECALL. right; right. esplits; eauto. econs; eauto.
  Qed.

End AUX.



Section BUNDLE.

  Variant bundle_event : Type :=
    (* generate a call code + other followup events; call-ext-ret *)
    | Bundle_call (tr: trace) (id: ident) (args: list eventval) (sg: signature)
                  (d: option mem_delta)
    (* generate a return code; ret *)
    | Bundle_return (tr: trace) (retv: eventval)
    (* generate a builtin code; ext *)
    | Bundle_builtin (tr: trace) (ef: external_function) (args: list eventval)
                     (d: mem_delta)
  .

  Definition bundle_trace := list bundle_event.

  Definition unbundle (be: bundle_event): trace :=
    match be with
    | Bundle_call tr _ _ _ _ | Bundle_return tr _ | Bundle_builtin tr _ _ _ => tr
    end.

  Fixpoint unbundle_trace (btr: bundle_trace) : trace :=
    match btr with
    | be :: tl => (unbundle be) ++ (unbundle_trace tl)
    | nil => nil
    end.

  Lemma unbundle_trace_cons
        be btr
    :
    unbundle_trace (be :: btr) = (unbundle be) ++ (unbundle_trace btr).
  Proof. simpl. auto. Qed.

  Lemma unbundle_trace_app
        btr1 btr2
    :
    unbundle_trace (btr1 ++ btr2) = (unbundle_trace btr1) ++ (unbundle_trace btr2).
  Proof.
    revert btr2. induction btr1; intros.
    { simpl. auto. }
    rewrite <- app_comm_cons. rewrite ! unbundle_trace_cons. rewrite <- app_assoc. f_equal.
    eauto.
  Qed.

  Inductive istar {genv state : Type} (step : genv -> state -> bundle_event -> state -> Prop) (ge : genv) : state -> bundle_trace -> state -> Prop :=
    istar_refl : forall s : state, istar step ge s nil s
  | istar_step : forall (s1 : state) (ev : bundle_event) (s2 : state) (t2 : bundle_trace) (s3 : state) (t : bundle_trace),
      step ge s1 ev s2 -> istar step ge s2 t2 s3 -> t = ev :: t2 -> istar step ge s1 t s3.

  Lemma istar_trans
        genv state (step: genv -> state -> bundle_event -> state -> Prop) ge
        s1 t1 s2
        (ISTAR1: istar step ge s1 t1 s2)
        t2 s3
        (ISTAR2: istar step ge s2 t2 s3)
        t
        (TR: t = t1 ++ t2)
    :
    istar step ge s1 t s3.
  Proof.
    revert_until ISTAR1. induction ISTAR1; intros.
    { simpl in *. subst; auto. }
    subst. rewrite <- app_comm_cons. econstructor 2. eapply H.
    { eapply IHISTAR1. eapply ISTAR2. eauto. }
    auto.
  Qed.

End BUNDLE.


Section EVENT.

  Definition typ_to_eventval (ty: typ): eventval :=
    match ty with
    | Tint => EVint Int.zero
    | Tfloat => EVfloat Floats.Float.zero
    | Tlong => EVlong Int64.zero
    | Tsingle => EVsingle Floats.Float32.zero
    | Tany32 => EVint Int.zero
    | Tany64 => EVlong Int64.zero
    end.

  Definition typ_to_eventvals (ty: list typ): list eventval := map typ_to_eventval ty.

  Inductive call_trace_cross {F V : Type} (ge : Genv.t F V) : compartment -> compartment -> block -> list val -> list typ -> trace -> ident -> list eventval -> Prop :=
  | call_trace_cross_cross : forall (cp cp' : compartment) (b : block) (vargs : list val) (vl : list eventval) (ty : list typ) (i : ident) tr,
      Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall ->
      Genv.invert_symbol ge b = Some i -> eventval_list_match ge vl ty vargs ->
      (tr = Event_call cp cp' i vl :: nil) ->
      call_trace_cross ge cp cp' b vargs ty tr i vl.

  Inductive return_trace_cross {F V : Type} (ge : Genv.t F V) : compartment -> compartment -> val -> rettype -> trace -> eventval -> Prop :=
  | return_trace_cross_cross : forall (cp cp' : compartment) (res : eventval) (v : val) (ty : rettype) tr,
      Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall -> eventval_match ge res (proj_rettype ty) v ->
      (tr = Event_return cp cp' res :: nil) ->
      return_trace_cross ge cp cp' v ty tr res.

  (* external call *)
  Definition senv_invert_symbol_total (ge: Senv.t) (b: block) : ident :=
    match Senv.invert_symbol ge b with
    | Some id => id
    | _ => xH
    end.

  Definition val_to_eventval (ge: Senv.t) (v: val): eventval :=
    match v with
    | Vundef => EVint Int.zero
    | Vint n => EVint n
    | Vlong n => EVlong n
    | Vfloat n => EVfloat n
    | Vsingle n => EVsingle n
    | Vptr b o => let id := senv_invert_symbol_total ge b in EVptr_global id o
    end.

  Definition vals_to_eventvals (ge: Senv.t) (vs: list val): list eventval := map (val_to_eventval ge) vs.

  Lemma eventval_match_val_to_eventval
        ge ev ty v
        (EVM: eventval_match ge ev ty v)
    :
    val_to_eventval ge v = ev.
  Proof.
    inv EVM; simpl; auto.
    unfold senv_invert_symbol_total. erewrite Senv.find_invert_symbol; eauto.
  Qed.

  Lemma eventval_list_match_vals_to_eventvals
        ge evs tys vs
        (EVM: eventval_list_match ge evs tys vs)
    :
    vals_to_eventvals ge vs = evs.
  Proof.
    induction EVM; simpl; auto.
    rewrite IHEVM. f_equal. eapply eventval_match_val_to_eventval; eauto.
  Qed.

End EVENT.



Section IR.

  Variant ir_cont_type : Type := | ir_cont: block -> ir_cont_type.
  Definition ir_conts := list ir_cont_type.

  Definition crossing_comp {F V} (ge: Genv.t F V) (cp cp': compartment) :=
    Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall.

  Definition ir_state := option (block * mem * ir_conts)%type.

  Variant ir_step (ge: Asm.genv) : ir_state -> bundle_event -> ir_state -> Prop :=
    | ir_step_cross_call_internal
        cur m1 ik
        tr id evargs sg
        cp cp' vargs
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        b f_next
        (FINDB: Genv.find_symbol ge id = Some b)
        (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (AST.Internal f_next))
        (CP': cp' = comp_of f_next)
        (ALLOW: Genv.allowed_call ge cp (Vptr b Ptrofs.zero))
        (NPTR: crossing_comp ge cp cp' -> Forall not_ptr vargs)
        (SIG: sg = Asm.fn_sig f_next)
        (TR: call_trace_cross ge cp cp' b vargs (sig_args sg) tr id evargs)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_call tr id evargs sg None) (Some (b, m1, (ir_cont cur) :: ik))
    | ir_step_cross_return_internal
        cur m1 next ik ik_tl
        tr evretv
        cp_cur cp_next vretv
        (CURCP: cp_cur = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        sg fd_cur
        (FINDFD: Genv.find_funct_ptr ge cur = Some (fd_cur))
        (* in Asm, stack has the sig *)
        (SIG: sg = Asm.funsig fd_cur)
        (NPTR: crossing_comp ge cp_next cp_cur -> not_ptr vretv)
        (NEXTCP: cp_next = Genv.find_comp ge (Vptr next Ptrofs.zero))
        f_next
        (INTERNAL: Genv.find_funct_ptr ge next = Some (AST.Internal f_next))
        (* internal return: memory changes in Clight-side, so need inj-relation *)
        (TR: return_trace_cross ge cp_next cp_cur vretv (sig_res sg) tr evretv)
        (CONT: ik = (ir_cont next) :: ik_tl)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_return tr evretv) (Some (next, m1, ik_tl))
    | ir_step_intra_call_external
        cur m1 m2 ik
        tr id evargs sg
        cp_cur
        (CURCP: cp_cur = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        b_ext ef cp_ext
        (FINDB: Genv.find_symbol ge id = Some b_ext)
        (FINDF: Genv.find_funct ge (Vptr b_ext Ptrofs.zero) = Some (AST.External ef))
        (EXTCP: cp_ext = comp_of ef)
        (INTRA: Genv.type_of_call ge cp_cur cp_ext = Genv.InternalCall)
        (SIG: sg = ef_sig ef)
        d m1'
        (MEM: mem_delta_apply_inj (meminj_public ge) d (Some m1) = Some m1')
        vargs vretv
        (EC: external_call ef ge vargs m1' tr vretv m2)
        (ECCASES: (external_call_unknowns ef ge m1' vargs) \/
                    (external_call_known_observables ef ge m1' vargs tr vretv m2))
        (ARGS: evargs = vals_to_eventvals ge vargs)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_call tr id evargs sg (Some d)) (Some (cur, m2, ik))
    | ir_step_builtin
        cur m1 m2 ik
        tr ef evargs
        cp_cur
        (CURCP: cp_cur = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        d m1'
        (MEM: mem_delta_apply_inj (meminj_public ge) d (Some m1) = Some m1')
        vargs vretv
        (EC: external_call ef ge vargs m1' tr vretv m2)
        (ECCASES: (external_call_unknowns ef ge m1' vargs) \/
                    (external_call_known_observables ef ge m1' vargs tr vretv m2))
        (ARGS: evargs = vals_to_eventvals ge vargs)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_builtin tr ef evargs d) (Some (cur, m2, ik))
    | ir_step_cross_call_external1
        (* early cut at call *)
        cur m1 ik
        tr id evargs sg
        cp cp' vargs
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        b ef
        (FINDB: Genv.find_symbol ge id = Some b)
        (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (AST.External ef))
        (CP': cp' = comp_of ef)
        (ALLOW: Genv.allowed_call ge cp (Vptr b Ptrofs.zero))
        (NPTR: crossing_comp ge cp cp' -> Forall not_ptr vargs)
        (SIG: sg = ef_sig ef)
        (TR: call_trace_cross ge cp cp' b vargs (sig_args sg) tr id evargs)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_call tr id evargs sg None) None
    | ir_step_cross_call_external2
        (* early cut at call-ext_call *)
        cur m1 ik
        tr1 id evargs sg
        cp cp' vargs
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        b ef
        (FINDB: Genv.find_symbol ge id = Some b)
        (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (AST.External ef))
        (CP': cp' = comp_of ef)
        (ALLOW: Genv.allowed_call ge cp (Vptr b Ptrofs.zero))
        (NPTR: crossing_comp ge cp cp' -> Forall not_ptr vargs)
        (SIG: sg = ef_sig ef)
        (TR1: call_trace_cross ge cp cp' b vargs (sig_args sg) tr1 id evargs)
        (* external function part *)
        d m1'
        (MEM: mem_delta_apply_inj (meminj_public ge) d (Some m1) = Some m1')
        tr2 m2 vretv
        (TR2: external_call ef ge vargs m1' tr2 vretv m2)
        (ECCASES: (external_call_unknowns ef ge m1' vargs) \/
                    (external_call_known_observables ef ge m1' vargs tr2 vretv m2))
        (ARGS: evargs = vals_to_eventvals ge vargs)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_call (tr1 ++ tr2) id evargs sg (Some d)) None
    | ir_step_cross_call_external3
        (* early cut at call-ext_call *)
        cur m1 ik
        tr1 id evargs sg
        cp cp' vargs
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        b ef
        (FINDB: Genv.find_symbol ge id = Some b)
        (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (AST.External ef))
        (CP': cp' = comp_of ef)
        (ALLOW: Genv.allowed_call ge cp (Vptr b Ptrofs.zero))
        (NPTR: crossing_comp ge cp cp' -> Forall not_ptr vargs)
        (SIG: sg = ef_sig ef)
        (TR1: call_trace_cross ge cp cp' b vargs (sig_args sg) tr1 id evargs)
        (* external function part *)
        d m1'
        (MEM: mem_delta_apply_inj (meminj_public ge) d (Some m1) = Some m1')
        tr2 m2 vretv
        (TR2: external_call ef ge vargs m1' tr2 vretv m2)
        (ECCASES: (external_call_unknowns ef ge m1' vargs) \/
                    (external_call_known_observables ef ge m1' vargs tr2 vretv m2))
        (ARGS: evargs = vals_to_eventvals ge vargs)
        (* return part *)
        tr3 evretv
        (NPTR: crossing_comp ge cp cp' -> not_ptr vretv)
        f_cur
        (INTERNAL: Genv.find_funct_ptr ge cur = Some (AST.Internal f_cur))
        (TR3: return_trace_cross ge cp cp' vretv (sig_res sg) tr3 evretv)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_call (tr1 ++ tr2 ++ tr3) id evargs sg (Some d)) (Some (cur, m2, ik)).

End IR.


Section AUX.

  Definition wf_ge {F V} (ge: Genv.t F V) := exists (p: AST.program F V), (list_norepet (prog_defs_names p)) /\ (ge = Genv.globalenv p).

  Lemma wf_ge_block_to_id
        F V (ge: Genv.t F V)
        (WF: wf_ge ge)
        b gd
        (DEF: Genv.find_def ge b = Some gd)
    :
    exists id, Genv.invert_symbol ge b = Some id.
  Proof. destruct WF as (p & A & B). eapply genv_def_to_ident; eauto. Qed.

  Lemma val_is_ptr_or_not
        (v: val)
    :
    (forall b o, v <> Vptr b o) \/ (exists b o, v = Vptr b o).
  Proof. destruct v; eauto. all: left; intros; intros F; inv F. Qed.

End AUX.


Section MEASURE.

  Inductive star_measure {genv state : Type} (step : genv -> state -> trace -> state -> Prop) (ge : genv) : nat -> state -> trace -> state -> Prop :=
    star_measure_refl : forall s : state, star_measure step ge O s E0 s
  | star_step : forall n (s1 : state) (t1 : trace) (s2 : state) (t2 : trace) (s3 : state) (t : trace),
      step ge s1 t1 s2 -> star_measure step ge n s2 t2 s3 -> t = t1 ** t2 -> star_measure step ge (S n) s1 t s3.

  Lemma measure_star
        genv state
        (step : genv -> state -> trace -> state -> Prop)
        (ge : genv)
        s0 tr s1
        (STAR: star step ge s0 tr s1)
    :
    exists n, star_measure step ge n s0 tr s1.
  Proof.
    induction STAR.
    { exists O. constructor 1. }
    destruct IHSTAR as (n & NEXT). exists (S n). econstructor 2. eapply H. eapply NEXT. auto.
  Qed.

End MEASURE.


Section FROMASM.

  Import ListNotations.

  Ltac Simplif_all :=
    ((rewrite Asmgenproof0.nextinstr_inv in * by eauto with asmgen)
     || (rewrite Asmgenproof0.nextinstr_inv1 in * by eauto with asmgen)
     || (rewrite Pregmap.gss in *)
     || (rewrite Asmgenproof0.nextinstr_pc in *)
     || (rewrite Pregmap.gso in * by eauto with asmgen)); auto with asmgen.

  Ltac Simpl_all := repeat Simplif_all.

  Ltac simpl_before_exists :=
    repeat (Simpl_all;
            match goal with
            (* Goto *)
            | _: goto_label _ _ ?rs _ = Next _ _ |- _ =>
                unfold goto_label in *; destruct label_pos; try congruence
            | _: eval_branch _ _ ?rs _ _ = Next _ _ |- _ =>
                unfold eval_branch in *; simpl in *
            | _: exec_load _ _ _ _ _ _ _ _ _ = Next _ _ |- _ =>
                unfold exec_load in *; simpl in *
            | _: exec_store _ _ _ _ _ _ _ _ = Next _ _ |- _ =>
                unfold exec_store in *; simpl in *
            | _: context [Val.cmp_bool] |- _ =>
                unfold Val.cmp_bool in *; simpl in *
            | _: context [Val.cmpl_bool] |- _ =>
                unfold Val.cmpl_bool in *; simpl in *
            | _: context [eval_offset _ ?ofs] |- _ =>
                destruct ofs; simpl in *

            | |- context [Ptrofs.repr 0] => replace (Ptrofs.repr 0) with Ptrofs.zero by reflexivity; auto
            | H: context [Ptrofs.repr 0] |- _ => replace (Ptrofs.repr 0) with Ptrofs.zero in H by reflexivity; auto
            | |- context [Ptrofs.add _ Ptrofs.zero] => rewrite Ptrofs.add_zero; auto
            | H: context [Ptrofs.add _ Ptrofs.zero] |- _ => rewrite Ptrofs.add_zero in H; simpl in *; try congruence
            | |- context [Ptrofs.sub _ Ptrofs.zero] => rewrite Ptrofs.sub_zero_l; auto
            | H: context [Ptrofs.sub _ Ptrofs.zero] |- _ => rewrite Ptrofs.sub_zero_l in H; simpl in *; try congruence

            (* hypothesis manipulation *)
            | _: context [match ?rs1 ?i with | _ => _ end] |- _ =>
                destruct (rs1 i) eqn:?; try congruence; simpl in *; eauto

            | _: context [Val.offset_ptr (?rs1 ?i) _] |- _ =>
                destruct (rs1 i) eqn:?; try congruence; simpl in *; eauto

            | H: Next _ _ = Next _ _ |- _ => inv H
            | H: Some _ = Some _ |- _ => inv H
            | H: Some _ = None |- _ => inv H
            | H: None = Some _ |- _ => inv H
            | H: Stuck = Next _ _ |- _ => inv H
            | H: Next _ _ = Stuck |- _ => inv H
            | H: negb _ = true |- _ => apply negb_true_iff in H
            | H: negb _ = false |- _ => apply negb_false_iff in H
            | H: Int.eq ?x ?x = false |- _ => rewrite Int.eq_true in H
            | H: Int64.eq ?x ?x = false |- _ => rewrite Int64.eq_true in H
            | H: false = true |- _ => congruence
            | H: true = false |- _ => congruence
            | H: ?x = false, H': ?x = true |- _ => congruence
            | H: match ?x with | _ => _ end = Next _ _ |- _ =>
                let eq := fresh "eq" in
                destruct x eqn:eq; simpl in *; try congruence
            | _: context [?rs1 ### ?rs] |- context [?rs3 ### ?rs] =>
                let i := fresh "i" in destruct rs as [| i]; simpl in *
            | _: context [?rs1 ## ?rs] |- context [?rs3 ## ?rs] =>
                let i := fresh "i" in destruct rs as [| i]; simpl in *
            | H: ?x = _ |- context [if ?x then _ else _] =>
                rewrite H; simpl
            | H: ?x = _ |- context [match ?x with | _ => _ end] =>
                rewrite H; simpl
            | |- context [(if ?x then _ else _) = Next _ _] =>
                let eq := fresh "eq" in destruct x eqn:eq; simpl in *
            | |- context [(match ?x with | _ => _ end) = Next _ _] =>
                let eq := fresh "eq" in destruct x eqn:eq; simpl in *

            end);
    simpl.

  Definition public_not_freeable ge m := forall b, (meminj_public ge b <> None) -> (forall ofs, ~ Mem.perm m b ofs Max Freeable).

  Lemma public_not_freeable_free_inj_none
        ge m
        (NFREE: public_not_freeable ge m)
        b lo hi cp m'
        (FREE: Mem.free m b lo hi cp = Some m')
        (BOUND: (lo < hi)%Z)
    :
    meminj_public ge b = None.
  Proof.
    destruct (meminj_public ge b) eqn:INJPUB; auto. exfalso.
    eapply Mem.free_range_perm in FREE. unfold Mem.range_perm in FREE.
    eapply NFREE. erewrite INJPUB. congruence. eapply Mem.perm_cur_max; apply FREE.
    instantiate (1:=lo). lia.
  Qed.

  Lemma mem_delta_exec_instr
        (ge: genv) f i rs m cp rs' m'
        (NFREE: public_not_freeable ge m)
        (EXEC: exec_instr ge f i rs m cp = Next rs' m')
        m0 d
        (DELTA0: mem_delta_inj_wf (meminj_public ge) d)
        (DELTA1: mem_delta_apply d (Some m0) = Some m)
    :
    exists d', (mem_delta_inj_wf (meminj_public ge) d') /\ (mem_delta_apply d' (Some m0) = Some m').
  Proof.
    destruct i; simpl in EXEC.
    all: try (inv EXEC; eauto).
    all: simpl_before_exists; eauto.
    all: try
           (match goal with
            | H: context [Mem.alloc] |- _ => idtac
            | H: context [Mem.free] |- _ => idtac
            | H: Mem.store ?ch ?m ?b ?ofs ?v ?cp = _ |-  _ =>
                exists (d ++ [mem_delta_kind_store (ch, b, ofs, v, cp)]); split
            end;
            [apply Forall_app; split; [auto | constructor; simpl; auto]
            | rewrite mem_delta_apply_app; (match goal with | H: mem_delta_apply _ _ = Some _ |- _ => rewrite H end; simpl; auto) ]).
    { match goal with
      | _: Mem.alloc _ ?cp1 ?lo ?hi = _, _: Mem.store ?ch _ ?b ?ofs ?v ?cp2 = _ |- _ =>
          exists (d ++ ([mem_delta_kind_alloc (cp1, lo, hi)] ++ [mem_delta_kind_store (ch, b, ofs, v, cp2)]))
      end.
      split.
      - apply Forall_app; split; auto. apply Forall_app; split; constructor; simpl; auto.
      - rewrite mem_delta_apply_app. rewrite DELTA1. rewrite mem_delta_apply_app. simpl. rewrite Heqp. simpl. auto.
    }
    { destruct (Z.leb_spec sz 0); cycle 1.
      { match goal with
        | _: Mem.free _ ?b ?lo ?hi ?cp = _ |- _ =>
            exists (d ++ [mem_delta_kind_free (b, lo, hi, cp)])
        end.
        split.
        - apply Forall_app; split; auto. constructor; auto. simpl. destruct (meminj_public ge b) eqn:INJPUB; auto. exfalso.
          eapply Mem.free_range_perm in Heqo0. unfold Mem.range_perm in Heqo0. eapply NFREE. erewrite INJPUB. congruence. eapply Mem.perm_cur_max; apply Heqo0. instantiate (1:=0%Z). lia.
        - rewrite mem_delta_apply_app. rewrite DELTA1. simpl. auto.
      }
      { apply Mem.free_result in Heqo0. unfold Mem.unchecked_free in Heqo0. unfold zle in Heqo0. des_ifs. eexists; eauto. }
    }
  Qed.

  Lemma public_not_freeable_store
        ge m1
        (NFREE: public_not_freeable ge m1)
        chunk b ofs v cp m2
        (STORE: Mem.store chunk m1 b ofs v cp = Some m2)
    :
    public_not_freeable ge m2.
  Proof.
    unfold public_not_freeable in *; intros b' H' ofs' CC; specialize (NFREE _ H' ofs').
    apply NFREE; eapply Mem.perm_store_2; eauto.
  Qed.

  Lemma public_not_freeable_bytes
        ge m1
        (NFREE: public_not_freeable ge m1)
        b ofs mvs cp m2
        (STORE: Mem.storebytes m1 b ofs mvs cp = Some m2)
    :
    public_not_freeable ge m2.
  Proof.
    unfold public_not_freeable in *; intros b' H' ofs' CC; specialize (NFREE _ H' ofs').
    apply NFREE; eapply Mem.perm_storebytes_2; eauto.
  Qed.

  Lemma public_not_freeable_alloc
        ge m1
        (NALLOC: meminj_not_alloc (meminj_public ge) m1)
        (NFREE: public_not_freeable ge m1)
        cp lo hi m2 bn
        (STORE: Mem.alloc m1 cp lo hi = (m2, bn))
    :
    public_not_freeable ge m2.
  Proof.
    unfold public_not_freeable in *; intros b' H' ofs' CC; specialize (NFREE _ H' ofs').
    apply NFREE. eapply Mem.perm_alloc_4; eauto.
    intros EQ; subst b'. apply H'. apply NALLOC. erewrite Mem.alloc_result; eauto. lia.
  Qed.

  Lemma public_not_freeable_free
        ge m1
        (NFREE: public_not_freeable ge m1)
        b lo hi cp m2
        (STORE: Mem.free m1 b lo hi cp = Some m2)
    :
    public_not_freeable ge m2.
  Proof.
    unfold public_not_freeable in *; intros b' H' ofs' CC; specialize (NFREE _ H' ofs').
    apply NFREE. eapply Mem.perm_free_3; eauto.
  Qed.

  Lemma public_not_freeable_exec_instr
        (ge: genv) f i rs m cp rs' m'
        (NFREE: public_not_freeable ge m)
        (NALLOC: meminj_not_alloc (meminj_public ge) m)
        (EXEC: exec_instr ge f i rs m cp = Next rs' m')
    :
    public_not_freeable ge m'.
  Proof.
    destruct i; simpl in EXEC.
    all: try (inv EXEC; eauto).
    all: simpl_before_exists; eauto.
    all: try
           (match goal with
            | H: context [Mem.alloc] |- _ => idtac
            | H: context [Mem.free] |- _ => idtac
            | H: Mem.store ?ch ?m ?b ?ofs ?v ?cp = _ |-  _ =>
                eapply public_not_freeable_store; eauto
            end).
    { eapply public_not_freeable_store. eapply public_not_freeable_alloc; eauto. eauto. }
    { eapply public_not_freeable_free; eauto. }
  Qed.

  Lemma meminj_not_alloc_delta
        j m0
        (NALLOC: meminj_not_alloc j m0)
        d m1
        (APPD: mem_delta_apply d (Some m0) = Some m1)
    :
    meminj_not_alloc j m1.
  Proof.
    revert m0 NALLOC m1 APPD. induction d; intros.
    { simpl in *. inv APPD. auto. }
    rewrite mem_delta_apply_cons in APPD. destruct a.
    - destruct d0 as ((((ch & b) & ofs) & v) & cp). simpl in *. exploit mem_delta_apply_some. eapply APPD. intros (mi & MEM). rewrite MEM in APPD. eapply IHd. 2: eapply APPD.
      unfold meminj_not_alloc in *. intros. eapply NALLOC. erewrite Mem.nextblock_store in H; eauto.
    - destruct d0 as (((b & ofs) & mvs) & cp). simpl in *. exploit mem_delta_apply_some. eapply APPD. intros (mi & MEM). rewrite MEM in APPD. eapply IHd. 2: eapply APPD.
      unfold meminj_not_alloc in *. intros. eapply NALLOC. erewrite Mem.nextblock_storebytes in H; eauto.
    - destruct d0 as ((cp & lo) & hi). simpl in *. exploit mem_delta_apply_some. eapply APPD. intros (mi & MEM). rewrite MEM in APPD. eapply IHd. 2: eapply APPD.
      unfold meminj_not_alloc in *. intros. eapply NALLOC. destruct (Mem.alloc m0 cp lo hi) eqn:MA. simpl in *. inv MEM. erewrite Mem.nextblock_alloc in H; eauto. lia.
    - destruct d0 as (((b & lo) & hi) & cp). simpl in *. exploit mem_delta_apply_some. eapply APPD. intros (mi & MEM). rewrite MEM in APPD. eapply IHd. 2: eapply APPD.
      unfold meminj_not_alloc in *. intros. eapply NALLOC. erewrite Mem.nextblock_free in H; eauto.
  Qed.

  Lemma exec_instr_is_return
        ge f i rs m cp rs' m'
        (EXEC: exec_instr ge f i rs m cp = Next rs' m')
        (ISRET: is_return i = true)
    :
    (exists v, rs' = (rs # PC <- v)) /\ (m' = m).
  Proof. destruct i; simpl in *; clarify. split; eauto. Qed.

  Lemma exec_instr_is_call
        ge f i rs m cp rs' m'
        (EXEC: exec_instr ge f i rs m cp = Next rs' m')
        sig
        (ISRET: sig_call i = Some sig)
    :
    (rs' X1 = Val.offset_ptr rs#PC Ptrofs.one) /\ (m' = m).
  Proof. destruct i; simpl in *; clarify. Qed.

End FROMASM.


Section INVS.

  Import ListNotations.

  Definition wf_stackframe (ge: Asm.genv) (fr: stackframe) :=
    match fr with
    | Stackframe b _ _ _ _ => match Genv.find_funct_ptr ge b with
                             | Some (Internal f) => True
                             | _ => False
                             end
    end.
  Definition wf_stack (ge: Asm.genv) (sk: stack) := Forall (wf_stackframe ge) sk.

  Definition wf_regset (ge: Asm.genv) (rs: regset) :=
    match rs PC with
    | Vptr b _ => match Genv.find_funct_ptr ge b with
                 | Some (Internal f) => True
                 | _ => False
                 end
    | _ => False
    end.

  Definition wf_asm (ge: Asm.genv) (ast: Asm.state) :=
    match ast with
    | State sk rs m => (wf_stack ge sk) /\ (wf_regset ge rs)
    | _ => False
    end.


  Definition wf_ir_cur (ge: Asm.genv) (cur: block) :=
    match Genv.find_funct_ptr ge cur with
    | Some (Internal f) => True
    | _ => False
    end.

  Definition wf_ir_cont (ge: Asm.genv) (ik: ir_cont_type) :=
    match ik with
    | ir_cont b => match Genv.find_funct_ptr ge b with
                  | Some (Internal f) => True
                  | _ => False
                  end
    end.
  Definition wf_ir_conts (ge: Asm.genv) (ik: ir_conts) := Forall (wf_ir_cont ge) ik.


  Definition match_cur_stack_sig (cur: block) (ge: Asm.genv) (sk: stack) :=
    match Genv.find_funct_ptr ge cur with
    | Some fd => Asm.funsig fd = sig_of_call sk
    | _ => False
    end.

  Definition match_cur_regset (cur: block) (ge: Asm.genv) (rs: regset) :=
    Genv.find_comp ge (Vptr cur Ptrofs.zero) = Genv.find_comp_ignore_offset ge (rs PC).

  Inductive match_stack (ge: Asm.genv): ir_conts -> stack -> Prop :=
  | match_stack_nil
    :
    match_stack ge [] []
  | match_stack_cons
      next ik_tl
      b cp sg v ofs sk_tl
      (COMP: Genv.find_comp ge (Vptr next Ptrofs.zero) = Genv.find_comp ge (Vptr b Ptrofs.zero))
      (SIG: match_cur_stack_sig next ge sk_tl)
      (TL: match_stack ge ik_tl sk_tl)
    :
    match_stack ge (ir_cont next :: ik_tl) (Stackframe b cp sg v ofs :: sk_tl).

  Definition match_mem (ge: Senv.t) (k: meminj) (d: mem_delta) (m_a0 m_i m_a1: mem): Prop :=
    let j := meminj_public ge in
    (Mem.inject k m_a0 m_i) /\ (inject_incr j k) /\
      (meminj_not_alloc j m_a0) /\ (public_not_freeable ge m_a1) /\
      (mem_delta_inj_wf j d) /\ (mem_delta_apply d (Some m_a0) = Some m_a1).

  Definition match_state (ge: Asm.genv) (k: meminj) (m_a0: mem) (d: mem_delta) (ast: Asm.state) (ist: ir_state): Prop :=
    match ast, ist with
    | State sk rs m_a, Some (cur, m_i, ik) =>
        (wf_ir_cur ge cur) /\ (wf_ir_conts ge ik) /\
          (match_cur_stack_sig cur ge sk) /\ (match_cur_regset cur ge rs) /\
          (match_stack ge ik sk) /\ (match_mem ge k d m_a0 m_i m_a)
    | _, _ => False
    end.

End INVS.


Section PROOF.

  Import ListNotations.

  Ltac end_case := do 2 eexists; split; [|constructor 1]; auto.


  Lemma asm_step_current_pc
        cpm ge st rs m t s'
        (STEP: step_fix cpm ge (State st rs m) t s')
    :
    exists b ofs, rs PC = Vptr b ofs.
  Proof. destruct (rs PC) eqn:NEXTPC. 1,2,3,4,5: inv STEP; rewrite NEXTPC in H2; inv H2. eauto. Qed.

  Lemma asm_step_some_fundef
        cpm ge st rs m t s'
        (STEP: step_fix cpm ge (State st rs m) t s')
        b ofs
        (NEXTPC: rs PC = Vptr b ofs)
    :
    exists fd, Genv.find_funct_ptr ge b = Some fd.
  Proof. destruct (Genv.find_funct_ptr ge b) eqn:CASE; eauto. exfalso. inv STEP; rewrite NEXTPC in H2; inv H2; rewrite CASE in H3; inv H3. Qed.

  Lemma asm_to_ir_compose
        ge ist0 t t1 t2
        (ISTARS: exists btr1 ist1,
            (unbundle_trace btr1 = t1 /\ istar ir_step ge ist0 btr1 ist1)
            /\ exists btr2 ist2,
              (unbundle_trace btr2 = t2 /\ istar ir_step ge ist1 btr2 ist2))
        (TR: t = t1 ** t2)
    :
    exists (btr : bundle_trace) (ist' : ir_state),
      unbundle_trace btr = t /\ istar ir_step ge ist0 btr ist'.
  Proof.
    subst. destruct ISTARS as (btr1 & ist1 & (UTR1 & ISTAR1) & btr2 & ist2 & (UTR2 & ISTAR2)).
    exists (btr1 ++ btr2). exists ist2. split; auto.
    { rewrite unbundle_trace_app. rewrite UTR1, UTR2. auto. }
    { eapply istar_trans; eauto. }
  Qed.


  Lemma visible_fo_meminj_fo
        (ge: Senv.t) m tys args
        (VFO: visible_fo ge m tys args)
    :
    meminj_first_order (meminj_public ge) m.
  Proof.
    destruct VFO as [PFO _]. ii. unfold public_first_order in PFO. unfold meminj_public in H. des_ifs.
    exploit PFO; eauto. apply Senv.invert_find_symbol. auto.
  Qed.

  Lemma external_call_unknowns_fo
        ef (ge: Senv.t) m args
        (ECC: external_call_unknowns ef ge m args)
    :
    meminj_first_order (meminj_public ge) m.
  Proof.
    unfold external_call_unknowns in ECC. des_ifs; eapply visible_fo_meminj_fo; eauto.
  Qed.

  Lemma symbols_inject_meminj_public
        F V (ge: Genv.t F V)
    :
    symbols_inject (meminj_public ge) ge ge.
  Proof.
    unfold symbols_inject. splits; intros; unfold meminj_public in *; auto.
    - des_ifs.
    - erewrite Senv.find_invert_symbol; eauto. rewrite H. eauto.
    - des_ifs.
  Qed.

  Lemma visible_fo_val_inject_list
        (ge: Senv.t) m tys args
        (VFO: visible_fo ge m tys args)
    :
    Val.inject_list (meminj_public ge) args args.
  Proof.
    destruct VFO as [PFO VP]. induction VP; ss. econs; eauto. clear dependent l. clear dependent l'. inv H; auto.
    destruct H0 as [id [INV PUB]].
    econs. unfold meminj_public. rewrite INV. rewrite PUB. eauto. rewrite Ptrofs.add_zero. auto.
  Qed.

  Lemma external_call_unknowns_val_inject_list
        ef (ge: Senv.t) m args
        (ECC: external_call_unknowns ef ge m args)
    :
    Val.inject_list (meminj_public ge) args args.
  Proof.
    unfold external_call_unknowns in ECC. des_ifs; eapply visible_fo_val_inject_list; eauto.
  Qed.

(*   Lemma visible_fo_mem_inj *)
(*         (ge: Senv.t) m tys args *)
(*         (VFO: visible_fo ge m tys args) *)
(*         m' *)
(*         (MEMINJ: Mem.inject (meminj_public ge) m m') *)
(*     : *)
(*     visible_fo ge m' tys args. *)
(*   Proof. *)
(*     destruct VFO as [PFO VP]. split; auto. clear VP. clear - PFO MEMINJ. *)
(*     unfold public_first_order in *. intros. exploit PFO; clear PFO; eauto. *)
(*     { instantiate (1:=ofs). *)
(* Mem.perm_inject_inv: *)
(*   forall (f : meminj) (m1 m2 : mem) (b1 : block) (ofs : Z) (b2 : block) (delta : Z) (k : perm_kind) (p : permission), *)
(*   Mem.inject f m1 m2 -> f b1 = Some (b2, delta) -> Mem.perm m2 b2 (ofs + delta) k p -> Mem.perm m1 b1 ofs k p \/ ~ Mem.perm m1 b1 ofs Max Nonempty *)

(*   Lemma external_call_unknowns_mem_inj *)
(*         (ge: Senv.t) m ef args *)
(*         (ECC: external_call_unknowns ef ge m args) *)
(*         m' *)
(*         (MEMINJ: Mem.inject (meminj_public ge) m m') *)
(*     : *)
(*     external_call_unknowns ef ge m' args. *)
(*   Proof. *)
(*     unfold external_call_unknowns in *. des_ifs. *)

  Lemma match_mem_external_call_establish1
        (ge: genv) k d m_a0 m_i m
        (MEM: match_mem ge k d m_a0 m_i m)
        ef args t res m'
        (EXTCALL: external_call ef ge args m t res m')
        (ECC: external_call_unknowns ef ge m args)
    :
    exists m1 m2 res',
      (mem_delta_apply_inj (meminj_public ge) d (Some m_i) = Some m1) /\
        (external_call ef ge args m1 t res' m2) /\
        (external_call_unknowns ef ge m1 args) /\
        (exists k2, match_mem ge k2 [] m' m2 m' /\ Val.inject k2 res res')
  .
  Proof.
    destruct MEM as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    (* reestablish meminj *)
    exploit mem_delta_apply_establish_inject; eauto.
    { apply meminj_public_strict. }
    { eapply external_call_unknowns_fo. eauto. }
    intros (m_i' & APPD' & MEMINJ').
    hexploit ec_mem_inject. eapply external_call_spec. 2: eapply EXTCALL. all: eauto.
    (* hexploit external_call_mem_inject. 2: eapply EXTCALL. all: eauto. *)
    { instantiate (1:=ge). apply symbols_inject_meminj_public. }
    { instantiate (1:=args). eapply external_call_unknowns_val_inject_list; eauto. }
    intros (f' & vres' & m_i'' & EXTCALL' & VALINJ' & MEMINJ'' & _ & _ & INCRINJ' & _).
    assert (MM': match_mem ge f' [] m' m_i'' m').
    { unfold match_mem. simpl. splits; auto.
      { pose proof (meminj_not_alloc_delta _ _ MEM2 _ _ MEM5) as NALLOC.
        clear - EXTCALL NALLOC. unfold meminj_not_alloc in *. intros. apply NALLOC.
        pose proof (@external_call_valid_block _ _ _ _ _ _ _ b EXTCALL).
        destruct (Pos.leb_spec (Mem.nextblock m) b); auto.
        unfold Mem.valid_block in H0. apply H0 in H1. exfalso. unfold Plt in H1. lia.
      }
      { pose proof (meminj_not_alloc_delta _ _ MEM2 _ _ MEM5) as NALLOC.
        clear - EXTCALL MEM3 NALLOC. unfold public_not_freeable in *. intros.
        specialize (MEM3 _ H). intros CC. apply (MEM3 ofs); clear MEM3.
        eapply external_call_max_perm; eauto. unfold Mem.valid_block.
        unfold meminj_not_alloc in NALLOC. unfold Plt.
        destruct (Pos.ltb_spec b (Mem.nextblock m)); auto.
        specialize (NALLOC _ H0). congruence.
      }
      constructor.
    }
    exists m_i', m_i'', vres'. splits; eauto.
    { clear - ECC MEMINJ'. admit.

Mem.perm_drop_1:
  forall (m : mem) (b : block) (lo hi : Z) (p : permission) (cp : compartment) (m' : mem),
  Mem.drop_perm m b lo hi p cp = Some m' -> forall (ofs : Z) (k : perm_kind), (lo <= ofs < hi)%Z -> Mem.perm m' b ofs k p

Genv.alloc_global = 
fun (F V : Type) (CF : has_comp F) (ge : Genv.t F V) (m : mem) (idg : ident * globdef F V) =>
let (_, g) := idg in
match g with
| Gfun f => let (m1, b) := Mem.alloc m (comp_of f) 0 1 in Mem.drop_perm m1 b 0 1 Nonempty (comp_of f)
| Gvar v =>
    let init := gvar_init v in
    let comp := gvar_comp v in
    let sz := init_data_list_size init in
    let (m1, b) := Mem.alloc m comp 0 sz in
    match store_zeros m1 b 0 sz comp with
    | Some m2 => match Genv.store_init_data_list ge m2 b 0 init comp with
                 | Some m3 => Mem.drop_perm m3 b 0 sz (Genv.perm_globvar v) comp
                 | None => None
                 end
    | None => None
    end
end
     : forall F V : Type, has_comp F -> Genv.t F V -> mem -> ident * globdef F V -> option mem
      

    (* visible_fo *) }
  Admitted.


  Lemma asm_to_ir_returnstate_nccc_internal
        cpm (ge: genv) n n0
        (LT: (n0 < n)%nat)
        (IH: forall y : nat,
            (y < n)%nat ->
            forall (m_a0 : mem) (ast ast' : state) (tr : trace),
              wf_ge ge ->
              wf_asm ge ast ->
              star_measure (step_fix cpm) ge y ast tr ast' ->
              forall (ist : ir_state) (k : meminj) (d : mem_delta),
                match_state ge k m_a0 d ast ist ->
                exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = tr /\ istar ir_step ge ist btr ist')
        (WFGE: wf_ge ge)
        cur ik
        (WFIR0 : wf_ir_cur ge cur)
        (WFIR1 : wf_ir_conts ge ik)
        st (rs: regset)
        (WFASM1: wf_stack ge st)
        (MTST0 : match_cur_stack_sig cur ge st)
        (CURCOMP : Genv.find_comp ge (Vptr cur Ptrofs.zero) = callee_comp cpm st)
        (MTST2 : match_stack ge ik st)
        k d m_a0 m_i m_a
        (MEM: match_mem ge k d m_a0 m_i m_a)
        t' ast'
        (STEP: step_fix cpm ge (ReturnState st rs m_a) t' ast')
        t'' ast''
        (STAR: star_measure (step_fix cpm) ge n0 ast' t'' ast'')
        (NCCC: Genv.type_of_call ge (Genv.find_comp_ignore_offset ge (rs PC)) (callee_comp cpm st) <> Genv.CrossCompartmentCall)
        b1 ofs1
        (NEXTPC: rs PC = Vptr b1 ofs1)
        f
        (NEXTF : Genv.find_funct_ptr ge b1 = Some (Internal f))
    :
    exists (btr : bundle_trace) (ist' : ir_state),
      unbundle_trace btr = t' ** t'' /\ istar ir_step ge (Some (cur, m_i, ik)) btr ist'.
  Proof.
    destruct MEM as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    (** step --- ReturnState *)
    inv STEP. inv EV; simpl in *.
    2:{ rewrite H in NCCC. congruence with NCCC. }
    (** return is nccc *)
    clear H. pose proof STAR as STAR0. inv STAR.
    (* end case *)
    { end_case. }
    (* has next step - internal -> done*)
    rename H into STEP, H0 into STAR.
    (** next is internal *)
    exploit IH; clear IH. 4: eapply STAR0. lia. all: auto.
    { simpl. split.
      - unfold Genv.type_of_call in NCCC. des_ifs. unfold update_stack_return in STUPD. rewrite Pos.eqb_sym, Heq in STUPD. inv STUPD. auto.
      - unfold wf_regset in *. rewrite NEXTPC, NEXTF. auto.
    }
    { instantiate (4:=k). instantiate (3:=m_a0). instantiate (2:=d). instantiate (1:=Some (cur, m_i, ik)).
      assert (st' = st).
      { unfold Genv.type_of_call in NCCC. des_ifs. unfold update_stack_return in STUPD. rewrite Pos.eqb_sym, Heq in STUPD. inv STUPD. auto. }
      subst st'. simpl. split; auto. split; auto. split; auto. split.
      { unfold match_cur_regset in *. rewrite CURCOMP. unfold Genv.type_of_call in NCCC. des_ifs. apply Pos.eqb_eq in Heq. auto. }
      split; auto.
      { unfold match_mem. split; auto. }
    }
    intros (btr & ist' & UTR & ISTAR').
    exists btr, ist'. split; auto.
  Qed.

  Lemma match_mem_external_call_establish2
        ge k d m_a0 m_i m
        (MEM: match_mem ge k d m_a0 m_i m)
        ef args t res m'
        (EXTCALL: external_call ef ge args m t res m')
        (ECKO: external_call_known_observables ef ge m args t res m')
    :
    (external_call ef ge args m_i t res m_i) /\
      (external_call_known_observables ef ge m_i args t res m_i) /\
      (match_mem ge k d m_a0 m_i m')
  .
  Proof.
    destruct MEM as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    unfold external_call_known_observables in ECKO.
    des_ifs; simpl in *.
    { destruct ECKO as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify. esplits; eauto.
      1,2: econs; econs; eauto. split; auto. 
    }
    { destruct ECKO as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify. esplits; eauto.
      1,2: econs; econs; eauto. split; auto.
    }
    { destruct ECKO as [_ OBS]. inv EXTCALL. clarify. }
    { destruct ECKO as [_ OBS]. inv EXTCALL; clarify. }
    { destruct ECKO as [_ OBS]. inv EXTCALL; clarify. }
    { destruct ECKO as [_ OBS]. inv EXTCALL. esplits; eauto.
      1,2: econs; eauto. split; auto.
    }
    { destruct ECKO as [_ OBS]. inv EXTCALL. esplits; eauto.
      1,2: econs; eauto. split; auto.
    }
    { destruct ECKO as [_ OBS]. inv EXTCALL. clarify. }
  Qed.

  Lemma match_mem_external_call_establish
        (ge: genv) k d m_a0 m_i m
        (MEM: match_mem ge k d m_a0 m_i m)
        ef args t res m'
        (EXTCALL: external_call ef ge args m t res m')
        (ECC: external_call_unknowns ef ge m args \/ external_call_known_observables ef ge m args t res m')
    :
    exists d' m1 m2 res',
      (mem_delta_apply_inj (meminj_public ge) d' (Some m_i) = Some m1) /\
        (external_call ef ge args m1 t res' m2) /\
        ((external_call_unknowns ef ge m1 args) \/ (external_call_known_observables ef ge m1 args t res' m2)) /\
        (exists k2 d2 m_a02, match_mem ge k2 d2 m_a02 m2 m' /\ (Val.inject k2 res res' \/ (res = res')))
  .
  Proof.
    destruct ECC as [ECC | ECC].
    - exploit match_mem_external_call_establish1; eauto. intros. des. esplits; eauto.
    - exploit match_mem_external_call_establish2; eauto. intros. des. esplits; eauto. instantiate (1:=[]); ss. 
  Qed.

  Lemma asm_to_ir_step_external
        cpm (ge: genv)
        (WFGE: wf_ge ge)
        cur ik
        (WFIR0 : wf_ir_cur ge cur)
        (WFIR1 : wf_ir_conts ge ik)
        st (rs: regset)
        (WFASM1: wf_stack ge st)
        (MTST0 : match_cur_stack_sig cur ge st)
        (CURCOMP : Genv.find_comp ge (Vptr cur Ptrofs.zero) = callee_comp cpm st)
        (MTST2 : match_stack ge ik st)
        k d m_a0 m_i m_a
        (MEM: match_mem ge k d m_a0 m_i m_a)
        t ast'
        (STEP: step_fix cpm ge (State st rs m_a) t ast')
        b1 ofs1
        (NEXTPC: rs PC = Vptr b1 ofs1)
        ef
        (NEXTF : Genv.find_funct_ptr ge b1 = Some (External ef))
        n t' ast''
        (STAR: star_measure (step_fix cpm) ge n ast' t' ast'')
    :
    exists (btr : bundle_trace) k' d' m_a0' m_i' m_a',
      (unbundle_trace btr = t) /\
        (istar ir_step ge (Some (cur, m_i, ik)) btr (Some (cur, m_i', ik))) /\
        (match_mem ge k' d' m_a0' m_i' m_a') /\
        (exists res, star_measure (step_fix cpm) ge n
                             (ReturnState st (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) # PC <- (rs X1) m_a') t' ast'').
  Proof.
    destruct MEM as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    (* take a step *)
    inv STEP.
    (* invalid *)
    1,2,3,4: rewrite NEXTPC in H2; inv H2; rewrite NEXTF in H3; inv H3.
    rewrite NEXTPC in H2; inv H2; rewrite NEXTF in H3; inv H3.
    exploit Genv.find_funct_ptr_iff. intros (TEMP & _). specialize (TEMP NEXTF).
    exploit wf_ge_block_to_id; eauto. intros (ef_id & INVSYMB).
    exploit Genv.invert_find_symbol. eapply INVSYMB. intros FINDSYMB. clear TEMP.
    exploit extcall_cases. eapply ECC. eauto. clear ECC. intros [ECU | [ECKO | ECKS]].

    - (* extcall is unknown *)
      exploit match_mem_external_call_establish1; eauto. unfold match_mem; splits; eauto.
      intros. des.
      exists ([Bundle_call t ef_id (vals_to_eventvals ge args) (ef_sig ef0) (Some d)]).
      do 5 eexists. splits; simpl. 3: eapply x3. apply app_nil_r.
      2:{ exists res. auto. }
      econstructor 2. 2: econstructor 1. 2: eauto.
      eapply ir_step_intra_call_external; eauto.
      { unfold Genv.type_of_call in *. rewrite CURCOMP, <- REC_CURCOMP. rewrite NEXTPC. simpl.
        unfold Genv.find_comp. setoid_rewrite NEXTF. rewrite Pos.eqb_refl. auto.
      }

    - (* extcall is known and observable *)
      rename H4 into EXTCALL, H7 into EXTARGS. unfold external_call_known_observables in ECKO.
      des_ifs; simpl in *.
      { destruct ECKO as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify.
        exists ([Bundle_call [Event_vload chunk id ofs ev] ef_id [EVptr_global id ofs] {| sig_args := [Tptr]; sig_res := rettype_of_chunk chunk; sig_cc := cc_default |} (Some [])]).
        exists k, d, m_a0, m_i, m'. simpl. splits; auto. 2: split; auto. 2: eauto.
        econstructor 2. 2: econstructor 1. 2: auto.
        eapply ir_step_intra_call_external. all: eauto.
        { rewrite CURCOMP, <- REC_CURCOMP, NEXTPC. simpl. unfold Genv.find_comp. setoid_rewrite NEXTF. unfold Genv.type_of_call. rewrite Pos.eqb_refl. auto. }
        { simpl. eauto. }
        { simpl. econstructor. econstructor 1; eauto. }
        { simpl. right. econs; eauto. econs. econs; eauto. }
        { simpl. unfold senv_invert_symbol_total. erewrite Senv.find_invert_symbol; eauto. }
      }
      { destruct ECKO as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify.
        exists ([Bundle_call [Event_vstore chunk id ofs ev] ef_id [EVptr_global id ofs; ev] {| sig_args := [Tptr; type_of_chunk chunk]; sig_res := Tvoid; sig_cc := cc_default |} (Some [])]).
        exists k, d, m_a0, m_i, m'. simpl. splits; auto. 2: split; auto. 2: eauto.
        econstructor 2. 2: econstructor 1. 2: auto.
        eapply ir_step_intra_call_external. all: eauto.
        { rewrite CURCOMP, <- REC_CURCOMP, NEXTPC. simpl. unfold Genv.find_comp. setoid_rewrite NEXTF. unfold Genv.type_of_call. rewrite Pos.eqb_refl. auto. }
        { simpl. eauto. }
        { instantiate (2:=[Vptr b0 ofs; Val.load_result chunk v]).
          simpl. econstructor. econstructor 1; eauto. rewrite val_load_result_idem. auto.
        }
        { simpl. right. econs; eauto. econs. econs; eauto. rewrite val_load_result_idem. auto. }
        { simpl. unfold senv_invert_symbol_total. erewrite Senv.find_invert_symbol; eauto.
          f_equal. erewrite eventval_match_val_to_eventval; eauto.
        }
      }
      { destruct ECKO as [_ OBS]. inv EXTCALL. clarify. }
      { destruct ECKO as [_ OBS]. inv EXTCALL; clarify. }
      { destruct ECKO as [_ OBS]. inv EXTCALL; clarify. }
      { destruct ECKO as [_ OBS]. inv EXTCALL; simpl in *; clarify.
        exists ([Bundle_call [Event_annot text args0] ef_id (vals_to_eventvals ge args) {| sig_args := targs; sig_res := Tvoid; sig_cc := cc_default |} (Some [])]).
        exists k, d, m_a0, m_i, m'. simpl. splits; auto. 2: split; auto. 2: eauto.
        econstructor 2. 2: econstructor 1. 2: auto.
        eapply ir_step_intra_call_external. all: eauto.
        { rewrite CURCOMP, <- REC_CURCOMP, NEXTPC. simpl. unfold Genv.find_comp. setoid_rewrite NEXTF. unfold Genv.type_of_call. rewrite Pos.eqb_refl. auto. }
        { simpl. eauto. }
        { simpl. econstructor. auto. }
        { simpl. right. econs; eauto. econs. auto. }
      }
      { destruct ECKO as [_ OBS]. inv EXTCALL; simpl in *; clarify.
        exists ([Bundle_call [Event_annot text [arg]] ef_id [val_to_eventval ge res] {| sig_args := [targ]; sig_res := targ; sig_cc := cc_default |} (Some [])]).
        exists k, d, m_a0, m_i, m'. simpl. splits; auto. 2: split; auto. 2: eauto.
        econstructor 2. 2: econstructor 1. 2: auto.
        eapply ir_step_intra_call_external. all: eauto.
        { rewrite CURCOMP, <- REC_CURCOMP, NEXTPC. simpl. unfold Genv.find_comp. setoid_rewrite NEXTF. unfold Genv.type_of_call. rewrite Pos.eqb_refl. auto. }
        { simpl. eauto. }
        { simpl. econstructor. eauto. }
        { simpl. right. econs; eauto. econs. auto. }
        { simpl. auto. }
      }
      { destruct ECKO as [_ OBS]. inv EXTCALL. clarify. }

    - (* extcall is known and silent *)
      rename H4 into EXTCALL, H7 into EXTARGS. unfold external_call_known_silents in ECKS.
      des_ifs; ss; clarify.
      { unfold builtin_or_external_sem in EXTCALL. rewrite Heq in EXTCALL. inv EXTCALL.
        exists [], k, d, m_a0, m_i, m'. simpl. splits; auto. 2: split; auto. 2: eauto. econstructor 1.
      }
      { unfold builtin_or_external_sem in EXTCALL. rewrite Heq in EXTCALL. inv EXTCALL.
        exists [], k, d, m_a0, m_i, m'. simpl. splits; auto. 2: split; auto. 2: eauto. econstructor 1.
      }
      { destruct ECKS as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify.
        exists [], k, d, m_a0, m_i, m'. simpl. splits; auto. 2: split; auto. 2: eauto. econstructor 1.
      }
      { destruct ECKS as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify.
        exists [], k, (d ++ [mem_delta_kind_store (chunk, b0, (Ptrofs.unsigned ofs), v, cp)]), m_a0, m_i, m'. simpl. splits; auto. econstructor 1. 2: eauto. unfold match_mem. splits; auto.
        { eapply public_not_freeable_store; eauto. }
        { setoid_rewrite Forall_app. split; auto. econs; auto. simpl. auto. }
        { rewrite mem_delta_apply_app. rewrite MEM5. simpl. auto. }
      }
      { destruct ECKS as [_ OBS]. inv EXTCALL.
        exists [], k, (d ++ [mem_delta_kind_alloc (cp, (- size_chunk Mptr), (Ptrofs.unsigned sz)); mem_delta_kind_store (Mptr, b0, (- size_chunk Mptr), (Vptrofs sz), cp)]), m_a0, m_i, m'.
        simpl. splits; auto. econstructor 1. 2: eauto. unfold match_mem. splits; auto.
        { eapply public_not_freeable_store. 2: eauto. eapply public_not_freeable_alloc.
          3: eauto. all: auto.
          eapply meminj_not_alloc_delta; eauto.
        }
        { setoid_rewrite Forall_app. split; auto. econs; auto.
          { simpl. auto. }
          econs; auto. simpl. auto.
        }
        { rewrite mem_delta_apply_app. rewrite MEM5. simpl. rewrite H. simpl. auto. }
      }
      { destruct ECKS as [_ OBS]. inv EXTCALL.
        - exists [], k, (d ++ [mem_delta_kind_free (b0, (Ptrofs.unsigned lo - size_chunk Mptr)%Z, (Ptrofs.unsigned lo + Ptrofs.unsigned sz)%Z, cp)]), m_a0, m_i, m'.
          simpl. splits; auto. econstructor 1. 2: eauto. unfold match_mem. splits; auto.
          { eapply public_not_freeable_free; eauto. }
          { setoid_rewrite Forall_app. split; auto. econs; auto. simpl.
            eapply public_not_freeable_free_inj_none; eauto.
            { unfold size_chunk. unfold Mptr. des_ifs; lia. }
          }
          { rewrite mem_delta_apply_app. rewrite MEM5. simpl. auto. }
        - exists [], k, d, m_a0, m_i, m'.
          simpl. splits; auto. econstructor 1. 2: eauto. unfold match_mem. splits; auto.
      }
      { destruct ECKS as [_ [OBS NPUB]]. inv EXTCALL.
        exists [], k, (d ++ [mem_delta_kind_bytes (bdst, (Ptrofs.unsigned odst), bytes, cp)]), m_a0, m_i, m'.
        simpl. splits; auto. econstructor 1. 2: eauto. unfold match_mem. splits; auto.
        { eapply public_not_freeable_bytes; eauto. }
        { setoid_rewrite Forall_app. split; auto. econs; auto. simpl.
          clear - NPUB. simpl in NPUB. unfold meminj_public. des_ifs. exfalso. apply NPUB.
          exists i. auto.
        }
        { rewrite mem_delta_apply_app. rewrite MEM5. simpl. auto. }
      }

      { destruct ECKS as [_ OBS]. inv EXTCALL. clarify. }
      { destruct ECKS as [_ OBS]. inv EXTCALL. clarify. }
      { destruct ECKS as [_ OBS]. inv EXTCALL.
        exists [], k, d, m_a0, m_i, m'. simpl. splits; auto. 2: split; auto. 2: eauto. econstructor 1.
      }

  Qed.

  Lemma asm_to_ir_builtin
        (ge: genv)
        m_a0
        (WFGE: wf_ge ge)
        rs m st
        (WFASM: wf_asm ge (State st rs m))
        cur m_i ik k d
        (MTST: match_state ge k m_a0 d (State st rs m) (Some (cur, m_i, ik)))
        t1 ef vres m' b ofs f vargs
        (CURPC: rs PC = Vptr b ofs)
        (CURF: Genv.find_funct_ptr ge b = Some (Internal f))
        (EXTCALL: external_call ef ge vargs m t1 vres m')
        (ALLOWED: comp_of ef = comp_of f)
        (ECC: external_call_conds ef ge m vargs)
    :
    exists (btr : bundle_trace) k' d' m_a0' m_i',
      (unbundle_trace btr = t1) /\
        (istar ir_step ge (Some (cur, m_i, ik)) btr (Some (cur, m_i', ik))) /\
        (match_mem ge k' d' m_a0' m_i' m').
  Proof.
    ss. destruct MTST as (WFIR0 & WFIR1 & MTST0 & MTST1 & MTST2 & MTST3).
    destruct MTST3 as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    destruct WFASM as [WFASM0 WFASM1].
    exploit extcall_cases. eapply ECC. eauto. clear ECC. intros [ECU | [ECKO | ECKS]].

    - (* extcall is unknown *)
      exploit match_mem_external_call_establish1; eauto. unfold match_mem; splits; eauto.
      intros. des.
      exists ([Bundle_builtin t1 ef (vals_to_eventvals ge vargs) d]).
      do 4 eexists. splits; simpl. 3: eapply x3. apply app_nil_r.
      econstructor 2. 2: econstructor 1. 2: eauto.
      eapply ir_step_builtin; eauto.

    - (* extcall is known and observable *)
      unfold external_call_known_observables in ECKO.
      des_ifs; simpl in *.
      { destruct ECKO as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify.
        exists ([Bundle_builtin [Event_vload chunk id ofs0 ev] (EF_vload cp chunk) [EVptr_global id ofs0] []]).
        exists k, d, m_a0, m_i. simpl. splits; auto. 2: split; auto.
        econstructor 2. 2: econstructor 1. 2: auto.
        eapply ir_step_builtin. all: eauto.
        { simpl. eauto. }
        { simpl. econstructor. econstructor 1; eauto. }
        { simpl. right. econs; eauto. econs. econs; eauto. }
        { simpl. unfold senv_invert_symbol_total. erewrite Senv.find_invert_symbol; eauto. }
      }
      { destruct ECKO as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify.
        exists ([Bundle_builtin [Event_vstore chunk id ofs0 ev] (EF_vstore cp chunk) [EVptr_global id ofs0; ev] []]).
        exists k, d, m_a0, m_i. simpl. splits; auto. 2: split; auto.
        econstructor 2. 2: econstructor 1. 2: auto.
        eapply ir_step_builtin. all: eauto.
        { simpl. eauto. }
        { instantiate (2:=[Vptr b0 ofs0; Val.load_result chunk v]).
          simpl. econstructor. econstructor 1; eauto. rewrite val_load_result_idem. auto.
        }
        { simpl. right. econs; eauto. econs. econs; eauto. rewrite val_load_result_idem. auto. }
        { simpl. unfold senv_invert_symbol_total. erewrite Senv.find_invert_symbol; eauto.
          f_equal. erewrite eventval_match_val_to_eventval; eauto.
        }
      }
      { destruct ECKO as [_ OBS]. inv EXTCALL. clarify. }
      { destruct ECKO as [_ OBS]. inv EXTCALL; clarify. }
      { destruct ECKO as [_ OBS]. inv EXTCALL; clarify. }
      { destruct ECKO as [_ OBS]. inv EXTCALL; simpl in *; clarify.
        exists ([Bundle_builtin [Event_annot text args] (EF_annot cp kind text targs) (vals_to_eventvals ge vargs) []]).
        exists k, d, m_a0, m_i. simpl. splits; auto. 2: split; auto.
        econstructor 2. 2: econstructor 1. 2: auto.
        eapply ir_step_builtin. all: eauto.
        { simpl. eauto. }
        { simpl. econstructor. auto. }
        { simpl. right. econs; eauto. econs. auto. }
      }
      { destruct ECKO as [_ OBS]. inv EXTCALL; simpl in *; clarify.
        exists ([Bundle_builtin [Event_annot text [arg]] (EF_annot_val cp kind text targ) [val_to_eventval ge vres] []]).
        exists k, d, m_a0, m_i. simpl. splits; auto. 2: split; auto.
        econstructor 2. 2: econstructor 1. 2: auto.
        eapply ir_step_builtin. all: eauto.
        { simpl. eauto. }
        { simpl. econstructor. eauto. }
        { simpl. right. econs; eauto. econs. auto. }
        { simpl. auto. }
      }
      { destruct ECKO as [_ OBS]. inv EXTCALL. clarify. }

    - (* extcall is known and silent *)
      unfold external_call_known_silents in ECKS. des_ifs; ss; clarify.
      { unfold builtin_or_external_sem in EXTCALL. rewrite Heq in EXTCALL. inv EXTCALL.
        exists [], k, d, m_a0, m_i. simpl. splits; auto. 2: split; auto. econstructor 1.
      }
      { unfold builtin_or_external_sem in EXTCALL. rewrite Heq in EXTCALL. inv EXTCALL.
        exists [], k, d, m_a0, m_i. simpl. splits; auto. 2: split; auto. econstructor 1.
      }
      { destruct ECKS as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify.
        exists [], k, d, m_a0, m_i. simpl. splits; auto. 2: split; auto. econstructor 1.
      }
      { destruct ECKS as [_ OBS]. inv EXTCALL. inv H; simpl in *; clarify.
        exists [], k, (d ++ [mem_delta_kind_store (chunk, b0, (Ptrofs.unsigned ofs0), v, cp)]), m_a0, m_i. simpl. splits; auto. econstructor 1. unfold match_mem. splits; auto.
        { eapply public_not_freeable_store; eauto. }
        { setoid_rewrite Forall_app. split; auto. econs; auto. simpl. auto. }
        { rewrite mem_delta_apply_app. rewrite MEM5. simpl. auto. }
      }
      { destruct ECKS as [_ OBS]. inv EXTCALL.
        exists [], k, (d ++ [mem_delta_kind_alloc (cp, (- size_chunk Mptr), (Ptrofs.unsigned sz)); mem_delta_kind_store (Mptr, b0, (- size_chunk Mptr), (Vptrofs sz), cp)]), m_a0, m_i.
        simpl. splits; auto. econstructor 1. unfold match_mem. splits; auto.
        { eapply public_not_freeable_store. 2: eauto. eapply public_not_freeable_alloc.
          3: eauto. all: auto.
          eapply meminj_not_alloc_delta; eauto.
        }
        { setoid_rewrite Forall_app. split; auto. econs; auto.
          { simpl. auto. }
          econs; auto. simpl. auto.
        }
        { rewrite mem_delta_apply_app. rewrite MEM5. simpl. rewrite H. simpl. auto. }
      }
      { destruct ECKS as [_ OBS]. inv EXTCALL.
        - exists [], k, (d ++ [mem_delta_kind_free (b0, (Ptrofs.unsigned lo - size_chunk Mptr)%Z, (Ptrofs.unsigned lo + Ptrofs.unsigned sz)%Z, cp)]), m_a0, m_i.
          simpl. splits; auto. econstructor 1. unfold match_mem. splits; auto.
          { eapply public_not_freeable_free; eauto. }
          { setoid_rewrite Forall_app. split; auto. econs; auto. simpl.
            eapply public_not_freeable_free_inj_none; eauto.
            { unfold size_chunk. unfold Mptr. des_ifs; lia. }
          }
          { rewrite mem_delta_apply_app. rewrite MEM5. simpl. auto. }
        - exists [], k, d, m_a0, m_i.
          simpl. splits; auto. econstructor 1. unfold match_mem. splits; auto.
      }
      { destruct ECKS as [_ [OBS NPUB]]. inv EXTCALL.
        exists [], k, (d ++ [mem_delta_kind_bytes (bdst, (Ptrofs.unsigned odst), bytes, cp)]), m_a0, m_i.
        simpl. splits; auto. econstructor 1. unfold match_mem. splits; auto.
        { eapply public_not_freeable_bytes; eauto. }
        { setoid_rewrite Forall_app. split; auto. econs; auto. simpl.
          clear - NPUB. simpl in NPUB. unfold meminj_public. des_ifs. exfalso. apply NPUB.
          exists i. auto.
        }
        { rewrite mem_delta_apply_app. rewrite MEM5. simpl. auto. }
      }

      { destruct ECKS as [_ OBS]. inv EXTCALL. clarify. }
      { destruct ECKS as [_ OBS]. inv EXTCALL. clarify. }
      { destruct ECKS as [_ OBS]. inv EXTCALL.
        exists [], k, d, m_a0, m_i. simpl. splits; auto. 2: split; auto. econstructor 1.
      }

  Qed.


  Lemma asm_to_ir_returnstate_undef_nccc_external
        cpm (ge: genv) n n0
        (LT: (n0 < n)%nat)
        (IH: forall y : nat,
            (y < n)%nat ->
            forall (m_a0 : mem) (ast ast' : state) (tr : trace),
              wf_ge ge ->
              wf_asm ge ast ->
              star_measure (step_fix cpm) ge y ast tr ast' ->
              forall (ist : ir_state) (k : meminj) (d : mem_delta),
                match_state ge k m_a0 d ast ist ->
                exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = tr /\ istar ir_step ge ist btr ist')
        (WFGE: wf_ge ge)
        cur ik
        (WFIR0 : wf_ir_cur ge cur)
        (WFIR1 : wf_ir_conts ge ik)
        st (rs: regset)
        (WFASM1: wf_stack ge st)
        (MTST0 : match_cur_stack_sig cur ge st)
        (CURCOMP : Genv.find_comp ge (Vptr cur Ptrofs.zero) = callee_comp cpm st)
        (MTST2 : match_stack ge ik st)
        k d m_a0 m_i m_a
        (MEM: match_mem ge k d m_a0 m_i m_a)
        (RSX: rs X1 = Vundef)
        t' ast'
        (STEP: step_fix cpm ge (ReturnState st rs m_a) t' ast')
        t'' ast''
        (STAR: star_measure (step_fix cpm) ge n0 ast' t'' ast'')
        (NCCC: Genv.type_of_call ge (Genv.find_comp_ignore_offset ge (rs PC)) (callee_comp cpm st) <> Genv.CrossCompartmentCall)
        b1 ofs1
        (NEXTPC: rs PC = Vptr b1 ofs1)
        ef
        (NEXTF : Genv.find_funct_ptr ge b1 = Some (External ef))
    :
    exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = t' ** t'' /\ istar ir_step ge (Some (cur, m_i, ik)) btr ist'.
  Proof.
    destruct MEM as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    (** step --- ReturnState *)
    inv STEP. inv EV; simpl in *.
    2:{ rewrite H in NCCC. congruence with NCCC. }
    (** return is nccc *)
    clear H. pose proof STAR as STAR0. inv STAR.
    (* end case *)
    { end_case. }
    (** next is external --- another extcall, Returnstate, and finally next-next PC is Vundef *)
    (* take a step *)
    rename H into STEP, H0 into STAR.

    assert (st' = st).
    { unfold Genv.type_of_call in NCCC. des_ifs. unfold update_stack_return in STUPD. rewrite Pos.eqb_sym, Heq in STUPD. inv STUPD. auto. }
    subst st'.
    exploit asm_to_ir_step_external.
    12: eapply STAR. 11: eapply NEXTF. 10: eapply NEXTPC. 9: eapply STEP.
    all: eauto.
    { split; eauto. }
    clear STEP STAR.
    intros (btr1 & k' & d' & m_a0' & m_i' & m_a' & UTR1 & ISTAR1 & MM' & (res & STAR)).
    eapply asm_to_ir_compose. 2: eauto. do 2 eexists. split; eauto. clear btr1 UTR1 ISTAR1.

    assert (STUCK: (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs))
                     # PC <- (rs X1) PC = Vundef).
    { rewrite Pregmap.gss. auto. }
    inv STAR.
    (* end case *)
    { exists []. eexists. split; auto. econstructor 1. }
    (* now at Returnstate *)
    inv H; simpl in *. rewrite Pregmap.gss in *. inv H0.
    (* end case *)
    { inv EV.
      (* return is NCCC - silent *)
      { exists []. simpl. eexists. split; auto. econstructor 1. }
      (* return is CCC - return event *)
      { unfold Genv.type_of_call in H. des_ifs. unfold update_stack_return in STUPD0.
        clear H. rewrite Pregmap.gss in *.
        rewrite Pos.eqb_sym in Heq. rewrite Heq in STUPD0. des_ifs.
        pose proof Heq as NEQ. eapply Pos.eqb_neq in NEQ. specialize (PC_RA0 NEQ).
        (* stuck --- return PC is Vundef *)
        rewrite STUCK in PC_RA0. clear - PC_RA0. exfalso. simpl in PC_RA0. des_ifs.
      }
    }
    (* stuck case *)
    inv H; simpl in *; rewrite Pregmap.gss in *; rewrite STUCK in H5; inv H5.
  Qed.

  Lemma asm_to_ir_returnstate_ccc
        cpm (ge: genv) n n0
        (LT: (n0 < n)%nat)
        (IH: forall y : nat,
            (y < n)%nat ->
            forall (m_a0 : mem) (ast ast' : state) (tr : trace),
              wf_ge ge ->
              wf_asm ge ast ->
              star_measure (step_fix cpm) ge y ast tr ast' ->
              forall (ist : ir_state) (k : meminj) (d : mem_delta),
                match_state ge k m_a0 d ast ist ->
                exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = tr /\ istar ir_step ge ist btr ist')
        (WFGE: wf_ge ge)
        cur ik
        (WFIR0 : wf_ir_cur ge cur)
        (WFIR1 : wf_ir_conts ge ik)
        st (rs: regset)
        (WFASM1: wf_stack ge st)
        (MTST0 : match_cur_stack_sig cur ge st)
        (CURCOMP : Genv.find_comp ge (Vptr cur Ptrofs.zero) = callee_comp cpm st)
        (MTST2 : match_stack ge ik st)
        k d m_a0 m_i m_a
        (MEM: match_mem ge k d m_a0 m_i m_a)
        t' ast'
        (STEP: step_fix cpm ge (ReturnState st rs m_a) t' ast')
        t'' ast''
        (STAR: star_measure (step_fix cpm) ge n0 ast' t'' ast'')
        (CCC: Genv.type_of_call ge (Genv.find_comp_ignore_offset ge (rs PC)) (callee_comp cpm st) = Genv.CrossCompartmentCall)
    :
    exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = t' ** t'' /\ istar ir_step ge (Some (cur, m_i, ik)) btr ist'.
  Proof.
    destruct MEM as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    (** step --- ReturnState *)
    inv STEP. inv EV; simpl in *.
    { rewrite CCC in H. congruence with H. }
    clear H.
    (** return is ccc --- next is poped from the stack, which is internal, so done *)
    unfold Genv.type_of_call in CCC. des_ifs. clear CCC. unfold update_stack_return in STUPD.
    rewrite Pos.eqb_sym in Heq. rewrite Heq in STUPD. des_ifs.
    pose proof Heq as NEQ. eapply Pos.eqb_neq in NEQ. specialize (PC_RA NEQ).
    destruct s as [b3 cp3 sig3 rv3 ptr3]. simpl in *.
    inv WFASM1. simpl in *. des_ifs. clear H2. inv MTST2.
    exploit (IH _ _ _ _ _ _ _ _ STAR). lia. all: auto.
    { simpl. split; auto. unfold wf_regset. rewrite PC_RA. rewrite Heq0. auto. }
    { instantiate (4:=k). instantiate (3:=m_a0). instantiate (2:=d).
      instantiate (1:=Some (next, m_i, ik_tl)). simpl. splits; auto.
      { inv WFIR1. simpl in *. auto. }
      { inv WFIR1. auto. }
      { unfold match_cur_regset. rewrite COMP. rewrite PC_RA. auto. }
      { split; auto. }
    }
    intros (btr & ist' & UTR & ISTAR').
    exists ((Bundle_return [Event_return (Genv.find_comp_ignore_offset ge (rs PC)) (Genv.find_comp ge (Vptr cur Ptrofs.zero)) res] res) :: btr), ist'.
    simpl. rewrite UTR. split; auto.
    econstructor 2. 2: eapply ISTAR'. 2: auto.
    inv WFIR1. simpl in *. des_ifs. clear H2. unfold wf_ir_cur in WFIR0. des_ifs. clear WFIR0.
    eapply ir_step_cross_return_internal. 6: eapply Heq1. all: eauto.
    { rewrite COMP. rewrite PC_RA. simpl. auto. }
    constructor; auto.
    { unfold Genv.type_of_call. rewrite Pos.eqb_sym, Heq. auto. }
    { replace (funsig (Internal f2)) with sig3; auto. unfold match_cur_stack_sig in MTST0. des_ifs. }
  Qed.

  Lemma asm_to_ir_returnstate_undef
        cpm (ge: genv) n n0
        (LT: (n0 < n)%nat)
        (IH: forall y : nat,
            (y < n)%nat ->
            forall (m_a0 : mem) (ast ast' : state) (tr : trace),
              wf_ge ge ->
              wf_asm ge ast ->
              star_measure (step_fix cpm) ge y ast tr ast' ->
              forall (ist : ir_state) (k : meminj) (d : mem_delta),
                match_state ge k m_a0 d ast ist ->
                exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = tr /\ istar ir_step ge ist btr ist')
        (WFGE: wf_ge ge)
        cur ik
        (WFIR0 : wf_ir_cur ge cur)
        (WFIR1 : wf_ir_conts ge ik)
        st (rs: regset)
        (WFASM1: wf_stack ge st)
        (MTST0 : match_cur_stack_sig cur ge st)
        (CURCOMP : Genv.find_comp ge (Vptr cur Ptrofs.zero) = callee_comp cpm st)
        (MTST2 : match_stack ge ik st)
        k d m_a0 m_i m_a
        (MEM: match_mem ge k d m_a0 m_i m_a)
        (RSX: rs X1 = Vundef)
        t' ast'
        (STEP: step_fix cpm ge (ReturnState st rs m_a) t' ast')
        t'' ast''
        (STAR: star_measure (step_fix cpm) ge n0 ast' t'' ast'')
    :
    exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = t' ** t'' /\ istar ir_step ge (Some (cur, m_i, ik)) btr ist'.
  Proof.
    destruct MEM as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    (** step --- ReturnState *)
    pose proof STEP as STEP0. inv STEP. inv EV; simpl in *.
    (** return is nccc *)
    { rename H into NCCC. pose proof STAR as STAR0. inv STAR.
      (* end case *)
      { end_case. }
      (* has next step - if internal, done; if external, ub by RSX *)
      rename H into STEP, H0 into STAR. exploit asm_step_current_pc. eapply STEP. intros (b1 & ofs1 & NEXTPC).
      exploit asm_step_some_fundef. eapply STEP. eapply NEXTPC. intros (fd & NEXTF).
      destruct fd.
      (** next is internal *)
      { exploit asm_to_ir_returnstate_nccc_internal. 2: eapply IH.
        11: eapply STAR0. 10: eapply STEP0. all: eauto. split; eauto.
      }
      (** next is external --- undef *)
      { exploit asm_to_ir_returnstate_undef_nccc_external. 2: eapply IH.
        12: eapply STAR0. 11: eapply STEP0. all: eauto. split; eauto.
      }
    }
    (** return is ccc --- next is poped from the stack, which is internal, so done *)
    { exploit asm_to_ir_returnstate_ccc. 2: eapply IH.
      11: eapply STAR. 10: eapply STEP0. all: eauto. split; eauto.
    }
  Qed.

  Lemma asm_to_ir_returnstate_nccc_external
        cpm (ge: genv) n n0
        (LT: (n0 < n)%nat)
        (IH: forall y : nat,
            (y < n)%nat ->
            forall (m_a0 : mem) (ast ast' : state) (tr : trace),
              wf_ge ge ->
              wf_asm ge ast ->
              star_measure (step_fix cpm) ge y ast tr ast' ->
              forall (ist : ir_state) (k : meminj) (d : mem_delta),
                match_state ge k m_a0 d ast ist ->
                exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = tr /\ istar ir_step ge ist btr ist')
        (WFGE: wf_ge ge)
        cur ik
        (WFIR0 : wf_ir_cur ge cur)
        (WFIR1 : wf_ir_conts ge ik)
        st (rs: regset)
        (WFASM1: wf_stack ge st)
        (MTST0 : match_cur_stack_sig cur ge st)
        (CURCOMP : Genv.find_comp ge (Vptr cur Ptrofs.zero) = callee_comp cpm st)
        (MTST2 : match_stack ge ik st)
        k d m_a0 m_i m_a
        (MEM: match_mem ge k d m_a0 m_i m_a)
        t' ast'
        (STEP: step_fix cpm ge (ReturnState st rs m_a) t' ast')
        t'' ast''
        (STAR: star_measure (step_fix cpm) ge n0 ast' t'' ast'')
        (NCCC: Genv.type_of_call ge (Genv.find_comp_ignore_offset ge (rs PC)) (callee_comp cpm st) <> Genv.CrossCompartmentCall)
        b1 ofs1
        (NEXTPC: rs PC = Vptr b1 ofs1)
        ef
        (NEXTF : Genv.find_funct_ptr ge b1 = Some (External ef))
    :
    exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = t' ** t'' /\ istar ir_step ge (Some (cur, m_i, ik)) btr ist'.
  Proof.
    destruct MEM as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    (** step --- ReturnState *)
    inv STEP. inv EV; simpl in *.
    2:{ rewrite H in NCCC. congruence with NCCC. }
    (** return is nccc *)
    clear H. pose proof STAR as STAR0. inv STAR.
    (* end case *)
    { end_case. }
    (** next is external --- another extcall, Returnstate, and finally next-next PC is Vundef *)
    (* take a step *)
    rename H into STEP, H0 into STAR.

    assert (st' = st).
    { unfold Genv.type_of_call in NCCC. des_ifs. unfold update_stack_return in STUPD. rewrite Pos.eqb_sym, Heq in STUPD. inv STUPD. auto. }
    subst st'.
    exploit asm_to_ir_step_external.
    12: eapply STAR. 11: eapply NEXTF. 10: eapply NEXTPC. 9: eapply STEP.
    all: eauto.
    { split; eauto. }
    clear STEP STAR.
    intros (btr1 & k' & d' & m_a0' & m_i' & m_a' & UTR1 & ISTAR1 & MM' & (res & STAR)).
    eapply asm_to_ir_compose. 2: eauto. do 2 eexists. split; eauto. clear btr1 UTR1 ISTAR1.

    inv STAR.
    (* end case *)
    { exists []. eexists. split; auto. econstructor 1. }
    (* now at Returnstate *)
    eapply asm_to_ir_returnstate_undef. 2: eapply IH. 12: eapply H0. 11: eapply H.
    all: eauto. lia.
    { clear. rewrite Pregmap.gso. 2: congruence. unfold loc_external_result. unfold Conventions1.loc_result. des_ifs. }
  Qed.

  Lemma asm_to_ir_returnstate
        cpm (ge: genv) n n0
        (LT: (n0 < n)%nat)
        (IH: forall y : nat,
            (y < n)%nat ->
            forall (m_a0 : mem) (ast ast' : state) (tr : trace),
              wf_ge ge ->
              wf_asm ge ast ->
              star_measure (step_fix cpm) ge y ast tr ast' ->
              forall (ist : ir_state) (k : meminj) (d : mem_delta),
                match_state ge k m_a0 d ast ist ->
                exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = tr /\ istar ir_step ge ist btr ist')
        (WFGE: wf_ge ge)
        cur ik
        (WFIR0 : wf_ir_cur ge cur)
        (WFIR1 : wf_ir_conts ge ik)
        st (rs: regset)
        (WFASM1: wf_stack ge st)
        (MTST0 : match_cur_stack_sig cur ge st)
        (CURCOMP : Genv.find_comp ge (Vptr cur Ptrofs.zero) = callee_comp cpm st)
        (MTST2 : match_stack ge ik st)
        k d m_a0 m_i m_a
        (MEM: match_mem ge k d m_a0 m_i m_a)
        t' ast'
        (STEP: step_fix cpm ge (ReturnState st rs m_a) t' ast')
        t'' ast''
        (STAR: star_measure (step_fix cpm) ge n0 ast' t'' ast'')
    :
    exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = t' ** t'' /\ istar ir_step ge (Some (cur, m_i, ik)) btr ist'.
  Proof.
    destruct MEM as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    (** step --- ReturnState *)
    pose proof STEP as STEP0. inv STEP. inv EV; simpl in *.
    (** return is nccc *)
    { rename H into NCCC. pose proof STAR as STAR0. inv STAR.
      (* end case *)
      { end_case. }
      (* has next step - if internal, done; if external, one external step and X1 = undef *)
      rename H into STEP, H0 into STAR. exploit asm_step_current_pc. eapply STEP. intros (b1 & ofs1 & NEXTPC).
      exploit asm_step_some_fundef. eapply STEP. eapply NEXTPC. intros (fd & NEXTF).
      destruct fd.
      (** next is internal *)
      { exploit asm_to_ir_returnstate_nccc_internal. 2: eapply IH.
        11: eapply STAR0. 10: eapply STEP0. all: eauto. split; eauto.
      }
      (** next is external --- another extcall, Returnstate, and finally next-next PC is Vundef *)
      { exploit asm_to_ir_returnstate_nccc_external. 2: eapply IH.
        11: eapply STAR0. 10: eapply STEP0. all: eauto. split; eauto.
      }
    }
    (** return is ccc --- next is poped from the stack, which is internal, so done *)
    { exploit asm_to_ir_returnstate_ccc. 2: eapply IH.
      11: eapply STAR. 10: eapply STEP0. all: eauto. split; eauto.
    }
  Qed.

  Lemma asm_to_ir_nccc_internal
        cpm ge n n'
        (LT: (n < n')%nat)
        (IH: forall y : nat,
            (y < n')%nat ->
            forall (m_a0 : mem) (ast ast' : state) (tr : trace),
              wf_ge ge ->
              wf_asm ge ast ->
              star_measure (step_fix cpm) ge y ast tr ast' ->
              forall (ist : ir_state) (k : meminj) (d : mem_delta), match_state ge k m_a0 d ast ist ->
                                                               exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = tr /\ istar ir_step ge ist btr ist')
        m_a0 ast'
        (WFGE: wf_ge ge)
        rs m st
        (WFASM: wf_asm ge (State st rs m))
        ist k d
        (MTST: match_state ge k m_a0 d (State st rs m) ist)
        t2 rs' m'
        (STAR: star_measure (step_fix cpm) ge n (State st rs' m') t2 ast')
        b
        ofs
        f
        i
        b'
        ofs'
        (H0: rs PC = Vptr b ofs)
        (H1: Genv.find_funct_ptr ge b = Some (Internal f))
        (H2: find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i)
        (H3: exec_instr ge f i rs m (comp_of f) = Next rs' m')
        (NEXTPC: rs' PC = Vptr b' ofs')
        (ALLOWED: comp_of f = Genv.find_comp_ignore_offset ge (Vptr b' ofs'))
    :
    exists (btr : bundle_trace) (ist' : ir_state), unbundle_trace btr = t2 /\ istar ir_step ge ist btr ist'.
  Proof.
    destruct (Genv.find_funct_ptr ge b') eqn:NEXTF.
    (* no next function *)
    2:{ move STAR after NEXTF. inv STAR.
        (* end case *)
        { end_case. }
        (* take a step *)
        { inv H.
          (* invalid *)
          all: exfalso; rewrite NEXTPC in H8; inv H8; rewrite NEXTF in H9; inv H9.
        }
    }
    unfold match_state in MTST. destruct ist as [[[cur m_i] ik] |].
    2:{ inv MTST. }
    destruct MTST as (WFIR0 & WFIR1 & MTST0 & MTST1 & MTST2 & MTST3). destruct MTST3 as (MEM0 & MEM1 & MEM2 & MEM3 & MEM4 & MEM5).
    exploit mem_delta_exec_instr. eapply MEM3. eapply H3. eapply MEM4. eapply MEM5. intros (d' & MEM4' & MEM5').
    destruct f0.

    (** has next function --- internal *)
    { assert (WFASM': wf_asm ge (State st rs' m')).
      { clear IH. unfold wf_asm in *. destruct WFASM as [WFASM0 WFASM1]. split; [auto|].
        unfold wf_regset in *. rewrite H0, H1 in WFASM1. rewrite NEXTPC, NEXTF. auto.
      }
      assert (MTST': match_state ge k m_a0 d' (State st rs' m') (Some (cur, m_i, ik))).
      { clear IH. split. auto. split. auto. split. auto. split.
        { unfold match_cur_regset in *. rewrite NEXTPC. rewrite <- ALLOWED. rewrite MTST1.
          unfold Genv.find_comp_ignore_offset. rewrite H0. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr.
          rewrite H1. auto.
        }
        split. auto.
        { unfold match_mem. repeat (split; auto). eapply public_not_freeable_exec_instr. 3: eapply H3. all: auto. eapply meminj_not_alloc_delta; eauto. }
      }
      exploit IH. 4: eapply STAR. 3: apply WFASM'. 3: eapply MTST'. all: auto.
    }

    (** has next function --- external *)
    { move STAR after NEXTF. inv STAR.
      (* end case *)
      { end_case. }
      (* take a step *)
      destruct WFASM as [WFASM0 WFASM1].
      exploit asm_to_ir_step_external. 12: eapply H4. 11: eapply NEXTF. 10: eapply NEXTPC. 9: eapply H. all: eauto.
      { inv H.
        1,2,3,4: rewrite NEXTPC in H8; inv H8; rewrite NEXTF in H9; inv H9.
        rewrite <- REC_CURCOMP. rewrite H8. rewrite MTST1, H0. simpl in *. rewrite NEXTPC in H8; inv H8. rewrite <- ALLOWED.
        unfold Genv.find_comp. setoid_rewrite H1. auto.
      }
      { instantiate (4:=k). instantiate (3:=d'). unfold match_mem. splits; eauto.
        eapply public_not_freeable_exec_instr; eauto. eapply meminj_not_alloc_delta; eauto.
      }
      intros (btr' & k' & d'0 & m_a0' & m_i' & m_a' & UTR' & ISTAR' & MM' & (res' & STAR')).
      eapply asm_to_ir_compose. 2: eauto.
      exists btr'. eexists. split.
      { split; auto. eapply ISTAR'. }
      clear btr' UTR' ISTAR'. rename H into STEP0, H4 into STAR0.
      inv STAR'.
      { end_case. }
      exploit asm_to_ir_returnstate_undef. 2: eapply IH. 12: eapply H4. 11: eapply H. 9: eapply MM'. all: eauto.
      { lia. }
      { inv STEP0.
        1,2,3,4: rewrite NEXTPC in H8; inv H8; rewrite NEXTF in H9; inv H9.
        rewrite <- REC_CURCOMP. rewrite H8. rewrite MTST1, H0. simpl in *. rewrite NEXTPC in H8; inv H8. rewrite <- ALLOWED.
        unfold Genv.find_comp. setoid_rewrite H1. auto.
      }
      { clear. rewrite Pregmap.gso. 2: congruence. unfold loc_external_result. unfold Conventions1.loc_result. des_ifs. }
    }
  Qed.

  Lemma asm_to_ir_ccc_external1
        ge rs cur
        (MTST1 : match_cur_regset cur ge rs)
        rs' e b ofs f args
        (H0 : rs PC = Vptr b ofs)
        (H1 : Genv.find_funct_ptr ge b = Some (Internal f))
        ofs0 b0
        (ALLOWED : Genv.allowed_call ge (comp_of f) (Vptr b0 Ptrofs.zero))
        (NEXTPC : rs' PC = Vptr b0 ofs0)
        (TYPEC : Genv.type_of_call ge (comp_of f) (Genv.find_comp ge (Vptr b0 Ptrofs.zero)) = Genv.CrossCompartmentCall)
        (NO_CROSS_PTR : Forall not_ptr args)
        (CALLSIG : Genv.find_funct_ptr ge b0 = Some (External e))
        vl i0
        (H3 : Genv.invert_symbol ge b0 = Some i0)
        (H4 : eventval_list_match ge vl (sig_args (ef_sig e)) args)
    :
    exists cp cp' sg,
      (cp = Genv.find_comp ge (Vptr cur Ptrofs.zero)) /\
        (Genv.find_symbol ge i0 = Some b0) /\
        (Genv.find_funct ge (Vptr b0 Ptrofs.zero) = Some (External e)) /\
        (cp' = comp_of e) /\
        (Genv.allowed_call ge cp (Vptr b0 Ptrofs.zero)) /\
        (crossing_comp ge cp cp' -> Forall not_ptr args) /\
        (sg = ef_sig e) /\
        (call_trace_cross ge cp cp' b0 args (sig_args sg) [Event_call (comp_of f) (Genv.find_comp ge (Vptr b0 Ptrofs.zero)) i0 vl] i0 vl).
  Proof.
    assert (EQC : Genv.find_comp ge (Vptr b Ptrofs.zero) = comp_of f).
    { unfold Genv.find_comp. setoid_rewrite H1. auto. }
    assert (EQC2 : Genv.find_comp ge (Vptr b0 Ptrofs.zero) = comp_of e).
    { unfold Genv.find_comp. setoid_rewrite CALLSIG. auto. }
    do 3 eexists.
    ss. splits; auto.
    - eapply Genv.invert_find_symbol; auto.
    - replace (Genv.find_comp ge (Vptr cur Ptrofs.zero)) with (comp_of f); auto. rewrite MTST1, H0. ss.
    - econs; auto.
      + unfold Genv.type_of_call.
        replace (comp_of e) with (Genv.find_comp ge (Vptr b0 Ptrofs.zero)); auto.
        replace (Genv.find_comp ge (Vptr cur Ptrofs.zero)) with (comp_of f); auto. rewrite MTST1, H0. ss.
      + replace (comp_of e) with (Genv.find_comp ge (Vptr b0 Ptrofs.zero)); auto.
        replace (Genv.find_comp ge (Vptr cur Ptrofs.zero)) with (comp_of f); auto. rewrite MTST1, H0. ss.
  Qed.

  Lemma arguments_same
        rs m sig args1 args2
        (CARGS: call_arguments rs m sig args1)
        (EARGS: extcall_arguments rs m sig args2)
    :
    args1 = args2.
  Proof.
    unfold call_arguments in CARGS. unfold extcall_arguments in EARGS.
    unfold Conventions.loc_parameters in CARGS. remember (Conventions1.loc_arguments sig) as clas. clear dependent sig.
    move args1 after rs. revert_until args1. induction args1; ss; intros.
    { inv CARGS. symmetry in H0. apply map_eq_nil in H0. subst. inv EARGS. auto. }
    inv CARGS. symmetry in H. apply map_eq_cons in H. des; clarify.
    inv EARGS. f_equal.
    2:{ eapply IHargs1; eauto. }
    clear - H2 H1. inv H1; ss.
    - inv H2. inv H.
      + ss. inv H1; auto.
      + inv H1; auto. unfold Mem.loadv in *. des_ifs. apply Mem.load_Some_None in H2, H5. rewrite H2 in H5. inv H5. auto.
    - inv H2. inv H.
      + inv H0.
        * inv H4. inv H6. auto.
        * inv H4. inv H6. unfold Mem.loadv in *. des_ifs. apply Mem.load_Some_None in H1, H4. rewrite H1 in H4. inv H4. auto.
      + inv H0.
        * inv H4. inv H6. unfold Mem.loadv in *. des_ifs. apply Mem.load_Some_None in H2, H5. rewrite H2 in H5. inv H5. auto.
        * inv H4. inv H6. unfold Mem.loadv in *. des_ifs. apply Mem.load_Some_None in H1, H2, H5, H7. rewrite H2 in H7. rewrite H1 in H5. clarify.
  Qed.


  (* If main is External, treat it as a different case - 
     the trace can start with Event_syscall, without a preceding Event_call *)
  Theorem asm_to_ir
          cpm (ge: genv) m_a0
          ast ast' tr
          (WFGE: wf_ge ge)
          (WFASM: wf_asm ge ast)
          (STAR: star (Asm.step_fix cpm) ge ast tr ast')
          ist k d
          (MTST: match_state ge k m_a0 d ast ist)
    :
    exists btr ist', (unbundle_trace btr = tr) /\ (istar (ir_step) ge ist btr ist').
  Proof.
    apply measure_star in STAR. destruct STAR as (n & STAR).
    move n before ge. revert m_a0 ast ast' tr WFGE WFASM STAR ist k d MTST.
    pattern n. apply (well_founded_induction Nat.lt_wf_0). intros n1 IH. intros.
    inv STAR; subst.
    (* end case *)
    { end_case. }
    rename H0 into STAR. inv H; simpl.

    - (** internal *)
      eapply asm_to_ir_nccc_internal; eauto.

    - (** internal_call *)
      assert (EQC: (Genv.find_comp_ignore_offset ge (Vptr b Ptrofs.zero)) = (comp_of f)).
      { ss. unfold Genv.find_comp. setoid_rewrite H1. auto. }
      destruct (Genv.type_of_call ge (comp_of f) (Genv.find_comp_ignore_offset ge (Vptr b' ofs'))) eqn:TYPEC.
      (* case nccc: same as the previous *)
      { assert (st' = st).
        { unfold Genv.type_of_call in TYPEC. des_ifs. unfold update_stack_call in STUPD. rewrite EQC in STUPD. rewrite NEXTPC, Heq in STUPD. inv STUPD. auto. }
        subst.
        exploit asm_to_ir_nccc_internal. 2: eapply IH. 5: eapply STAR. all: eauto. rewrite <- EQC; auto.
        { unfold Genv.type_of_call in TYPEC. des_ifs. rewrite Pos.eqb_eq in Heq. auto. }
        intros RES. inv EV. simpl. apply RES. rewrite TYPEC in H. inv H.
      }

      (* case ccc *)
      { destruct ist as [[[cur m_i] ik] |]; ss.
        destruct MTST as (WFIR0 & WFIR1 & MTST0 & MTST1 & MTST2 & MTST3).
        destruct WFASM as [WFASM0 WFASM1].
        assert (Genv.CrossCompartmentCall <> Genv.InternalCall) by congruence. specialize (CALLSIG H); clear H. des.
        exploit exec_instr_is_call; eauto. clear H2 H3 H4. intros (RSX & MEM). subst m'.
        destruct fd.
        (* calling internal function *)
        { inv EV.
          { rewrite TYPEC in H. clarify. }
          clear H. clarify. unfold update_stack_call in STUPD. des_ifs.
          { unfold Genv.type_of_call in TYPEC. rewrite NEXTPC in Heq. rewrite <- EQC in TYPEC. ss. rewrite Heq in TYPEC. inv TYPEC. }
          ss. eapply asm_to_ir_compose.
          2:{ instantiate (2:=[Event_call (comp_of f) (Genv.find_comp ge (Vptr b0 Ptrofs.zero)) i0 vl]). simpl. eauto. }
          assert (EQC2: (Genv.find_comp ge (Vptr b0 Ptrofs.zero)) = comp_of f0).
          { unfold Genv.find_comp. setoid_rewrite CALLSIG. auto. }
          exists ([Bundle_call [Event_call (comp_of f) (Genv.find_comp ge (Vptr b0 Ptrofs.zero)) i0 vl] i0 vl (fn_sig f0) None]). eexists. split.
          { simpl. split; auto. econstructor 2. 2: econstructor 1. 2: eauto. eapply ir_step_cross_call_internal.
            7: eauto. 6: intros; eapply NO_CROSS_PTR; auto. 3: setoid_rewrite CALLSIG; auto. 3,4: eauto.
            { rewrite MTST1. rewrite <- EQC, H0. simpl. auto. }
            { apply Genv.invert_find_symbol; auto. }
            { econs; auto. }
          }
          rewrite H0 in RSX. simpl in RSX. inv RSX.
          eapply IH. 4: eapply STAR. all: auto.
          { ss. split.
            - econs; auto. ss. rewrite H1. auto.
            - unfold wf_regset. rewrite NEXTPC. rewrite CALLSIG. auto.
          }
          unfold match_state. splits; eauto.
          - unfold wf_ir_cur. rewrite CALLSIG. auto.
          - econs; eauto.
          - unfold match_cur_stack_sig. rewrite CALLSIG. ss.
          - unfold match_cur_regset. rewrite NEXTPC. ss.
          - econs; eauto. rewrite MTST1. rewrite H0. ss.
        }
        (* calling external function *)
        { assert (EQC2: (Genv.find_comp ge (Vptr b' Ptrofs.zero)) = comp_of e).
          { unfold Genv.find_comp. setoid_rewrite CALLSIG. auto. }
          inv EV.
          { rewrite TYPEC in H. clarify. }
          clear H. clarify. unfold update_stack_call in STUPD. des_ifs.
          { unfold Genv.type_of_call in TYPEC. rewrite NEXTPC in Heq. rewrite <- EQC in TYPEC. ss. rewrite Heq in TYPEC. inv TYPEC. }
          pose proof STAR as STAR0. move STAR after H4.
          exploit asm_to_ir_ccc_external1. eapply MTST1. eapply H0. eapply H1. eapply ALLOWED. eapply NEXTPC. all: auto. eapply CALLSIG. eapply H3. eapply H4.
          intros (cp & cp' & sg & FACT1 & FACT2 & FACT3 & FACT4 & FACT5 & FACT6 & FACT7 & FACT8). subst.
          inv STAR; ss.
          (* subcase 1 *)
          { exists ([Bundle_call [Event_call (comp_of f) (Genv.find_comp ge (Vptr b0 Ptrofs.zero)) i0 vl] i0 vl (ef_sig e) None]). eexists. ss. split; auto.
            econs 2. 2: econs 1. 2: eauto. eapply ir_step_cross_call_external1.
            8: eapply FACT8. 6: eapply FACT6. 5: eapply FACT5. 3: eapply FACT3. 2: eapply FACT2. all: eauto.
          }
          rename H into STEP, H2 into STAR, TYPEC into CCC, CALLSIG into NEXTF. inv STEP.
          1,2,3,4: rewrite NEXTPC in H6; inv H6; rewrite NEXTF in H7; inv H7.
          rewrite NEXTPC in H6; inv H6. rewrite NEXTF in H7; inv H7. ss. clear REC_CURCOMP. rename H8 into EXTCALL, H11 into EXTARGS.
          assert (NEQCP: comp_of f <> comp_of ef).
          { rewrite <- EQC2.  clear - CCC. intros CC. unfold Genv.type_of_call in CCC. rewrite CC in CCC. rewrite Pos.eqb_refl in CCC. inv CCC. }
          exploit extcall_cases. eapply ECC. eapply EXTCALL. clear ECC. rewrite <- or_assoc. intros [ECC | ECC].
          2:{ exfalso. clear - NEXTF NEQCP ALLOWED ECC. destruct ALLOWED as [A | A].
              { rewrite A in NEQCP. unfold Genv.find_comp in NEQCP. setoid_rewrite NEXTF in NEQCP. auto. }
              unfold Genv.allowed_cross_call in A. destruct A as (i & cp' & INV & OK & _). unfold Genv.find_funct_ptr in NEXTF. specialize (OK _ NEXTF).
              destruct ef; ss; clarify. des_ifs. des_ifs.
              { destruct ECC as [ECC1 ECC2]. subst. inv ECC1. }
              { destruct ECC as [ECC1 ECC2]. subst. inv ECC1. }
          }
          exploit arguments_same; eauto. intros EQ. subst args0.
          exploit match_mem_external_call_establish; eauto. intros.
          destruct x0 as (d' & m1 & m2 & res' & EFACT1 & EFACT2 & EFACT3 & (k2 & d2 & m_a02 & MM)).
          inv STAR.
          (* subcase 2 *)
          { exists ([Bundle_call ([Event_call (comp_of f) (Genv.find_comp ge (Vptr b2 Ptrofs.zero)) i0 vl] ++ t1) i0 vl (ef_sig ef) (Some d')]). eexists. split; auto.
            econs 2. 2: econs 1. 2: eauto. eapply ir_step_cross_call_external2.
            8: eapply FACT8. 6: eapply FACT6. 5: eapply FACT5. 3: eapply FACT3. 2: eapply FACT2. all: eauto.
            erewrite eventval_list_match_vals_to_eventvals; eauto.
          }
          rename H into STEP, H2 into STAR. inv STEP. ss. rewrite Pregmap.gss in *. destruct MM as [MM VAL].
          (* subcase 3 *)
          pose proof WFIR0 as CUR. unfold wf_ir_cur in CUR. des_ifs. clear CUR. rename Heq1 into CUR.
          unfold update_stack_return in STUPD. rewrite Pregmap.gss in STUPD. des_ifs.
          { exfalso. rewrite Heq0, RSX, H0 in Heq1. ss. rewrite Pos.eqb_sym, Heq in Heq1. congruence with Heq1. }
          clear PC_RA. inv EV.
          { exfalso. apply H. rewrite Heq0, RSX, H0. ss. unfold Genv.type_of_call. rewrite Heq. auto. }
          assert (RES: (return_value (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs')) # PC <- (rs' X1) (ef_sig ef)) = res).
          { exploit NO_CROSS_PTR0; auto. clear. intros NPTR.
            unfold return_value, loc_external_result in *. remember (Conventions1.loc_result (ef_sig ef)) as rpmr.
            unfold Conventions1.loc_result in Heqrpmr. des_ifs.
            ss. rewrite ! (Pregmap.gso (j:=PC)) in *; ss. rewrite ! Pregmap.gss in *. rewrite Pregmap.gso, Pregmap.gss in *; ss.
            unfold Val.longofwords, Val.hiword, Val.loword in *. des_ifs.
            rewrite Int64.ofwords_recompose. auto.
          }
          eapply asm_to_ir_compose.
          2:{ instantiate (1:=t3). rewrite app_comm_cons. setoid_rewrite app_assoc. eauto. }
          exists ([Bundle_call ([Event_call (comp_of f) (Genv.find_comp ge (Vptr b2 Ptrofs.zero)) i0 vl] ++ t1 ++ [Event_return (Genv.find_comp_ignore_offset ge (rs' X1)) (Genv.find_comp_ignore_offset ge (rs' PC)) res0]) i0 vl (ef_sig ef) (Some d')]). eexists. split.
          { split; auto.
            { ss. rewrite app_nil_r. auto. }
            econstructor 2. 2: econstructor 1. 2: eauto. eapply ir_step_cross_call_external3.
            8: eapply FACT8. 6: eapply FACT6. 5: eapply FACT5. 3: eapply NEXTF. 2: eapply FACT2. all: eauto.
            { erewrite eventval_list_match_vals_to_eventvals; eauto. }
            { intros. exploit NO_CROSS_PTR0; auto. rewrite RES. clear - VAL. intros. destruct VAL as [VAL | VAL].
              - pose proof Val.inject_list_not_ptr. specialize (H k2 [res] [res']). exploit H. econs; eauto. econs; eauto. intros. inv x1. auto.
              - subst; auto.
            }
            { econs; eauto.
              - setoid_rewrite MTST1. rewrite H0. ss. unfold Genv.find_comp. setoid_rewrite H1. clear - NEQCP.
                unfold Genv.type_of_call. rewrite <- Pos.eqb_neq in NEQCP. setoid_rewrite NEQCP. auto.
              - instantiate (1:=res0). rewrite RES in H2, NO_CROSS_PTR0. exploit NO_CROSS_PTR0; auto. intros NPTR.
                clear - H2 NPTR VAL. destruct VAL as [VAL | VAL]; subst; auto. remember (proj_rettype (sig_res (ef_sig ef))) as ty. clear dependent ef.
                inv VAL; ss; eauto.
              - f_equal. f_equal. rewrite Heq0, RSX. rewrite MTST1, H0. ss. rewrite NEXTPC. ss.
            }
          }
          rewrite H0 in RSX. ss. inv RSX. eapply IH. 4: eapply STAR. all: auto.
          { ss. splits; auto. unfold wf_regset in *. rewrite Pregmap.gss. rewrite Heq0. rewrite H1. auto. }
          { ss. splits; auto.
            - unfold match_cur_regset in *. rewrite Pregmap.gss. rewrite Heq0. rewrite MTST1. rewrite H0. ss.
            - eauto.
          }
        }
      }

    - (** internal_return *)
      destruct ist as [[[cur m_i] ik] |]; ss.
      destruct MTST as (WFIR0 & WFIR1 & MTST0 & MTST1 & MTST2 & MTST3).
      destruct WFASM as [WFASM0 WFASM1].
      inv STAR.
      { end_case. }
      rename H into STEP, H5 into STAR.
      exploit exec_instr_is_return. eapply H3. auto. intros ((v & NEXTPC) & TEMP). subst m'.
      eapply asm_to_ir_returnstate. 2: eapply IH. 11: eapply STAR. 10: eapply STEP.
      all: eauto.
      { rewrite <- REC_CURCOMP. apply MTST1. }

    - (** return *)
      exfalso. unfold wf_asm in WFASM. contradiction WFASM.

    - (** builtin  *)
      destruct ist as [[[cur m_i] ik] |]; ss.
      exploit asm_to_ir_builtin; eauto.
      destruct MTST as (WFIR0 & WFIR1 & MTST0 & MTST1 & MTST2 & MTST3).
      clear dependent k. clear dependent d. clear dependent m_a0.
      intros (btr1 & k & d & m_a & m_i' & UTR1 & ISTAR1 & MEM).
      eapply asm_to_ir_compose. 2: eauto. exists btr1. eexists. split.
      { split; eauto. }
      clear dependent btr1. clear dependent m_i. rename m_i' into m_i.
      destruct WFASM as [WFASM0 WFASM1].
      remember (nextinstr (set_res (map_builtin_res preg_of res) vres (undef_regs (map preg_of (destroyed_by_builtin ef)) (rs # X1 <- Vundef) # X31 <- Vundef))) as rs'.
      assert (NEXTPC: rs' PC = Val.offset_ptr (rs PC) Ptrofs.one).
      { subst rs'. clear. unfold nextinstr. simpl.
        rewrite Pregmap.gss. f_equal. rewrite ! Asmgenproof0.set_res_other; ss.
        rewrite Asmgenproof0.undef_regs_other_2.
        rewrite Pregmap.gso. rewrite Pregmap.gso. all: ss; auto.
        rewrite Asmgenproof0.preg_notin_charact. intros. destruct mr; ss.
      }
      eapply IH. 4: eapply STAR. all: auto.
      { simpl. split; auto. unfold wf_regset in *. rewrite NEXTPC, H0. simpl. rewrite H1. auto. }
      { simpl. splits. 6: eapply MEM. all: auto. unfold match_cur_regset in *.
        rewrite NEXTPC, H0. ss. rewrite MTST1, H0. ss.
      }

    - (** external *)
      exfalso. destruct WFASM as [WFASM0 WFASM1]. unfold wf_regset in WFASM1.
      rewrite H0 in WFASM1. rewrite H1 in WFASM1. contradiction WFASM1.

  Qed.

End PROOF.
