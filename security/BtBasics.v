Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Record syscall_properties (sem: extcall_sem) (sg: signature) : Prop :=
  mk_syscall_properties {
      sc_args_match:
      forall ge cp args m1 name evargs evres res m2,
        sem ge cp args m1 (Event_syscall name evargs evres :: nil) res m2 ->
        eventval_list_match ge evargs sg.(sig_args) args;
    }.


Section GENV.

  Context {F: Type}.
  Context {V: Type}.

  (* For NR, use below: *)
  (* ::: mkpass Unusedglobproof.match_prog *)
  (* match_prog_unique: *)
  (*   list_norepet (prog_defs_names tp) *)
  Lemma genv_def_to_some_ident
        (p: AST.program F V)
        (NR: list_norepet (prog_defs_names p))
        ge
        (GE: ge = Genv.globalenv p)
        b gd
        (DEF: Genv.find_def ge b = Some gd)
    :
    exists id b', Genv.find_symbol ge id = Some b' /\ Genv.find_def ge b' = Some gd.
  Proof.
    subst ge. exploit Genv.find_def_inversion; eauto. intros [id IN].
    assert (GET: (prog_defmap p) ! id = Some gd).
    { unfold prog_defmap. unfold prog_defs_names in NR. apply PTree_Properties.of_list_norepet; auto. }
    apply Genv.find_def_symbol in GET. destruct GET as [b' [FINDSYM FINDDEF]]. eauto.
  Qed.

  Lemma genv_find_def_add_global_spec
        (ge: Genv.t F V) id gd
        (NEW: Genv.find_symbol ge id = None)
        b gd'
        (ADD: Genv.find_def (Genv.add_global ge (id, gd)) b = Some gd')
    :
    ((b = (Genv.genv_next ge)) /\ (gd' = gd)) \/
      ((b <> (Genv.genv_next ge)) /\ (Genv.find_def ge b = Some gd')).
  Proof.
    destruct (Pos.eqb_spec b (Genv.genv_next ge)).
    - left; split; auto.
      unfold Genv.find_def, Genv.add_global in ADD. subst; simpl in *.
      rewrite PTree.gss in ADD. inversion ADD; auto.
    - right; split; auto.
      unfold Genv.find_def, Genv.add_global in ADD. simpl in *.
      rewrite PTree.gso in ADD; auto.
  Qed.

  Lemma genv_def_to_ident
        (p: AST.program F V)
        (NR: list_norepet (prog_defs_names p))
        ge
        (GE: ge = Genv.globalenv p)
        b gd
        (DEF: Genv.find_def ge b = Some gd)
    :
    exists id, Genv.invert_symbol ge b = Some id.
  Proof.
    subst ge. unfold Genv.globalenv, Genv.add_globals, prog_defs_names in *.
    destruct p; simpl in *. clear - NR DEF.
    remember (Genv.empty_genv F V prog_public prog_pol) as ge.
    replace (fold_left (Genv.add_global (V:=V)) prog_defs ge) with
      (fold_right (fun ig g => Genv.add_global g ig) ge (rev prog_defs)) in *.
    2:{ rewrite fold_left_rev_right. f_equal. }
    remember (rev prog_defs) as rev_prog_defs.
    assert (RNR: list_norepet (map fst rev_prog_defs)).
    { subst. rewrite map_rev. apply list_norepet_rev; auto. }
    clear prog_defs NR Heqrev_prog_defs. subst ge.
    revert prog_public prog_pol b gd DEF RNR.
    induction rev_prog_defs; intros.
    { unfold Genv.find_def in DEF. simpl in DEF. rewrite PTree.gempty in DEF. congruence. }
    destruct a as [id0 gd0].
    simpl in *. specialize (IHrev_prog_defs prog_public prog_pol).
    remember (fold_right (fun (ig : ident * globdef F V) (g : Genv.t F V) => Genv.add_global g ig) (Genv.empty_genv F V prog_public prog_pol) rev_prog_defs) as ge.
    assert (GE: ge = Genv.globalenv (AST.mkprogram (rev rev_prog_defs) prog_public id0 prog_pol)).
    { subst ge. unfold Genv.globalenv. unfold Genv.add_globals. simpl.
      rewrite <- fold_left_rev_right. rewrite rev_involutive. auto. }
    apply genv_find_def_add_global_spec in DEF.
    { destruct DEF as [[BLK GD] | [BLK GD]].
      - subst b gd0. exists id0.
        apply Genv.find_invert_symbol. unfold Genv.find_symbol, Genv.add_global; simpl.
        rewrite PTree.gss. auto.
      - inversion RNR; clear RNR. subst hd tl. specialize (IHrev_prog_defs _ _ GD H2).
        destruct IHrev_prog_defs as [id' INV]. exists id'.
        apply Genv.find_invert_symbol. unfold Genv.find_symbol, Genv.add_global; simpl.
        rewrite PTree.gso. apply Genv.invert_find_symbol in INV. auto.
        clear - H1 Heqge INV GE. apply Genv.invert_find_symbol in INV.
        rewrite GE in INV. apply Genv.find_symbol_inversion in INV.
        unfold prog_defs_names in INV. simpl in INV.
        rewrite map_rev in INV. apply in_rev in INV. intros CONTRA. subst id'. auto.
    }
    { destruct (Genv.find_symbol ge id0) eqn:CASE; auto. exfalso.
      rewrite GE in CASE. apply Genv.find_symbol_inversion in CASE.
      unfold prog_defs_names in CASE. simpl in CASE. rewrite map_rev in CASE. apply in_rev in CASE.
      clear - CASE RNR. inversion RNR. auto.
    }
  Qed.

End GENV.


Section MEM.

  (* f doesn't map anything to [b], e.g. the counter and function parameters *)
  Definition meminj_notmap (f: meminj) b := forall b0 ofs0, ~ (f b0 = Some (b, ofs0)).

  Lemma loc_out_of_reach_unchanged_on_content:
    forall f b ofs m1 m1' m2'
      (NOTMAP: meminj_notmap f b),
      Mem.perm m1' b ofs Cur Readable ->
      (* Mem.perm m1' b ofs Cur Writable -> *)
      Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ->
      ZMap.get ofs (Mem.mem_contents m2') !! b = ZMap.get ofs (Mem.mem_contents m1') !! b.
  Proof.
    intros. destruct H0. apply unchanged_on_contents; eauto.
    unfold loc_out_of_reach. intros. now specialize (NOTMAP _ _ H0).
    (* eapply Mem.perm_implies; eauto. constructor. *)
  Qed.

  Lemma loc_out_of_reach_unchanged_on_perm:
    forall f b ofs m1 m1' m2' k p
      (NOTMAP: meminj_notmap f b),
      Mem.perm m1' b ofs k p ->
      Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ->
      Mem.perm m2' b ofs k p.
  Proof.
    intros. destruct H0. apply unchanged_on_perm; eauto.
    unfold loc_out_of_reach. intros. now specialize (NOTMAP _ _ H0).
    eapply Mem.perm_valid_block; eauto.
  Qed.

  (* Record unchanged_on (P : block -> Z -> Prop) (m_before m_after : mem) : Prop := mk_unchanged_on *)
  (* { unchanged_on_nextblock : Ple (Mem.nextblock m_before) (Mem.nextblock m_after); *)
  (*   unchanged_on_perm : forall (b : block) (ofs : Z) (k : perm_kind) (p : permission), P b ofs -> Mem.valid_block m_before b -> Mem.perm m_before b ofs k p <-> Mem.perm m_after b ofs k p; *)
  (*   unchanged_on_contents : forall (b : block) (ofs : Z), P b ofs -> Mem.perm m_before b ofs Cur Readable -> ZMap.get ofs (Mem.mem_contents m_after) !! b = ZMap.get ofs (Mem.mem_contents m_before) !! b; *)
  (*   unchanged_on_own : forall (b : block) (cp : option compartment), Mem.valid_block m_before b -> Mem.can_access_block m_before b cp <-> Mem.can_access_block m_after b cp }. *)

  Lemma inject_separated_notmap
        f f' m m' b
        (NM: meminj_notmap f b)
        (VALID: Mem.valid_block m' b)
        (* (INJ: Mem.inject f m m') *)
        (INCR: inject_incr f f')
        (SEP: inject_separated f f' m m')
    :
    meminj_notmap f' b.
  Proof.
    unfold meminj_notmap, inject_incr, inject_separated in *.
    intros. intros CONTRA. specialize (NM b0 ofs0). destruct (f b0) eqn:FB.
    { destruct p. specialize (INCR _ _ _ FB). rewrite CONTRA in INCR. inversion INCR; clear INCR; subst. congruence. }
    specialize (SEP _ _ _ FB CONTRA). destruct SEP as [NV1 NV2]. congruence.
  Qed.

(*
forall b, b is the block of one of the counter ->
     (forall b0 ofs, ~ (f b0 = Some (b, ofs)))
 *)

  (** Events.v **)
(* (** External calls must commute with memory injections, *)
 (*   in the following sense. *) *)
  (*   ec_mem_inject: *)
  (*     forall ge1 ge2 c vargs m1 t vres m2 f m1' vargs', *)
  (*     symbols_inject f ge1 ge2 -> *)
  (*     sem ge1 c vargs m1 t vres m2 -> *)
  (*     Mem.inject f m1 m1' -> *)
  (*     Val.inject_list f vargs vargs' -> *)
  (*     exists f', exists vres', exists m2', *)
  (*        sem ge2 c vargs' m1' t vres' m2' *)
  (*     /\ Val.inject f' vres vres' *)
  (*     /\ Mem.inject f' m2 m2' *)
  (*     /\ Mem.unchanged_on (loc_unmapped f) m1 m2 *)
  (*     /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' *)
  (*     /\ inject_incr f f' *)
  (*     /\ inject_separated f f' m1 m1'; *)

End MEM.

Section EXTCALL.

  Variant external_call_event_match_common
          (ef: external_function) (ev: event) (ge: Senv.t) (cp: compartment) (m1: mem)
    : val -> mem -> Prop :=
    | ext_match_vload
        ch
        (EF: ef = EF_vload ch)
        id ofs evv
        (EV: ev = Event_vload ch id ofs evv)
        b res m2
        (SEM: volatile_load_sem ch ge cp (Vptr b ofs :: nil) m1 (ev :: nil) res m2)
      :
      external_call_event_match_common ef ev ge cp m1 res m2
    | ext_match_vstore
        ch
        (EF: ef = EF_vstore ch)
        id ofs evv
        (EV: ev = Event_vstore ch id ofs evv)
        b argv m2
        (SEM: volatile_store_sem ch ge cp (Vptr b ofs :: argv :: nil) m1 (ev :: nil) Vundef m2)
      :
      external_call_event_match_common ef ev ge cp m1 Vundef m2
    | ext_match_annot
        len text targs
        (EF: ef = EF_annot len text targs)
        evargs
        (EV: ev = Event_annot text evargs)
        vargs m2
        (SEM: extcall_annot_sem text targs ge cp vargs m1 (ev :: nil) Vundef m2)
      :
      external_call_event_match_common ef ev ge cp m1 Vundef m2
    | ext_match_external
        name excp sg
        (EF: ef = EF_external name excp sg)
        evname evargs evres
        (EV: ev = Event_syscall evname evargs evres)
        vargs vres m2
        (SEM: external_functions_sem name sg ge cp vargs m1 (ev :: nil) vres m2)
        (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs)
      :
      external_call_event_match_common ef ev ge cp m1 vres m2
    | ext_match_builtin
        name sg
        (EF: (ef = EF_builtin name sg) \/ (ef = EF_runtime name sg))
        evname evargs evres
        (EV: ev = Event_syscall evname evargs evres)
        (ISEXT: Builtins.lookup_builtin_function name sg = None)
        vargs vres m2
        (SEM: external_functions_sem name sg ge cp vargs m1 (ev :: nil) vres m2)
        (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs)
      :
      external_call_event_match_common ef ev ge cp m1 vres m2
    | ext_match_inline_asm
        txt sg strs
        (EF: ef = EF_inline_asm txt sg strs)
        evname evargs evres
        (EV: ev = Event_syscall evname evargs evres)
        vargs vres m2
        (SEM: inline_assembly_sem txt sg ge cp vargs m1 (ev :: nil) vres m2)
        (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs)
      :
      external_call_event_match_common ef ev ge cp m1 vres m2
  .

End EXTCALL.
