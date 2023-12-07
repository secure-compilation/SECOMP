Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.


Section GENV.

  Context {F: Type}.
  Context {V: Type}.

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

  (* Lemma genv_def_to_ident *)
  (*       (p: AST.program F V) *)
  (*       (NR: list_norepet (prog_defs_names p)) *)
  (*       ge *)
  (*       (GE: ge = Genv.globalenv p) *)
  (*       b gd *)
  (*       (DEF: Genv.find_def ge b = Some gd) *)
  (*   : *)
  (*   exists id, Genv.invert_symbol ge b = Some id. *)
  (* Proof. *)
  (*   subst ge. unfold Genv.globalenv, Genv.add_globals, prog_defs_names in *. *)
  (*   destruct p; simpl in *. clear - NR DEF. *)
  (*   remember (Genv.empty_genv F V prog_public prog_pol) as ge. *)
  (*   replace (fold_left (Genv.add_global (V:=V)) prog_defs ge) with *)
  (*     (fold_right (fun ig g => Genv.add_global g ig) ge (rev prog_defs)) in *. *)
  (*   2:{ rewrite fold_left_rev_right. f_equal. } *)
  (*   remember (rev prog_defs) as rev_prog_defs. *)
  (*   assert (RNR: list_norepet (map fst rev_prog_defs)). *)
  (*   { subst. rewrite map_rev. apply list_norepet_rev; auto. } *)
  (*   clear prog_defs NR Heqrev_prog_defs. subst ge. *)
  (*   revert prog_public prog_pol b gd DEF RNR. *)
  (*   induction rev_prog_defs; intros. *)
  (*   { unfold Genv.find_def in DEF. simpl in DEF. rewrite PTree.gempty in DEF. congruence. } *)
  (*   destruct a as [id0 gd0]. *)
  (*   simpl in *. specialize (IHrev_prog_defs prog_public prog_pol). *)
  (*   remember (fold_right (fun (ig : ident * globdef F V) (g : Genv.t F V) => Genv.add_global g ig) (Genv.empty_genv F V prog_public prog_pol) rev_prog_defs) as ge. *)
  (*   assert (GE: ge = Genv.globalenv (AST.mkprogram (rev rev_prog_defs) prog_public id0 prog_pol)). *)
  (*   { subst ge. unfold Genv.globalenv. unfold Genv.add_globals. simpl. *)
  (*     rewrite <- fold_left_rev_right. rewrite rev_involutive. auto. } *)
  (*   apply genv_find_def_add_global_spec in DEF. *)
  (*   { destruct DEF as [[BLK GD] | [BLK GD]]. *)
  (*     - subst b gd0. exists id0. *)
  (*       apply Genv.find_invert_symbol. unfold Genv.find_symbol, Genv.add_global; simpl. *)
  (*       rewrite PTree.gss. auto. *)
  (*     - inversion RNR; clear RNR. subst hd tl. specialize (IHrev_prog_defs _ _ GD H2). *)
  (*       destruct IHrev_prog_defs as [id' INV]. exists id'. *)
  (*       apply Genv.find_invert_symbol. unfold Genv.find_symbol, Genv.add_global; simpl. *)
  (*       rewrite PTree.gso. apply Genv.invert_find_symbol in INV. auto. *)
  (*       clear - H1 Heqge INV GE. apply Genv.invert_find_symbol in INV. *)
  (*       rewrite GE in INV. apply Genv.find_symbol_inversion in INV. *)
  (*       unfold prog_defs_names in INV. simpl in INV. *)
  (*       rewrite map_rev in INV. apply in_rev in INV. intros CONTRA. subst id'. auto. *)
  (*   } *)
  (*   { destruct (Genv.find_symbol ge id0) eqn:CASE; auto. exfalso. *)
  (*     rewrite GE in CASE. apply Genv.find_symbol_inversion in CASE. *)
  (*     unfold prog_defs_names in CASE. simpl in CASE. rewrite map_rev in CASE. apply in_rev in CASE. *)
  (*     clear - CASE RNR. inversion RNR. auto. *)
  (*   } *)
  (* Qed. *)

End GENV.


Section MEM.

  (* f doesn't map anything to [b], e.g. the counter and function parameters *)
  Definition meminj_notmap (f: meminj) b := forall b0 ofs0, ~ (f b0 = Some (b, ofs0)).

  Lemma loc_out_of_reach_unchanged_on_content:
    forall f b ofs m1 m1' m2'
      (NOTMAP: meminj_notmap f b),
      Mem.perm m1' b ofs Cur Readable ->
      Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ->
      ZMap.get ofs (Mem.mem_contents m2') !! b = ZMap.get ofs (Mem.mem_contents m1') !! b.
  Proof.
    intros. destruct H0. apply unchanged_on_contents; eauto.
    unfold loc_out_of_reach. intros. now specialize (NOTMAP _ _ H0).
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

End MEM.

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
