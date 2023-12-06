Require Import Coqlib Maps Errors Integers.
Require Import Integers Floats AST Linking.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.
Require Import Op Locations Mach Conventions Asm.
Require Import Complements.

Require Import Split.

Print Instances has_side.

Variant match_fundef: fundef -> fundef -> Prop :=
  | match_fundef_internal:
    forall cp sig code code',
      match_fundef (Internal {| fn_comp := cp; fn_sig := sig; fn_code := code |})
        (Internal {| fn_comp := cp; fn_sig := sig; fn_code := code' |})
  | match_fundef_external:
    forall ef,
      match_fundef (External ef) (External ef)
.

#[local] Instance has_comp_match_fundef (A: Type): has_comp_match (fun _:A => match_fundef).
intros ? x y H.
inv H; auto.
Qed.

Definition match_varinfo (_ _: unit) := True.

Variant match_globdef: globdef fundef unit -> globdef fundef unit -> Prop :=
  | match_globdef_fundef: forall f f',
      match_fundef f f' ->
      match_globdef (Gfun f) (Gfun f')
  | match_globdef_varinfo: forall v v',
      match_globvar match_varinfo v v' ->
      match_globdef (Gvar v) (Gvar v')
.

Remark match_globdef_refl: forall gd,
    match_globdef gd gd.
Proof.
  intros [[[] |]| []]; repeat constructor.
Qed.

Definition kept_genv (s: split) (ge: genv) (δ: side) (id: ident): bool :=
  match Genv.find_symbol ge id with
  | Some b =>
      match (Genv.genv_defs ge)!b with
      | None => false
      | Some gd => side_eq (s (comp_of gd)) δ
      end
  | None => false
  end.

Definition kept_prog (s: split) (p: program) (δ: side) (id: ident): bool :=
  kept_genv s (Genv.globalenv p) δ id.

Record match_prog (s: split) (δ: side) (p p__recomp: program): Prop := {
    match_prog_main:
    p__recomp.(prog_main) = p.(prog_main);
    match_prog_public:
    p__recomp.(prog_public) = p.(prog_public);
    match_prog_pol:
    p__recomp.(prog_pol) = p.(prog_pol);
    match_prog_def:
    forall id,
      kept_prog s p δ id = true ->
      (prog_defmap p__recomp)!id = (prog_defmap p)!id;
    match_prog_notdef:
    forall id,
      kept_prog s p δ id = false ->
      option_rel match_globdef (prog_defmap p)!id (prog_defmap p__recomp)!id ;
    (* This means that anything defined as public must be defined both in [p] and [p__recomp] *)
    match_prog_unique:
    list_norepet (prog_defs_names p__recomp)
  }.

Section MEMINJ.

  Variable s: split.
  Variable δ: side.

  Variable p p__recomp: program.
  Hypothesis MATCH: match_prog s δ p p__recomp.


  Let ge := (Genv.globalenv p).
  Let ge__recomp := (Genv.globalenv p__recomp).

  Lemma transform_find_symbol_1:
    forall id b,
      Genv.find_symbol ge id = Some b ->
      exists b', Genv.find_symbol ge__recomp id = Some b'.
  Proof.
    intros id b H.
    assert (A: exists g, (prog_defmap p)!id = Some g).
    { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
    destruct A as (g & P).
    destruct (kept_prog s p δ id) eqn:ktept.
    - apply Genv.find_symbol_exists with g.
      apply in_prog_defmap.
      erewrite match_prog_def by eauto. auto.
    - exploit match_prog_notdef; eauto.
      intros G; inv G; try congruence.
      eapply Genv.find_symbol_exists.
      apply in_prog_defmap; eauto.
  Qed.

  Lemma transform_find_symbol_2:
    forall id b,
      Genv.find_symbol ge__recomp id = Some b ->
      exists b', Genv.find_symbol ge id = Some b'.
  Proof.
    intros id b H.
    assert (A: exists g, (prog_defmap p__recomp)!id = Some g).
    { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
    destruct A as (g & P).
    destruct (kept_genv s ge δ id) eqn:kept.
    - erewrite match_prog_def in P by eauto.
      apply Genv.find_symbol_exists with g.
      apply in_prog_defmap. auto.
    - exploit match_prog_notdef; eauto.
      intros G; inv G; try congruence.
      eapply Genv.find_symbol_exists.
      apply in_prog_defmap; eauto.
  Qed.

  Lemma match_prog_comp_of_main:
    comp_of_main p__recomp = comp_of_main p.
  Proof.
  Admitted.


  (** Injections that preserve used globals. *)
  Record meminj_preserves_globals (j: meminj): Prop := {
      symbols_inject1: forall id b b' delta,
        j b = Some (b', delta) ->
        Genv.find_symbol ge id = Some b ->
        delta = 0 /\ Genv.find_symbol ge__recomp id = Some b';
      symbols_inject2: forall id b,
        Genv.find_symbol ge id = Some b ->
        exists b', Genv.find_symbol ge__recomp id = Some b' /\ j b = Some(b', 0);
      symbols_inject3: forall id b',
        Genv.find_symbol ge__recomp id = Some b' ->
        exists b, Genv.find_symbol ge id = Some b /\ j b = Some (b', 0);
      defs_inject: forall b b' delta gd,
        j b = Some(b', delta) -> Genv.find_def ge b = Some gd ->
        exists gd', Genv.find_def ge__recomp b' = Some gd' /\
                 delta = 0 /\
                 match_globdef gd gd' /\
                 (forall id, Genv.find_symbol ge id = Some b -> kept_genv s ge δ id = true ->
                        gd' = gd);
      defs_rev_inject: forall b b' delta gd,
        j b = Some(b', delta) -> Genv.find_def ge__recomp b' = Some gd ->
        exists gd', Genv.find_def ge b = Some gd' /\ delta = 0 /\ match_globdef gd' gd;
    }.

  Definition init_meminj: meminj :=
    fun b =>
      match Genv.invert_symbol ge b with
      | Some id =>
          match Genv.find_symbol ge__recomp id with
          | Some b' => Some (b', 0)
          | None => None
          end
      | None => None
      end.

  Remark init_meminj_eq:
    forall id b b',
      Genv.find_symbol ge id = Some b -> Genv.find_symbol ge__recomp id = Some b' ->
      init_meminj b = Some(b', 0).
  Proof.
    intros. unfold init_meminj. erewrite Genv.find_invert_symbol by eauto.
    rewrite H0. auto.
  Qed.

  Remark init_meminj_invert:
    forall b b' delta,
      init_meminj b = Some(b', delta) ->
      delta = 0 /\ exists id, Genv.find_symbol ge id = Some b /\ Genv.find_symbol ge__recomp id = Some b'.
  Proof.
    unfold init_meminj; intros.
    destruct (Genv.invert_symbol ge b) as [id|] eqn:S; try discriminate.
    destruct (Genv.find_symbol ge__recomp id) as [b''|] eqn:F; inv H.
    split. auto. exists id. split. apply Genv.invert_find_symbol; auto. auto.
  Qed.

  Lemma init_meminj_preserves_globals:
    meminj_preserves_globals init_meminj.
  Proof.
    constructor; intros.
    - exploit init_meminj_invert; eauto. intros (A & id1 & B & C).
      assert (id1 = id) by (eapply (Genv.genv_vars_inj ge); eauto). subst id1.
      auto.
    - exploit transform_find_symbol_1; eauto. intros (b' & F). exists b'; split; auto.
      eapply init_meminj_eq; eauto.
    - exploit transform_find_symbol_2; eauto. intros (b & F).
      exists b; split; auto. eapply init_meminj_eq; eauto.
    - exploit init_meminj_invert; eauto. intros (A & id & B & C).
      destruct (kept_genv s ge δ id) eqn:kept.
      + assert ((prog_defmap p)!id = Some gd).
        { rewrite Genv.find_def_symbol. exists b; auto. }
        assert ((prog_defmap p__recomp)!id = Some gd).
        { erewrite match_prog_def by eauto. auto. }
        rewrite Genv.find_def_symbol in H2. destruct H2 as (b1 & P & Q).
        fold ge__recomp in P. replace b' with b1 by congruence.
        exists gd. split; auto. split; auto. split; auto.
        apply match_globdef_refl.
      + assert ((prog_defmap p)!id = Some gd).
        { rewrite Genv.find_def_symbol. exists b; auto. }
        exploit match_prog_notdef; eauto.
        intros G; inv G; try congruence.
        assert (x = gd) by congruence; subst x.
        symmetry in H3. rewrite Genv.find_def_symbol in H3. destruct H3 as (b1 & P & Q).
        fold ge__recomp in P. replace b' with b1 by congruence.
        eexists. split; eauto. split; auto. split; auto.
        intros id' D. apply Genv.find_invert_symbol in B, D.
        assert (id = id') by congruence; subst id'. congruence.
    - exploit init_meminj_invert; eauto. intros (A & id & B & C).
      destruct (kept_genv s ge δ id) eqn:kept.
      + assert ((prog_defmap p__recomp)!id = Some gd).
        { rewrite Genv.find_def_symbol. exists b'; auto. }
        exists gd; split; [| split]; auto using match_globdef_refl.
        erewrite match_prog_def in H1 by eauto.
        rewrite Genv.find_def_symbol in H1. destruct H1 as (b1 & P & Q).
        fold ge in P. replace b with b1 by congruence. auto.
      + pose proof Genv.find_def_symbol as F.
        exploit Genv.find_symbol_find_def_inversion; eauto.
        intros (gd_recomp & find_gd_recomp).
        exploit Genv.find_symbol_find_def_inversion; [exact B|].
        intros (gd_base & find_gd_base).
        assert (H1: exists b, Genv.find_symbol (Genv.globalenv p) id = Some b /\
                           Genv.find_def (Genv.globalenv p) b = Some gd_base) by eauto.
        assert (H2: exists b, Genv.find_symbol (Genv.globalenv p__recomp) id = Some b /\
                           Genv.find_def (Genv.globalenv p__recomp) b = Some gd_recomp) by eauto.
        apply F in H1, H2.
        assert (gd = gd_recomp) by (unfold ge__recomp in *; congruence). subst gd_recomp.
        eexists; split; [| split]; eauto.
        exploit match_prog_notdef; eauto. rewrite H1, H2; intros D.
        inv D; auto.
  Qed.

  Lemma symbol_address_inject:
    forall j id ofs,
      meminj_preserves_globals j ->
      Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address ge__recomp id ofs).
  Proof.
    intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    exploit symbols_inject2; eauto. intros (b' & TFS & INJ). rewrite TFS.
    econstructor; eauto. rewrite Ptrofs.add_zero; auto.
  Qed.

  Lemma globals_symbols_inject:
    forall j, meminj_preserves_globals j -> symbols_inject j ge ge__recomp.
  Proof.
    intros.
    assert (E1: Genv.genv_public ge = p.(prog_public)).
    { unfold ge. apply Genv.globalenv_public. }
    assert (E2: Genv.genv_public ge__recomp = p.(prog_public)).
    { unfold ge__recomp; rewrite Genv.globalenv_public. eapply match_prog_public; eauto. }
    split; [|split;[|split]]; intros.
    + simpl; unfold Genv.public_symbol; rewrite E1, E2.
      destruct (Genv.find_symbol ge__recomp id) as [b'|] eqn:TFS.
      exploit symbols_inject3; eauto. intros (b & FS & INJ). rewrite FS. auto.
      destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
      destruct (in_dec ident_eq id (prog_public p)); simpl; auto.
      exploit symbols_inject2; eauto.
      intros (b' & TFS' & INJ). congruence.
    + eapply symbols_inject1; eauto.
    + simpl in *; unfold Genv.public_symbol in H0.
      destruct (Genv.find_symbol ge id) as [b|] eqn:FS; try discriminate.
      rewrite E1 in H0.
      destruct (in_dec ident_eq id (prog_public p)); try discriminate. inv H1.
      exploit symbols_inject2; eauto.
      intros (b' & A & B); exists b'; auto.
    + simpl. unfold Genv.block_is_volatile.
      destruct (Genv.find_var_info ge b1) as [[c gv]|] eqn:V1.
      rewrite Genv.find_var_info_iff in V1.
      exploit defs_inject; eauto. intros (gd & A & B & C & D).
      inv C. inv H2.
      rewrite <- Genv.find_var_info_iff in A. rewrite A; auto.
      destruct (Genv.find_var_info ge__recomp b2) as [[c gv]|] eqn:V2; auto.
      rewrite Genv.find_var_info_iff in V2.
      exploit defs_rev_inject; eauto. intros (gd & A & B & C).
      inv C.
      rewrite <- Genv.find_var_info_iff in A. congruence.
  Qed.

End MEMINJ.
Section Invariants.
  Variable s: split.
  Variable cp_main: compartment.

  Definition regset_rel (j: meminj) (rs rs': regset): Prop :=
    forall r, Val.inject j (rs r) (rs' r).

  (* idea: we maintain a single injection that is only defined on the elements of δ.
This injection is going to be trivially preserved, because from elements of δ one cannot
obtain elements of (opposite δ) from it.

Then, at crossing points we will rely on globals only containing scalars to reconstruct
a bigger injection using mem_inj_disjoint_union. This injection will satisfy
meminj_preserves_globals which will allow us to prove preservation of events.
   *)
  Definition same_domain (s: split) (ge: genv) (j: meminj) (δ: side) (m: mem): Prop :=
    forall b, (j b <> None <-> ((s, m) |= b ∈ δ) \/ exists fd, Genv.find_def ge b = Some (Gfun fd)).

  Definition mem_delta_zero (j: meminj): Prop :=
    forall loc loc' delta, j loc = Some (loc', delta) -> delta = 0.

  Record mem_rel (ge1 ge2: genv) (j: meminj) (δ: side) (m1 m2: mem) :=
    { (* Uncomment as needed *)
      same_dom: same_domain s ge1 j δ m1;

      partial_mem_inject: Mem.inject j m1 m2;

      delta_zero: mem_delta_zero j;

      (* pres_globals: meminj_preserves_globals ge1 j; *)
      ple_nextblock1: Ple (Senv.nextblock ge1) (Mem.nextblock m1);
      ple_nextblock2: Ple (Senv.nextblock ge2) (Mem.nextblock m2);

      (* Functions *)
      (* funct_preserved1: forall b fd, Genv.find_funct_ptr ge1 b = Some fd -> j b = Some (b, 0); *)
      (* funct_preserved2: forall b1 b2 fd, Genv.find_funct_ptr ge2 b2 = Some fd -> j b1 = Some (b2, 0) -> b1 = b2; *)
      (* Find def valid *)
      find_def_valid1: forall b gd, Genv.find_def ge1 b = Some gd -> Mem.valid_block m1 b;
      find_def_valid2: forall b gd, Genv.find_def ge2 b = Some gd -> Mem.valid_block m2 b;

      (* Functions perm *)
      find_def_perm1: forall b fd, Genv.find_def ge1 b = Some (Gfun fd) -> forall ofs, not (Mem.perm m1 b ofs Max Readable);
      find_def_perm2: forall b fd, Genv.find_def ge2 b = Some (Gfun fd) -> forall ofs, not (Mem.perm m2 b ofs Max Readable);

      same_high_half: forall id ofs,
        Val.inject j (high_half ge1 id ofs) (high_half ge2 id ofs)
    }.

  Definition def_on_addressable (ge: genv) (j: meminj) (δ: side) :=
    forall id b cp,
      Genv.find_symbol ge id = Some b ->
      s cp = δ ->
      (Genv.find_comp_of_block ge b = Some cp \/
        exists fd, Genv.find_def ge b = Some (Gfun fd)) ->
      exists b' delta, j b = Some (b', delta).

  Lemma def_on_addressable_incr:
    forall ge j j' δ,
      def_on_addressable ge j δ ->
      inject_incr j j' ->
      def_on_addressable ge j' δ.
  Proof.
    intros ge j j' δ addr incr.
    intros ? ? ? ? ? ?. exploit addr; eauto.
    intros (? & ? & G). apply incr in G. eauto.
  Qed.

  Definition agrees_with (j1 j2: meminj) :=
    forall b b' b'' delta' delta'',
      j1 b = Some (b', delta') ->
      j2 b = Some (b'', delta'') ->
      b' = b'' /\ delta' = delta''.
  
  Lemma agrees_with_incr1:
    forall j j' b1 jref,
      agrees_with j jref ->
      j' b1 = None ->
      (forall b : block, b <> b1 -> j' b = j b) ->
      agrees_with j' jref.
  Proof.
    intros j j' b1 jref agr isnone diff.
    intros ? ? ? ? ? ? ?. exploit agr; eauto.
    rewrite diff in H; eauto.
    intros ?; congruence.
  Qed.

  Lemma agrees_with_incr2:
    forall j j' b1 jref,
      agrees_with j jref ->
      jref b1 = None ->
      (forall b : block, b <> b1 -> j' b = j b) ->
      agrees_with j' jref.
  Proof.
    intros j j' b1 jref agr isnone diff.
    intros ? ? ? ? ? ? ?. exploit agr; eauto.
    rewrite diff in H; eauto.
    intros ?; congruence.
  Qed.

End Invariants.


Arguments opposite /.

Lemma store_preserves_weak:
  forall s ge1 ge3 j ch cp b ofs v m1 m1' m3,
    Mem.store ch m1 b ofs v cp = Some m1' ->
    mem_rel s ge1 ge3 j (opposite (s cp)) m1 m3 ->
    mem_rel s ge1 ge3 j (opposite (s cp)) m1' m3.
Proof.
  intros s ge1 ge3 j ch cp b ofs v m1 m1' m3 exec m1_m3.
  assert (j b = None).
  { pose proof (same_dom _ _ _ _ _ m1 m3 m1_m3 b) as dom.
    exploit Mem.store_valid_access_3; eauto. intros (_ & access_block & _).
    simpl in access_block, dom, m1_m3.
    rewrite access_block in dom.
    destruct (j b) eqn:C; auto.
    assert (H: Some p <> None) by congruence.
    apply dom in H.
    destruct H as [H | (id & H)].
    destruct (s cp); try congruence.
    Local Transparent Mem.store.
    unfold Mem.store in exec.
    destruct Mem.valid_access_dec as [[e _] | n]; try congruence.
    eapply Mem.range_perm_max in e.
    assert (sz: ofs <= ofs < ofs + size_chunk ch) by now (destruct ch; simpl; lia).
    specialize (e ofs sz).
    exploit find_def_perm1; eauto.
    eapply Mem.perm_implies; eauto; try constructor.
    now auto. }
  constructor.
  - intros b'; apply same_dom in m1_m3; specialize (m1_m3 b').
    simpl in *. erewrite Mem.store_block_compartment; eauto.
  - eapply Mem.store_unmapped_inject; eauto using partial_mem_inject.
  - eapply delta_zero; eauto.
  - erewrite Mem.nextblock_store; eauto using ple_nextblock1.
  - eapply ple_nextblock2; eauto.
  - intros. eapply Mem.store_valid_block_1; eauto using find_def_valid1.
  - intros. eapply find_def_valid2; eauto.
  - intros. eapply find_def_perm1 with (b := b0) in m1_m3; eauto.
    intros n. apply m1_m3. eapply Mem.perm_store_2; eauto.
  - intros. eapply find_def_perm2 with (b := b0) in m1_m3; eauto.
  - intros. eapply same_high_half; eauto.
Qed.

Lemma exec_store_preserves_weak:
  forall s ge1 ge3 j cp ch m1 m1' m3 rs1 rs1' rs ra ofs,
    exec_store ge1 ch rs1 m1 rs ra ofs cp = Next rs1' m1' ->
    mem_rel s ge1 ge3 j (opposite (s cp)) m1 m3 ->
    mem_rel s ge1 ge3 j (opposite (s cp)) m1' m3.
Proof.
  intros s ge1 ge3 j cp ch m1 m1' m3 rs1 rs1' rs ra ofs exec m1_m3.
  unfold exec_store in exec.
  destruct Mem.storev eqn:m1_m1'; try congruence; inv exec.
  destruct (rs1 ra); simpl in *; try congruence.
  now eapply store_preserves_weak; eauto.
Qed.

Lemma alloc_preserves_weak:
  forall s δ W1 (_: list_norepet (prog_defs_names W1)) W3 j cp lo hi m1 m1' b1 m3,
    Mem.alloc m1 cp lo hi = (m1', b1) ->
    agrees_with j (init_meminj W1 W3) ->
    def_on_addressable s (Genv.globalenv W1) j δ ->
    mem_rel s (Genv.globalenv W1) (Genv.globalenv W3) j (opposite (s cp)) m1 m3 ->
    exists j',
    agrees_with j' (init_meminj W1 W3) /\
    def_on_addressable s (Genv.globalenv W1) j' δ /\
      mem_rel s (Genv.globalenv W1) (Genv.globalenv W3) j' (opposite (s cp)) m1' m3 /\ inject_incr j j'.
Proof.
  intros s δ W1 norepet1 W3 j cp lo hi m1 m1' b1 m3 exec agr addr m1_m3.
  exploit Mem.alloc_left_unmapped_inject; eauto using partial_mem_inject.
  intros (j' & m1'_m3 & incr & j'_b1 & same_inj).
  exists j'. split; [| split; [| split]]; auto.
  now eapply agrees_with_incr1; eauto.
  now eapply def_on_addressable_incr; eauto.
  constructor.
  - intros b; apply same_dom in m1_m3; specialize (m1_m3 b).
    simpl in *.
    erewrite Mem.alloc_block_compartment; eauto.
    destruct eq_block; try congruence; [| rewrite same_inj; auto].
    subst b1. rewrite j'_b1.
    assert (H: j b = None).
    { destruct (j b) as [[]|] eqn:?; auto.
      exploit incr; eauto. congruence. }
    rewrite H in m1_m3.
    destruct (s cp); simpl in *; intuition congruence.
  - auto.
  - intros b b' delta.
    destruct (eq_block b b1); try congruence.
    rewrite same_inj; eauto.
    eapply delta_zero; eauto.
  - apply ple_nextblock1 in m1_m3. erewrite Mem.nextblock_alloc; eauto using ple_nextblock1.
    eapply Ple_trans; eauto using Ple_succ.
  - eapply ple_nextblock2; eauto.
  - intros. eapply Mem.valid_block_alloc; eauto using find_def_valid1.
  - intros. eapply find_def_valid2; eauto.
  - intros.
    pose proof (ple_nextblock1 _ _ _ _ _ m1 m3 m1_m3) as ple.
    eapply find_def_perm1 with (b := b) in m1_m3; eauto.
    intros n. apply m1_m3.
    eapply Mem.perm_alloc_4; eauto.
    eapply Genv.find_def_find_symbol_inversion in H as [id H]; eauto.
    exploit (Senv.find_symbol_below (Genv.globalenv W1)); eauto. intros ?.
    exploit Mem.alloc_result; eauto. intros ->.
    intros ->. eapply Plt_strict.
    eapply Plt_Ple_trans; eauto.
  - intros. eapply find_def_perm2; eauto.
  - intros id ofs. eapply val_inject_incr; eauto using same_high_half.
Qed.

Lemma extcall_preserves_mem_rel_same_side:
  forall s ge1 ge3 j j' m1 m1' m3 m3' ef vres vres' t vargs vargs' δ,
    Mem.unchanged_on (loc_unmapped j) m1 m1' ->
    inject_incr j j' ->
    inject_separated j j' m1 m3 ->
    (forall b : block,
        (Mem.valid_block m1 b -> False) ->
        Mem.valid_block m1' b ->
        exists b' : block,
          j' b = Some (b', 0) /\ Mem.block_compartment m1' b = Some (comp_of ef)) ->
    s (comp_of ef) = δ ->
    mem_rel s ge1 ge3 j δ m1 m3 ->
    Mem.inject j' m1' m3' ->
    external_call ef ge1 vargs m1 t vres m1' ->
    external_call ef ge3 vargs' m3 t vres' m3' ->
    mem_rel s ge1 ge3 j' δ m1' m3'.
Proof.
  intros s ge1 ge3 j j' m1 m1' m3 m3' ef vres vres' t vargs vargs' δ
    unchanged inj_incr inj_sep comp_new comp_ef m1_m3 inj_m1'_m3' extcall1 extcall3.
  constructor.
  - (* same domain *)
    intros b. apply same_dom in m1_m3. specialize (m1_m3 b).
    destruct (j b) as [[] |] eqn:j_b.
    + apply inj_incr in j_b.
      split; try congruence.
      intros _. destruct m1_m3 as [side_b _].
      exploit side_b; try congruence.
      simpl. destruct (Mem.block_compartment m1 b) eqn:?; try contradiction. intros ?.
      pose proof (ec_can_access_block (external_call_spec _) _ _ _ _ _ _ b (Some c) extcall1) as G.
      simpl in G. rewrite G; auto.
      intros [? | ?]; try contradiction. right; auto.
    + destruct m1_m3 as [C1 C2].
      simpl in C1, C2; simpl.
      split.
      * destruct (j' b) as [[] |] eqn:j'_b; try congruence; intros _.
        exploit inj_sep; eauto.
        intros [H _].
        assert (Mem.valid_block m1' b).
        { pose proof (Mem.mi_freeblocks _ _ _ inj_m1'_m3' b) as G.
          apply Classical_Prop.NNPP.
          intros ?. exploit G; eauto. congruence. }
        exploit comp_new; eauto. intros [? [? ->]].
        auto.
      * clear C1.
        destruct (Mem.block_compartment m1 b) as [cp |] eqn:cp_b.
        { destruct (side_eq (s cp) δ) eqn:?; [exploit C2; eauto|].
          assert (Mem.valid_block m1 b).
          { unfold Mem.valid_block.
            pose proof (Mem.nextblock_compartments m1 b) as G.
            apply proj1 in G. apply Classical_Prop.NNPP.
            intros H. apply G in H.
            now unfold Mem.block_compartment in cp_b; congruence. }
          apply Mem.unchanged_on_own with (b := b) (cp := Some cp) in unchanged; auto.
          simpl in unchanged.
          rewrite unchanged in cp_b. rewrite cp_b. intros A; specialize (C2 A); congruence. }
        (* clear C2. *)
        destruct (Mem.block_compartment m1' b) as [cp |] eqn:cp_b';
          [| intros A; specialize (C2 A); congruence].
        intros [H | H].
        -- assert (Mem.valid_block m1' b).
           { unfold Mem.valid_block.
             pose proof (Mem.nextblock_compartments m1' b) as G.
             apply proj1 in G. apply Classical_Prop.NNPP.
             intros X. apply G in X.
             now unfold Mem.block_compartment in cp_b'; congruence. }
           assert (~ Mem.valid_block m1 b).
           { unfold Mem.valid_block.
             pose proof (Mem.nextblock_compartments m1 b) as G.
             apply G. auto. }
           exploit comp_new; eauto.
           intros [? [? ?]]. congruence.
        -- now specialize (C2 (or_intror H)).
  - (* injection *)
    assumption.
  - (* Delta zero *)
    intros b b' delta j'_b.
    apply delta_zero in m1_m3; eauto.
    destruct (j b) as [[] |] eqn:j_b.
    + exploit m1_m3; eauto. intros ->. exploit inj_incr; eauto. intros. congruence.
    + exploit inj_sep; eauto.
      intros [? ?].
      assert (Mem.valid_block m1' b).
      { pose proof (Mem.mi_freeblocks _ _ _ inj_m1'_m3' b) as G.
        apply Classical_Prop.NNPP.
        intros ?. exploit G; eauto. congruence. }
      exploit comp_new; eauto. intros [? [? ?]]; congruence.
  - (* Ple nextblock 1 *)
    eapply Ple_trans. eapply ple_nextblock1; eauto. eapply external_call_nextblock; eauto.
  - (* Ple nextblock 2 *)
    eapply Ple_trans. eapply ple_nextblock2; eauto. eapply external_call_nextblock; eauto.
  - (* find_def valid 1 *)
    intros.
    eapply external_call_valid_block; eauto.
    eapply find_def_valid1; eauto.
  - (* find_def valid 2 *)
    intros.
    eapply external_call_valid_block; eauto.
    eapply find_def_valid2; eauto.
  - intros. intros n. eapply external_call_max_perm in n; eauto.
    exploit find_def_perm1; eauto.
    eapply find_def_valid1; eauto.
  - intros. intros n. eapply external_call_max_perm in n; eauto.
    exploit find_def_perm2; eauto.
    eapply find_def_valid2; eauto.
  - (* same high half *)
    intros. eapply same_high_half in m1_m3; eauto.
Qed.

(* Admits were done at some point but I lost the proof (im stupid) *)
Lemma extcall_preserves_mem_rel_opp_side1: forall s ge1 ge3 j δ m1 m1' m3 ef vargs t vres,
    s (comp_of ef) = opposite δ ->
    mem_rel s ge1 ge3 j δ m1 m3 ->
    external_call ef ge1 vargs m1 t vres m1' ->
    mem_rel s ge1 ge3 j δ m1' m3.
Proof.
  intros s ge1 ge3 j δ m1 m1' m3 ef vargs t vres side_ef m1_m3 extcall.
  constructor.
  - (* same domain *)
    intros b. apply same_dom in m1_m3. specialize (m1_m3 b).
    destruct (j b) as [[] |] eqn:j_b.
    + split; try congruence.
      intros _. destruct m1_m3 as [side_b _].
      exploit side_b; try congruence.
      simpl. destruct (Mem.block_compartment m1 b) eqn:?; try contradiction. intros ?.
      pose proof (ec_can_access_block (external_call_spec _) _ _ _ _ _ _ b (Some c) extcall) as G.
      simpl in G. rewrite G; auto.
      admit.
    + destruct m1_m3 as [C1 C2].
      simpl in C1, C2; simpl.
      split.
      * congruence.
      * admit.
  - (* injection *)
    exploit ec_mem_outside_compartment; eauto using external_call_spec.
    intros unchanged. exploit partial_mem_inject; eauto.
    apply same_dom in m1_m3. rename m1_m3 into dom_j_m1.
    intros m1_m3.
    constructor.
    + apply Mem.mi_inj in m1_m3 as mi_inj_m1_m3.
      constructor.
      * intros b1 b2 delta ofs k p j_b1 perm1.
        assert (loc_not_in_compartment (comp_of ef) m1 b1 ofs).
        { unfold loc_not_in_compartment.
          assert (G: j b1 <> None) by congruence.
          apply dom_j_m1 in G. simpl in G.
          destruct (Mem.block_compartment m1 b1) eqn:?; try congruence.
          fold (Mem.can_access_block m1 b1 (Some c)) in Heqo.
          exploit Mem.can_access_block_inj; eauto.
          simpl. intros ?. admit. }
        eapply Mem.mi_perm; eauto.
        eapply Mem.perm_unchanged_on_2; eauto.
        eapply Mem.valid_block_inject_1; eauto.
      * intros b1 b2 delta cp j_b1 b1_cp.
        exploit Mem.can_access_block_inj; eauto.
        rewrite Mem.unchanged_on_own; eauto.
        eapply Mem.valid_block_inject_1; eauto.
      * intros b1 b2 delta chunk ofs p j_b1 range_perm.
        eapply Mem.mi_align; eauto.
        admit.
      * admit.
    + intros b not_valid_m1.
      eapply Mem.mi_freeblocks; eauto. intros ?.
      exploit ec_valid_block; eauto using external_call_spec.
    + intros b b' delta j_b.
      eapply Mem.mi_mappedblocks; eauto.
    + intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 j_b1 j_b2 perm_b1 perm_b2.
      exploit Mem.mi_no_overlap; eauto.
      eapply Mem.perm_unchanged_on_2; eauto. admit. admit.
      eapply Mem.perm_unchanged_on_2; eauto. admit. admit.
    + intros b b' delta ofs j_b [perm | perm].
      * eapply Mem.mi_representable; eauto. admit.
      * eapply Mem.mi_representable; eauto. admit.
    + admit.
  - (* Delta zero *)
    intros b b' delta j'_b.
    apply delta_zero in m1_m3; eauto.
  - (* Ple nextblock 1 *)
    eapply Ple_trans. eapply ple_nextblock1; eauto. eapply external_call_nextblock; eauto.
  - (* Ple nextblock 2 *)
    eapply ple_nextblock2; eauto.
  - (* find_def valid 1 *)
    intros. eapply external_call_valid_block; eauto.
    eapply find_def_valid1; eauto.
  - (* find_def valid 2 *)
    eapply find_def_valid2; eauto.
  - (* find def perm 1 *)
    intros. intros n. eapply external_call_max_perm in n; eauto.
    exploit find_def_perm1; eauto.
    eapply find_def_valid1; eauto.
  - (* find def perm 2 *)
    eapply find_def_perm2; eauto.
  - (* same high half *)
    intros. eapply same_high_half in m1_m3; eauto.
Admitted.

Lemma extcall_preserves_mem_rel_opp_side2: forall s ge1 ge3 j δ m1 m3 m3' ef vargs t vres,
    s (comp_of ef) = opposite δ ->
    mem_rel s ge1 ge3 j δ m1 m3 ->
    external_call ef ge3 vargs m3 t vres m3' ->
    mem_rel s ge1 ge3 j δ m1 m3'.
Proof.
  intros s ge1 ge3 j δ m1 m3 m3' ef vargs t vres side_ef m1_m3 extcall.
  constructor.
  - (* same dom *)
    eapply same_dom in m1_m3; eauto.
  - (* injection *)
    exploit ec_mem_outside_compartment; eauto using external_call_spec.
    intros unchanged. exploit partial_mem_inject; eauto.
    apply same_dom in m1_m3. rename m1_m3 into dom_j_m1.
    intros m1_m3.
    constructor.
    + apply Mem.mi_inj in m1_m3 as mi_inj_m1_m3.
      constructor.
      * intros b1 b2 delta ofs k p j_b1 perm1.
        eapply Mem.perm_unchanged_on; eauto.
        { unfold loc_not_in_compartment.
          assert (G: j b1 <> None) by congruence.
          apply dom_j_m1 in G. simpl in G.
          destruct G as [G | G].
          destruct (Mem.block_compartment m1 b1) eqn:?; try congruence.
          fold (Mem.can_access_block m1 b1 (Some c)) in Heqo.
          exploit Mem.can_access_block_inj; eauto.
          simpl. intros ->.
          destruct δ; simpl in *; congruence.
          admit.
        }
        eapply Mem.mi_perm; eauto.
      * intros b1 b2 delta cp j_b1 b1_cp.
        rewrite <- Mem.unchanged_on_own; eauto.
        { exploit Mem.can_access_block_inj; eauto. }
        eapply Mem.valid_block_inject_2; eauto.
      * intros b1 b2 delta chunk ofs p j_b1 range_perm.
        eapply Mem.mi_align; eauto.
      * intros b1 ofs b2 delta j_b1 perm.
        erewrite Mem.unchanged_on_contents with (m_after := m3') (m_before := m3); eauto using Mem.mi_memval.
        { unfold loc_not_in_compartment.
          assert (G: j b1 <> None) by congruence.
          apply dom_j_m1 in G. simpl in G.
          destruct (Mem.block_compartment m1 b1) eqn:?; try congruence.
          fold (Mem.can_access_block m1 b1 (Some c)) in Heqo.
          exploit Mem.can_access_block_inj; eauto.
          simpl. intros ->. admit. admit. }
        eapply Mem.mi_perm; eauto.
    + intros b not_valid_m1.
      now eapply Mem.mi_freeblocks; eauto.
    + intros b b' delta j_b.
      exploit ec_valid_block; eauto using external_call_spec.
      eapply Mem.mi_mappedblocks; eauto.
    + intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 b1_b2 j_b1 j_b2 perm_b1 perm_b2.
      eapply Mem.mi_no_overlap; eauto.
    + intros b b' delta ofs j_b [perm | perm].
      * eapply Mem.mi_representable; eauto.
      * eapply Mem.mi_representable; eauto.
    + intros b1 ofs b2 delta k p j_b1 perm.
      exploit Mem.mi_perm_inv; eauto.
      exploit Mem.perm_unchanged_on_2; eauto.
      { unfold loc_not_in_compartment.
        assert (G: j b1 <> None) by congruence.
        apply dom_j_m1 in G. simpl in G.
        destruct (Mem.block_compartment m1 b1) eqn:?; try congruence.
        fold (Mem.can_access_block m1 b1 (Some c)) in Heqo.
        exploit Mem.can_access_block_inj; eauto using Mem.mi_inj.
        simpl. intros ->. admit. admit. }
      eapply Mem.valid_block_inject_2; eauto.
  - (* Delta zero *)
    intros b b' delta j'_b.
    apply delta_zero in m1_m3; eauto.
  - (* Ple nextblock 1 *)
    eapply ple_nextblock1; eauto.
  - (* Ple nextblock 2 *)
    eapply Ple_trans. eapply ple_nextblock2; eauto. eapply external_call_nextblock; eauto.
  - (* find_def valid 1 *)
    intros. eapply find_def_valid1; eauto.
  - (* find_def valid 2 *)
    intros. eapply external_call_valid_block; eauto.
    eapply find_def_valid2; eauto.
  - (* find_def perm 1 *)
    intros. eapply find_def_perm1; eauto.
  - (* find_def valid 2 *)
    intros. intros n. eapply external_call_max_perm in n; eauto.
    exploit find_def_perm2; eauto.
    eapply find_def_valid2; eauto.
  - (* same high half *)
    intros. eapply same_high_half in m1_m3; eauto.
Admitted.

(** Useful simplification tactic *)
(** Taken from Asmgenproof1.v *)

Ltac Simplif :=
  ((rewrite Asmgenproof0.nextinstr_inv by eauto with asmgen)
   || (rewrite Asmgenproof0.nextinstr_inv1 by eauto with asmgen)
   || (rewrite Pregmap.gss)
   || (rewrite Asmgenproof0.nextinstr_pc)
   || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

Ltac Simplif_all :=
  ((rewrite Asmgenproof0.nextinstr_inv in * by eauto with asmgen)
   || (rewrite Asmgenproof0.nextinstr_inv1 in * by eauto with asmgen)
   || (rewrite Pregmap.gss in * )
   || (rewrite Asmgenproof0.nextinstr_pc in * )
   || (rewrite Pregmap.gso in * by eauto with asmgen)); auto with asmgen.

Ltac Simpl_all := repeat Simplif_all.

(* Some tactics *)
Ltac simpl_nextinstr_PC r :=
  destruct (Pregmap.elt_eq r PC);
  [subst r; Simpl; eapply Val.offset_ptr_inject; eauto|
    Simpl].

Lemma ptrofs_of_int_zero:
  Ptrofs.of_int Int.zero = Ptrofs.zero.
Proof.
  Local Transparent Ptrofs.repr Int.repr.
  simpl.
  Local Opaque Ptrofs.repr Int.repr.
  reflexivity.
Qed.

Lemma lt_xx_false: forall x,
    Int.lt x x = false.
Proof.
  intros. unfold Int.lt. apply zlt_false. lia.
Qed.

Lemma ltu_xx_false: forall x,
    Int.ltu x x = false.
Proof.
  intros. unfold Int.ltu. apply zlt_false. lia.
Qed.

Lemma lt64_xx_false: forall x,
    Int64.lt x x = false.
Proof.
  intros. unfold Int64.lt. apply zlt_false. lia.
Qed.

Lemma ltu64_xx_false: forall x,
    Int64.ltu x x = false.
Proof.
  intros. unfold Int64.ltu. apply zlt_false. lia.
Qed.

(* Comparisons *)

(* TODO: rename variables *)
Lemma cmpu_bool_preserved: forall s ge ge' j δ m1' m3 v1 v2 v1' v2' op b,
    mem_rel s ge ge' j δ m1' m3 ->
    Val.inject j v1 v1' ->
    Val.inject j v2 v2' ->
    Val.cmpu_bool (Mem.valid_pointer m1') op v1 v2 = Some b ->
    Val.cmpu_bool (Mem.valid_pointer m3) op v1' v2' = Some b.
Proof.
  intros until b. intros m1_m3 inj1 inj2.
  inv inj1; simpl; inv inj2; simpl; destruct Archi.ptr64; simpl; auto; try congruence.
  - destruct Int.eq; simpl; try congruence. destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
    eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
    clear valid. destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
    assert (delta = 0) by (eapply delta_zero; eauto); subst.
    eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
    rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'.
    now rewrite orb_true_r.
  - destruct Int.eq; simpl; try congruence. destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
    eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
    clear valid. destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
    assert (delta = 0) by (eapply delta_zero; eauto); subst.
    eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
    rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'.
    now rewrite orb_true_r.
  - destruct eq_block; subst; simpl in *; try congruence.
    + assert (b3 = b2) by congruence; subst; simpl.
      assert (delta = delta0) by congruence; subst; simpl.
      destruct eq_block; try congruence.
      destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
      eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
      clear valid.
      destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
      assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. rewrite Ptrofs.add_zero; auto.
      clear valid'.
      destruct Mem.valid_pointer eqn:valid''; simpl; try congruence.
      assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid''; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid''. rewrite valid''. rewrite Ptrofs.add_zero; auto.
      now rewrite orb_true_r.
      clear valid.
      destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
      assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. rewrite Ptrofs.add_zero; auto.
      rewrite orb_true_r. simpl.
      clear valid'.
      destruct Mem.valid_pointer eqn:valid''; simpl; try congruence.
      eapply Mem.valid_pointer_inject in valid''; eauto using partial_mem_inject.
      rewrite Z.add_0_r in valid''. rewrite valid''. now auto.
      clear valid''.
      destruct Mem.valid_pointer eqn:valid'''; simpl; try congruence.
      eapply Mem.valid_pointer_inject in valid'''; eauto using partial_mem_inject.
      rewrite Z.add_0_r in valid'''. rewrite valid'''.
      now rewrite orb_true_r.
    + destruct eq_block; subst; simpl in *.
      * destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
        destruct (Mem.valid_pointer m1' b0) eqn:valid'; simpl; try congruence.
        assert (delta = 0) by (eapply delta_zero; eauto); subst.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.mi_no_overlap with (f := j) in n; [| now eapply partial_mem_inject; eauto].
        specialize (n H H0 (Mem.perm_cur_max _ _ _ _ ((proj1 (Mem.valid_pointer_nonempty_perm _ _ _)) valid))
                      (Mem.perm_cur_max _ _ _ _ ((proj1 (Mem.valid_pointer_nonempty_perm _ _ _)) valid')));
          rewrite !Z.add_0_r in n.
        destruct n; [contradiction |].
        eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
        eapply Mem.valid_pointer_inject_val in valid'; eauto using partial_mem_inject; rewrite valid'; simpl; auto.
        destruct op; simpl; try congruence.
        intros. inv H2. rewrite !Ptrofs.add_zero. unfold Ptrofs.eq. destruct zeq; auto; congruence.
        intros. inv H2. rewrite !Ptrofs.add_zero. unfold Ptrofs.eq. destruct zeq; auto; congruence.
      * destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
        eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
        clear valid.
        destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
        assert (delta = 0) by (eapply delta_zero; eauto); subst.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
        rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. auto.
Qed.


Lemma cmpu_inject:
  forall s ge ge' j δ op m1 m3 v1 v1' v2 v2',
    mem_rel s ge ge' j δ m1 m3 ->
    Val.inject j v1 v1' ->
    Val.inject j v2 v2' ->
    Val.inject j (Val.cmpu (Mem.valid_pointer m1) op v1 v2)
      (Val.cmpu (Mem.valid_pointer m3) op v1' v2').
Proof.
  intros s ge ge' j δ op m1 m3 v1 v1' v2 v2' m1_m3 v1_v1' v2_v2'.
  unfold Val.cmpu.
  destruct (Val.cmpu_bool) eqn:eq_cmpu.
  - eapply cmpu_bool_preserved in eq_cmpu; eauto. rewrite eq_cmpu; now eapply Cminorgenproof.val_inject_val_of_optbool.
  - auto.
Qed.

(* TODO: this is the same proof as [cmpu_bool_preserved] above, but with [Int64] substituted for [Int] *)
Lemma cmplu_bool_preserved: forall s ge ge' j δ m1' m3 v1 v2 v1' v2' op b,
    mem_rel s ge ge' j δ m1' m3 ->
    Val.inject j v1 v1' ->
    Val.inject j v2 v2' ->
    Val.cmplu_bool (Mem.valid_pointer m1') op v1 v2 = Some b ->
    Val.cmplu_bool (Mem.valid_pointer m3) op v1' v2' = Some b.
Proof.
  intros until b. intros m1_m3 inj1 inj2.
  inv inj1; simpl; inv inj2; simpl; destruct Archi.ptr64; simpl; auto; try congruence.
  - destruct Int64.eq; simpl; try congruence. destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
    eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
    clear valid. destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
    assert (delta = 0) by (eapply delta_zero; eauto); subst.
    eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
    rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'.
    now rewrite orb_true_r.
  - destruct Int64.eq; simpl; try congruence. destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
    eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
    clear valid. destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
    assert (delta = 0) by (eapply delta_zero; eauto); subst.
    eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
    rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'.
    now rewrite orb_true_r.
  - destruct eq_block; subst; simpl in *; try congruence.
    + assert (b3 = b2) by congruence; subst; simpl.
      assert (delta = delta0) by congruence; subst; simpl.
      destruct eq_block; try congruence.
      destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
      eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
      clear valid.
      destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
      assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. rewrite Ptrofs.add_zero; auto.
      clear valid'.
      destruct Mem.valid_pointer eqn:valid''; simpl; try congruence.
      assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid''; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid''. rewrite valid''. rewrite Ptrofs.add_zero; auto.
      now rewrite orb_true_r.
      clear valid.
      destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
      assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. rewrite Ptrofs.add_zero; auto.
      rewrite orb_true_r. simpl.
      clear valid'.
      destruct Mem.valid_pointer eqn:valid''; simpl; try congruence.
      eapply Mem.valid_pointer_inject in valid''; eauto using partial_mem_inject.
      rewrite Z.add_0_r in valid''. rewrite valid''. now auto.
      clear valid''.
      destruct Mem.valid_pointer eqn:valid'''; simpl; try congruence.
      eapply Mem.valid_pointer_inject in valid'''; eauto using partial_mem_inject.
      rewrite Z.add_0_r in valid'''. rewrite valid'''.
      now rewrite orb_true_r.
    + destruct eq_block; subst; simpl in *.
      * destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
        destruct (Mem.valid_pointer m1' b0) eqn:valid'; simpl; try congruence.
        assert (delta = 0) by (eapply delta_zero; eauto); subst.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.mi_no_overlap with (f := j) in n; [| now eapply partial_mem_inject; eauto].
        specialize (n H H0 (Mem.perm_cur_max _ _ _ _ ((proj1 (Mem.valid_pointer_nonempty_perm _ _ _)) valid))
                      (Mem.perm_cur_max _ _ _ _ ((proj1 (Mem.valid_pointer_nonempty_perm _ _ _)) valid')));
          rewrite !Z.add_0_r in n.
        destruct n; [contradiction |].
        eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
        eapply Mem.valid_pointer_inject_val in valid'; eauto using partial_mem_inject; rewrite valid'; simpl; auto.
        destruct op; simpl; try congruence.
        intros. inv H2. rewrite !Ptrofs.add_zero. unfold Ptrofs.eq. destruct zeq; auto; congruence.
        intros. inv H2. rewrite !Ptrofs.add_zero. unfold Ptrofs.eq. destruct zeq; auto; congruence.
      * destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
        eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
        clear valid.
        destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
        assert (delta = 0) by (eapply delta_zero; eauto); subst.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
        rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. auto.
Qed.

Lemma cmplu_inject:
  forall s ge ge' j δ op m1 m3 v1 v1' v2 v2',
    mem_rel s ge ge' j δ m1 m3 ->
    Val.inject j v1 v1' ->
    Val.inject j v2 v2' ->
    Val.inject j (Val.maketotal (Val.cmplu (Mem.valid_pointer m1) op v1 v2))
      (Val.maketotal (Val.cmplu (Mem.valid_pointer m3) op v1' v2')).
Proof.
  intros s ge ge' j δ op m1 m3 v1 v1' v2 v2' m1_m3 v1_v1' v2_v2'.
  unfold Val.cmplu.
  destruct (Val.cmplu_bool) eqn:eq_cmplu.
  - eapply cmplu_bool_preserved in eq_cmplu; eauto. rewrite eq_cmplu.
    simpl. now eapply Cop.val_inject_of_bool.
  - auto.
Qed.


Hint Resolve cmpu_inject cmplu_inject : solve_inject.
Hint Resolve Cop.val_inject_of_bool: solve_inject.

Section Lemmas.

  Context (s: split) (W1 W2 W3: Asm.program) (δ: side).

  Hypothesis norepet1: list_norepet (prog_defs_names W1).
  Hypothesis norepet2: list_norepet (prog_defs_names W2).
  Hypothesis norepet3: list_norepet (prog_defs_names W3).

  (* Context (ge1 ge2: genv). *)
  Notation ge1 := (Genv.globalenv W1).
  Notation ge2 := (Genv.globalenv W2).
  Notation ge3 := (Genv.globalenv W3).


  Lemma alloc_preserves_rel1:
    forall cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3,
      s |= cp ∈ δ ->
      agrees_with j__δ (init_meminj W1 W3) ->
      def_on_addressable s ge1 j__δ δ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      agrees_with j__δ' (init_meminj W1 W3) /\
                      def_on_addressable s ge1 j__δ' δ /\
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      regset_rel j__δ' rs1 rs3 /\
                      j__δ' b1 = Some (b3, 0) /\
                      inject_incr j__δ j__δ'.
  Proof.
    intros cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3 side_cp agr addr m1_m3 m2_m3 rs1_rs3 alloc1.
    exploit (Mem.alloc_parallel_inject j__δ m1); eauto using partial_mem_inject, Z.le_refl.
    intros [j' [m3' [b3 [? [? [? [? diff]]]]]]].
    exists j', m3', b3.
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]];
      [assumption | eapply agrees_with_incr2; eauto | eapply def_on_addressable_incr; eauto | | | intros ?; eauto using val_inject_incr | assumption | assumption].
    { destruct (init_meminj W1 W3 b1) as [[] |] eqn:?; auto.
      exploit init_meminj_invert; eauto. intros [-> [id [? ?]]].
      apply Mem.alloc_result in alloc1; subst.

      pose proof (ple_nextblock1 _ _ _ _ _ _ _ m1_m3).
      exploit (Senv.find_symbol_below ge1); eauto. intros ?.
      pose proof (Plt_Ple_trans _ _ _ H6 H5).
      now exploit Plt_strict; eauto. }

    { clear dependent j__oppδ.
      constructor.
      - intros b. destruct (Pos.eq_dec b b1); subst.
        + split; [| congruence].
          intros _. apply Mem.owned_new_block in alloc1. simpl in alloc1. left; simpl; now rewrite alloc1.
        + rewrite (diff _ n).
          eapply same_dom in m1_m3. specialize (m1_m3 b).
          eapply Mem.alloc_block_compartment with (b' := b) in alloc1.
          simpl. rewrite alloc1. rewrite peq_false; eauto.
      - assumption.
      - intros b b' delta.
        destruct (Pos.eq_dec b b1); subst.
        + congruence.
        + rewrite (diff _ n).
          intros G. exploit delta_zero; eauto.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock2.
      - intros. exploit find_def_valid1; eauto. eapply Mem.valid_block_alloc; eauto.
      - intros. exploit find_def_valid2; eauto. eapply Mem.valid_block_alloc; eauto.
      - intros.
        pose proof (ple_nextblock1 _ _ _ _ _ m1 m3 m1_m3) as ple.
        eapply find_def_perm1 with (b := b) in m1_m3; eauto.
        intros n. apply m1_m3.
        eapply Mem.perm_alloc_4; eauto.
        eapply Genv.find_def_find_symbol_inversion in H3 as [id H3]; eauto.
        exploit (Senv.find_symbol_below (Genv.globalenv W1)); eauto. intros ?.
        exploit (Mem.alloc_result m1); eauto. intros ->.
        intros ->. eapply Plt_strict.
        eapply Plt_Ple_trans; eauto.
      - intros.
        pose proof (ple_nextblock2 _ _ _ _ _ m1 m3 m1_m3) as ple.
        eapply find_def_perm2 with (b := b) in m1_m3; eauto.
        intros n. apply m1_m3.
        eapply Mem.perm_alloc_4; eauto.
        eapply Genv.find_def_find_symbol_inversion in H3 as [id H3]; eauto.
        exploit (Senv.find_symbol_below (Genv.globalenv W3)); eauto. intros ?.
        exploit (Mem.alloc_result m3); eauto. intros -> ->.
        eapply Plt_strict. eapply Plt_Ple_trans; eauto.
      - intros id ofs.
        exploit same_high_half; eauto. }
    { clear dependent j__δ.
      destruct m2_m3.
      constructor; eauto.
      - eapply Mem.alloc_right_inject; eauto using partial_mem_inject.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_alloc; eauto.
      - intros. intros n.
        eapply Mem.perm_alloc_4 in n; eauto.
        eapply find_def_perm4; eauto.
        intros ->.
        exploit (Mem.alloc_result m3); eauto. intros ->.
        eapply Genv.find_def_find_symbol_inversion in H1 as [id H1]; eauto.
        exploit (Senv.find_symbol_below (Genv.globalenv W3)); eauto. intros ?.
        eapply Plt_strict. eapply Plt_Ple_trans; eauto. }
  Qed.

  Lemma alloc_preserves_rel2:
    forall cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3,
      s |= cp ∈ opposite δ ->
      agrees_with j__δ (init_meminj W1 W3) ->
      def_on_addressable s ge1 j__δ δ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      agrees_with j__δ' (init_meminj W1 W3) /\
                      def_on_addressable s ge1 j__δ' δ /\
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      regset_rel j__δ' rs1 rs3 /\
                      inject_incr j__δ j__δ'.
  Proof.
    intros cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3 side_cp agr addr m1_m3 m2_m3 rs1_rs3 alloc1.
    exploit (Mem.alloc_parallel_inject j__δ m1); eauto using partial_mem_inject, Z.le_refl.
    intros [_ [m3' [b3 [alloc3 [_ [_ [_ _]]]]]]].
    exploit (Mem.alloc_left_unmapped_inject j__δ m1); eauto using partial_mem_inject.
    intros [j' [inj [incr [isnone diff]]]].
    exploit Mem.alloc_right_inject; eauto. intros inj'.
    exists j', m3', b3.  split; [| split; [| split; [| split; [| split; [| split]]]]];
      [assumption | eapply agrees_with_incr1; eauto | eapply def_on_addressable_incr; eauto | | | intros ?; eauto using val_inject_incr | assumption].
    { clear dependent j__oppδ.
      constructor; auto.
      - intros b. destruct (Pos.eq_dec b b1); subst.
        + split; [congruence |].
          intros ?. apply Mem.owned_new_block in alloc1. simpl in *. rewrite alloc1 in H.
          apply same_dom in m1_m3. specialize (m1_m3 b1).
          destruct m1_m3 as [_ m1_m3].
          destruct H.
          * now destruct δ; congruence.
          * specialize (m1_m3 (or_intror H)).
            assert (exists b1' delta, j__δ b1 = Some (b1', delta)) as [b1' [? G]]
                by now (destruct (j__δ b1) as [[]|]; try congruence; eauto).
            apply incr in G. congruence.
        + rewrite (diff _ n).
          eapply same_dom in m1_m3. specialize (m1_m3 b).
          eapply Mem.alloc_block_compartment with (b' := b) in alloc1.
          simpl. rewrite alloc1. rewrite peq_false; eauto.
      - intros b b' delta.
        destruct (Pos.eq_dec b b1); subst.
        + congruence.
        + rewrite (diff _ n).
          intros G. exploit delta_zero; eauto.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock2.
      - intros. exploit find_def_valid1; eauto. eapply Mem.valid_block_alloc. eauto.
      - intros. exploit find_def_valid2; eauto. eapply Mem.valid_block_alloc. eauto.
      - intros. intros n. eapply find_def_perm1; eauto.
        eapply Mem.perm_alloc_4; eauto.
        intros ->.
        exploit (Mem.alloc_result m1); eauto. intros ->.
        eapply Genv.find_def_find_symbol_inversion in H as [id H]; eauto.
        exploit (Senv.find_symbol_below (Genv.globalenv W1)); eauto. intros ?.
        eapply Plt_strict. eapply Plt_Ple_trans; eauto using ple_nextblock1.
      - intros. intros n. eapply find_def_perm2; eauto.
        eapply Mem.perm_alloc_4; eauto.
        intros ->.
        exploit (Mem.alloc_result m3); eauto. intros ->.
        eapply Genv.find_def_find_symbol_inversion in H as [id H]; eauto.
        exploit (Senv.find_symbol_below (Genv.globalenv W3)); eauto. intros ?.
        eapply Plt_strict. eapply Plt_Ple_trans; eauto using ple_nextblock2.
      - intros id ofs.
        exploit same_high_half; eauto.
    }
    { clear dependent j__δ.
      destruct m2_m3.
      constructor; eauto.
      - eapply Mem.alloc_right_inject; eauto using partial_mem_inject.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_alloc; eauto.
      - intros. intros n. eapply find_def_perm4; eauto.
        eapply Mem.perm_alloc_4; eauto.
        intros ->.
        exploit (Mem.alloc_result m3); eauto. intros ->.
        eapply Genv.find_def_find_symbol_inversion in H as [id H]; eauto.
        exploit (Senv.find_symbol_below (Genv.globalenv W3)); eauto. intros ?.
        eapply Plt_strict. eapply Plt_Ple_trans; eauto using ple_nextblock2. }
  Qed.

  Lemma alloc_preserves_rel:
    forall cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3,
      agrees_with j__δ (init_meminj W1 W3) ->
      def_on_addressable s ge1 j__δ δ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      agrees_with j__δ' (init_meminj W1 W3) /\
                      def_on_addressable s ge1 j__δ' δ /\
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      regset_rel j__δ' rs1 rs3 /\
                      (s |= cp ∈ δ -> j__δ' b1 = Some (b3, 0)) /\
                      inject_incr j__δ j__δ'.
  Proof.
    intros.
    destruct (side_eq (s cp) δ) as [s_cp | s_cp].
    - exploit alloc_preserves_rel1; eauto. now simpl.
      intros [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto).
    - exploit alloc_preserves_rel2; eauto. now simpl; destruct (s cp); destruct δ.
      intros [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto). simpl; congruence.
  Qed.


  Lemma free_preserves_rel:
    forall cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 b3,
      j__δ b1 = Some (b3, 0) -> (* we are necessarily in the δ case *)
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      Mem.free m1 b1 lo hi cp = Some m1' ->
      exists m3', Mem.free m3 b3 lo hi cp = Some m3' /\
               mem_rel s ge1 ge3 j__δ δ m1' m3' /\
               mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3'.
  Proof.
    intros cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 b3 ptr_inj m1_m3 m2_m3 free1.
    exploit (Mem.free_parallel_inject j__δ m1); eauto using partial_mem_inject.
    intros [m3' [free3 m1'_m3']].
    rewrite 2!Z.add_0_r in free3.
    exists m3'; split; [| split]; [assumption | |].
    { clear dependent j__oppδ.
      constructor.
      - intros b. apply same_dom in m1_m3.
        specialize (m1_m3 b).
        simpl in *. apply Mem.free_result in free1. unfold Mem.unchecked_free in free1.
        destruct (zle hi lo); now subst.
      - assumption.
      - intros b b' delta.
        intros G. exploit delta_zero; eauto.
      - erewrite Mem.nextblock_free; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - erewrite Mem.nextblock_free; eauto using Ple_trans, Ple_succ, ple_nextblock2.
      - intros. exploit find_def_valid1; eauto. eapply Mem.valid_block_free_1; eauto.
      - intros. exploit find_def_valid2; eauto. eapply Mem.valid_block_free_1; eauto.
      - intros. intros n.
        eapply find_def_perm1; eauto.
        eapply Mem.perm_free_3; eauto.
      - intros. intros n.
        eapply find_def_perm2; eauto.
        eapply Mem.perm_free_3; eauto.
      - intros id ofs.
        exploit same_high_half; eauto. }
    { destruct m2_m3.
      constructor; auto.
      - eapply Mem.free_right_inject; eauto.
        intros.
        apply Mem.mi_inj in partial_mem_inject0.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m2 b0)) in partial_mem_inject0; eauto;
          [| now destruct Mem.block_compartment eqn:?]; eauto.
        specialize (same_dom0 b0).
        assert (X: j__oppδ b0 <> None) by congruence.
        apply same_dom0 in X. simpl in *.
        apply same_dom in m1_m3 as G.
        specialize (G b1).
        assert (Y: j__δ b1 <> None) by congruence.
        apply G in Y. simpl in *. clear G.
        apply partial_mem_inject in m1_m3.
        apply Mem.mi_inj in m1_m3.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m1 b1)) in m1_m3; eauto;
          [| now destruct (Mem.block_compartment m1 b1) eqn:?]; eauto.
        unfold Mem.can_access_block in *.
        destruct X as [X | X]; destruct Y as [Y | Y].
        (* easy -- Mem.can_access_block must agree with genv *)
        admit. admit. admit. admit.
      - erewrite Mem.nextblock_free; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_free_1; eauto.
      - intros. intros n.
        eapply find_def_perm4; eauto.
        eapply Mem.perm_free_3; eauto. }
  Admitted.

  Lemma store_preserves_rel:
    forall cp (j__δ j__oppδ: meminj) m1 m1' m2 m3 ch ofs v1 v3 b1 b3,
      j__δ b1 = Some (b3, 0) -> (* we are necessarily in the δ case *)
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      Val.inject j__δ v1 v3 ->
      Mem.store ch m1 b1 ofs v1 cp = Some m1' ->
      exists m3', Mem.store ch m3 b3 ofs v3 cp = Some m3' /\
               mem_rel s ge1 ge3 j__δ δ m1' m3' /\
               mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3'.
  Proof.
    intros cp j__δ j__oppδ m1 m1' m2 m3 ch ofs v1 v3 b1 b3 ptr_inj m1_m3 m2_m3 val_inj store1.
    exploit (Mem.store_mapped_inject j__δ); eauto using partial_mem_inject.
    intros [m3' [store3 ?]].
    rewrite Z.add_0_r in store3.
    exists m3'; split; [| split]; [assumption | |].
    { clear dependent j__oppδ.
      constructor.
      - intros b. apply same_dom in m1_m3.
        specialize (m1_m3 b). simpl in *.
        eapply Mem.store_block_compartment in store1. now rewrite store1.
      - assumption.
      - now eapply delta_zero; eauto.
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock2.
      - intros. exploit find_def_valid1; eauto. eapply Mem.store_valid_block_1; eauto.
      - intros. exploit find_def_valid2; eauto. eapply Mem.store_valid_block_1; eauto.
      - intros; intros n. exploit find_def_perm1; eauto.
        eapply Mem.perm_store_2; eauto.
      - intros; intros n. exploit find_def_perm2; eauto.
        eapply Mem.perm_store_2; eauto.
      - intros id ofs0.
        exploit same_high_half; eauto. }
    { destruct m2_m3.
      constructor; eauto.
      - eapply Mem.store_outside_inject; eauto.
        intros.
        apply Mem.mi_inj in partial_mem_inject0.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m2 b')) in partial_mem_inject0; eauto;
          [| now destruct Mem.block_compartment eqn:?]; eauto.
        specialize (same_dom0 b').
        assert (X: j__oppδ b' <> None) by congruence.
        apply same_dom0 in X. simpl in *.
        apply same_dom in m1_m3 as G.
        specialize (G b1).
        assert (Y: j__δ b1 <> None) by congruence.
        apply G in Y. simpl in *. clear G.
        apply partial_mem_inject in m1_m3.
        apply Mem.mi_inj in m1_m3.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m1 b1)) in m1_m3; eauto;
          [| now destruct (Mem.block_compartment m1 b1) eqn:?]; eauto.
        unfold Mem.can_access_block in *.
        destruct (Mem.block_compartment m2 b'); destruct (Mem.block_compartment m1 b1); try congruence.
        admit. admit. admit. admit.
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. exploit find_def_valid2; eauto. eapply Mem.store_valid_block_1; eauto.
      - intros; intros n. exploit find_def_perm2; eauto.
        eapply Mem.perm_store_2; eauto. }
  Admitted.

  Lemma regset_rel_inject: forall j rs1 rs3 rd v v',
      regset_rel j rs1 rs3 ->
      Val.inject j v v' ->
      regset_rel j (rs1 # rd <- v) (rs3 # rd <- v').
  Proof.
    intros.
    intros r.
    destruct (Pregmap.elt_eq r rd); now try subst r; Simpl.
  Qed.

  Parameter stack_rel: split -> genv -> side -> meminj -> meminj -> stack -> stack -> stack -> Prop.

  Lemma inject_incr_stack_rel1:
    forall j1 j1' j2 st1 st2 st3,
      inject_incr j1 j1' ->
      stack_rel s ge3 δ j1 j2 st1 st2 st3 ->
      stack_rel s ge3 δ j1' j2 st1 st2 st3.
  Proof.
  Admitted.
  (*   intros * incr st_rel. *)
  (*   induction st_rel. *)
  (*   - constructor; eauto. *)
  (*   - constructor; eauto. *)
  (*     inv H. *)
  (*     + econstructor; eauto. *)
  (*     + eapply stackframe_related_opp_δ; eauto. *)
  (* Qed. *)

  Lemma inject_incr_stack_rel2:
    forall j1 j2 j2' st1 st2 st3,
      inject_incr j2 j2' ->
      stack_rel s ge3 δ j1 j2 st1 st2 st3 ->
      stack_rel s ge3 δ j1 j2' st1 st2 st3.
  Proof.
  Admitted.
  (*   intros * incr st_rel. *)
  (*   induction st_rel. *)
  (*   - constructor; eauto. *)
  (*   - constructor; eauto. *)
  (*     inv H. *)
  (*     + econstructor; eauto. *)
  (*     + eapply stackframe_related_opp_δ; eauto. *)
  (* Qed. *)

  Lemma find_funct_ptr_preserved:
    forall j__δ b b' fd,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      j__δ b = Some (b', 0) ->
      Genv.find_funct_ptr ge1 b = Some fd ->
      exists fd',
        Genv.find_funct_ptr ge3 b' = Some fd' /\
          match_fundef fd fd' /\
          (forall id : ident, Genv.find_symbol ge1 id = Some b -> kept_genv s ge1 δ id = true -> fd = fd').
  Proof.
    intros j b b' fd inj_pres inj_b_b' find_b_fd.
    unfold Genv.find_funct_ptr in *.
    destruct (Genv.find_def ge1 b) as [[fd' |] |] eqn:find_def_b; try discriminate.
    assert (fd' = fd) by congruence; subst fd'; clear find_b_fd.

    exploit defs_inject; eauto. intros [gd' [find_def_b' [_ [match_fd_gd' left_implies_eq]]]].
    assert (exists fd', gd' = Gfun fd' /\ match_fundef fd fd') as [fd' [gd'_fd' match_fd_fd']].
    { inv match_fd_gd'; match goal with | H: match_fundef _ _ |- _ => inv H end.
      - eexists; split; [reflexivity | constructor].
      - eexists; split; [reflexivity | constructor]. }
    subst gd'.

    rewrite find_def_b'. eexists; split; [| split]; auto.
    intros; exploit left_implies_eq; eauto. congruence.
  Qed.

  Lemma find_def_preserved:
    forall j__δ b b' gd,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      j__δ b = Some (b', 0) ->
      Genv.find_def ge1 b = Some gd ->
      exists gd',
        Genv.find_def ge3 b' = Some gd' /\
          match_globdef gd gd' /\
          (forall id : ident, Genv.find_symbol ge1 id = Some b -> kept_genv s ge1 δ id = true -> gd' = gd).
  Proof.
    intros j__δ b b' gd inj_pres inj_b_b' find_b_gd. exploit defs_inject; eauto. intros [gd' [find_def_b' [_ [match_fd_gd' left_implies_eq]]]].
    eauto.
  Qed.

  Lemma def_on_addressable_init:
    match_prog s δ W1 W3 ->
    def_on_addressable s ge1 (init_meminj W1 W3) δ.
  Proof.
    unfold def_on_addressable.
    intros match_W1_W3. intros.
    unfold init_meminj.
    apply Genv.find_invert_symbol in H; rewrite H.
    apply Genv.invert_find_symbol in H.
    exploit transform_find_symbol_1; eauto.
    intros (? & ->). eauto.
  Qed.

  Lemma agrees_with_init_meminj_find_def_preserved:
    forall j b b' delta gd,
      match_prog s δ W1 W3 ->
      agrees_with j (init_meminj W1 W3) ->
      j b = Some (b', delta) ->
      Genv.find_def ge1 b = Some gd ->
      exists gd',
        Genv.find_def ge3 b' = Some gd' /\
          match_globdef gd gd' /\
          (forall id : ident, Genv.find_symbol ge1 id = Some b -> kept_genv s ge1 δ id = true -> gd' = gd).
    Proof.
      intros j b b' delta gd match_W1_W3 agr j_b find_b.
      exploit init_meminj_preserves_globals; eauto. intros inj_pres.
      eapply find_def_preserved; eauto.
      assert (exists b', init_meminj W1 W3 b = Some (b', 0)) as [b'' init_meminj_b].
      { unfold init_meminj.
        exploit Genv.find_def_find_symbol_inversion; eauto.
        intros (id & A). apply Genv.find_invert_symbol in A as B. rewrite B.
        destruct (kept_prog s W1 δ id) eqn:?.
        - exploit match_prog_def; eauto.
          assert (C: (prog_defmap W1) ! id = Some gd).
          { apply Genv.find_def_symbol; eauto. }
          rewrite C. intros D.
          apply Genv.find_def_symbol in D as [b'' [D E]]; eauto.
          rewrite D. eauto.
        - exploit match_prog_notdef; eauto.
          assert (C: (prog_defmap W1) ! id = Some gd).
          { apply Genv.find_def_symbol; eauto. }
          rewrite C. intros D.
          inversion D as [| ? ? matchgd u E]; subst. symmetry in E.
          apply Genv.find_def_symbol in E as [b'' [E F]]; eauto.
          rewrite E. eauto. }
      exploit agr; eauto. now intros []; congruence.
    Qed.

  Lemma find_comp_of_block_preserved:
    forall j__δ b b' delta
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      j__δ b = Some (b', delta) ->
      Genv.find_comp_of_block ge1 b = Genv.find_comp_of_block ge3 b'.
  Proof.
    intros j b b' delta inj_pres delta_zero j_b.
    exploit delta_zero; eauto; intros ->.
    unfold Genv.find_comp_of_block.
    destruct (Genv.find_def _ b) as [gd |] eqn:?.
    - exploit find_def_preserved; eauto.
      intros (gd' & -> & H & ?).
      destruct H as [? ? H | ? ? H]; now inv H.
    - destruct (Genv.find_def _ b') as [gd |] eqn:?; [| reflexivity].
      exploit defs_rev_inject; eauto. intros (gd' & ? & ?); congruence.
  Qed.


  Lemma agrees_with_init_meminj_find_comp_of_block_preserved:
    forall j b b' delta cp,
      match_prog s δ W1 W3 ->
      agrees_with j (init_meminj W1 W3) ->
      j b = Some (b', delta) ->
      Genv.find_comp_of_block ge1 b = Some cp ->
      Genv.find_comp_of_block ge3 b' = Some cp.
  Proof.
    intros j b b' delta cp match_W1_W3 agr j_b comp_b.
    unfold Genv.find_comp_of_block in *.
    destruct (Genv.find_def _ b) as [gd |] eqn:?.
    - exploit agrees_with_init_meminj_find_def_preserved; eauto.
      intros (gd' & -> & H & ?).
      destruct H as [? ? H | ? ? H]; now inv H.
    - congruence.
  Qed.

  Lemma find_comp_preserved:
    forall j__δ v v'
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      v <> Vundef ->
      Val.inject j__δ v v' ->
      Genv.find_comp ge1 v = Genv.find_comp ge3 v'.
  Proof.
    intros j v v' inj_pres delta_zero nundef H.
    inv H; simpl; auto; try congruence.
    exploit find_comp_of_block_preserved; eauto.
  Qed.

  Lemma agrees_with_init_meminj_find_comp_preserved:
    forall j v v' cp,
      match_prog s δ W1 W3 ->
      agrees_with j (init_meminj W1 W3) ->
      v <> Vundef ->
      Val.inject j v v' ->
      Genv.find_comp ge1 v = Some cp ->
      Genv.find_comp ge3 v' = Some cp.
  Proof.
    intros j v v' cp match_W1_W3 agr j_v v_not_undef comp_v.
    inv v_not_undef; simpl; auto; try congruence.
    eapply agrees_with_init_meminj_find_comp_of_block_preserved; eauto.
  Qed.

End Lemmas.

Section Theorems.

  Context (s: split) (W1 W2 W3: Asm.program) (δ: side).

  Hypothesis match_W1_W3: match_prog s δ W1 W3.
  Hypothesis match_W2_W3: match_prog s (opposite δ) W2 W3.

  Notation cp_main := (comp_of_main W1).

  Hypothesis norepet1: list_norepet (prog_defs_names W1).
  Hypothesis norepet2: list_norepet (prog_defs_names W2).

  Notation ge1 := (Genv.globalenv W1).
  Notation ge2 := (Genv.globalenv W2).
  Notation ge3 := (Genv.globalenv W3).

  Local Opaque Val.add Val.addl Val.sub Val.subl
    Val.mul Val.mulhs Val.mulhu Val.mull Val.mullhs Val.mullhu
    Val.and Val.or Val.xor Val.andl Val.orl Val.xorl
    Val.shl Val.shru Val.shr Val.shll Val.shrlu Val.shrl
    Val.cmp Val.cmpl Val.cmpf Val.cmpfs
    Val.cmpu Val.cmplu
    Val.divs Val.divu Val.divls Val.divlu
    Val.mods Val.modu Val.modls Val.modlu
    Val.negfs Val.negf Val.absfs Val.absf
    Val.addfs Val.addf Val.subfs Val.subf Val.mulfs Val.mulf
    Val.divfs Val.divf.

  Local Arguments comp_of /.

  (* Calls *)
  Lemma allowed_call_preserved:
    forall j__δ cp v v'
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      v <> Vundef ->
      Val.inject j__δ v v' ->
      Genv.allowed_call ge1 cp v ->
      Genv.allowed_call ge3 cp v'.
  Proof.
    intros * inj_pres delta_zero nundef H allowed.
    exploit find_comp_preserved; eauto.
    intros same_comp.
    destruct allowed as [eq_comp | cross_call].
    - left; congruence.
    - right.
      inv H; auto; try congruence.
      exploit delta_zero; eauto; intros ->; rewrite Ptrofs.add_zero in *.
      clear nundef.
      destruct cross_call as [id [cp' [inv_symb ?]]].
      exists id, cp'. split.
      + apply Genv.invert_find_symbol in inv_symb.
        apply Genv.find_invert_symbol.
        exploit symbols_inject1; eauto; intros []; auto.
      + replace (Genv.genv_policy ge3) with (prog_pol W3) by (symmetry; apply Genv.genv_pol_add_globals).
        replace (Genv.genv_policy ge1) with (prog_pol W1) in * by (symmetry; apply Genv.genv_pol_add_globals).
        rewrite (match_prog_pol _ _ _ _ match_W1_W3), <- same_comp.
        destruct H as [? ?]. split; auto.
  Qed.
  (*       unfold Genv.find_funct, Genv.find_funct_ptr in *. *)
  (*       intros fd; specialize (H fd). *)
  (*       destruct (Ptrofs.eq_dec ofs1 Ptrofs.zero); try congruence. *)
  (*       destruct (Genv.find_def ge3 b2) as [[] |] eqn:?; try congruence. *)
  (*       exploit defs_rev_inject; eauto. *)
  (*       intros [? [? [? ?]]]. *)
  (*       rewrite H2 in H. inv H4. simpl. intros G. inv G. *)
  (*       inv H7; auto. specialize (H eq_refl). auto. *)
  (* Qed. *)

  Lemma update_stack_call_preserved_internal:
    forall j__δ sg rs1 rs3 st1 st1' st3 cp
      (delta_zero: mem_delta_zero j__δ),
      agrees_with j__δ (init_meminj W1 W3) ->
      (rs1 PC <> Vundef) ->
      Genv.find_comp ge1 (rs1 PC) = Some cp ->
      regset_rel j__δ rs1 rs3 ->
      update_stack_call ge1 st1 sg cp rs1 = Some st1' ->
      st1' = st1 /\
        update_stack_call ge3 st3 sg cp rs3 = Some st3.
  Proof.
    intros * delta_zero agr nundef samecomp rs1_rs3.
    unfold update_stack_call.
    rewrite samecomp, Pos.eqb_refl.
    intros R; inv R.
    split; eauto.
    exploit (agrees_with_init_meminj_find_comp_preserved s W1 W3); eauto.
    intros ->. rewrite Pos.eqb_refl; eauto.
  Qed.

  Lemma call_arguments_preserved:
    forall j__δ m1 m3 rs1 rs3,
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      regset_rel j__δ rs1 rs3 ->
      forall sig args, call_arguments rs1 m1 sig args ->
                  exists args', Val.inject_list j__δ args args'
                           /\ call_arguments rs3 m3 sig args'.
  Proof.
    intros * m1_m3 rs1_rs3 sig args H.
    unfold call_arguments in H.
    unfold call_arguments.
    induction H.
    - exists nil. split; auto. constructor.
    - assert (exists b1', Val.inject j__δ b1 b1' /\ call_arg_pair rs3 m3 a1 b1').
      { inv H.
        - inv H1.
          + specialize (rs1_rs3 (preg_of r)).
            exists (rs3 (preg_of r)). split; eauto. constructor; constructor.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            exists b1'; split. eauto. constructor. econstructor; eauto.
        - inv H1; inv H2.
          + pose proof (rs1_rs3 (preg_of r)).
            pose proof (rs1_rs3 (preg_of r0)).
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; constructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3. clear H1.
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            intros [b0' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto. }
      destruct IHlist_forall2 as [? [? ?]].
      destruct H1 as [? [? ?]].
      eexists (cons _ _); split.
      + constructor; eassumption.
      + constructor; eauto.
  Qed.

  Lemma call_trace_preserved:
    forall j__δ cp cp' v v' args args' sig t
      (agr: agrees_with j__δ (init_meminj W1 W3))
      (delta_zero: mem_delta_zero j__δ),
      Val.inject j__δ v v' ->
      Val.inject_list j__δ args args' ->
      (Genv.type_of_call cp cp' = Genv.CrossCompartmentCall -> Forall not_ptr args) ->
      call_trace ge1 cp cp' v args (sig_args sig) t ->
      call_trace ge3 cp cp' v' args' (sig_args sig) t.
  Proof.
    intros j__δ cp cp' v v' args args' sig t agr delta_zero inj_v inj_args NPTR EV.
    inv EV.
    - constructor; auto.
    - specialize (NPTR H).
      inv inj_v; eauto.
      econstructor; eauto. apply Genv.find_invert_symbol.
      apply Genv.invert_find_symbol in H1.
      eapply (symbols_inject2 _ _ W1 W3 (init_meminj W1 W3)) in H1;
        eauto using init_meminj_preserves_globals.
      destruct H1 as [? [? ?]]; eauto.
      exploit agr; eauto. intros []; subst; eauto.
      (* eapply Genv.invert_find_symbol; eauto. *)
      remember (sig_args sig) as tys.
      clear -inj_args NPTR H2.
      revert args args' tys vl inj_args NPTR H2.
      induction args;intros args' tys vl inj_args NPTR Hmatch.
      + inv inj_args; inv Hmatch; constructor.
      + inv inj_args; inv Hmatch; inv NPTR.
        constructor; eauto.
        inv H1; inv H5; try contradiction; econstructor; eauto.
  Qed.

  (* Returns *)
  Lemma update_stack_return_preserved_internal:
    forall j__δ rs1 rs3 st1 st1' st3 cp
      (agr: agrees_with j__δ (init_meminj W1 W3))
      (delta_zero: mem_delta_zero j__δ),
      (rs1 PC <> Vundef) ->
      Genv.find_comp ge1 (rs1 PC) = Some cp ->
      regset_rel j__δ rs1 rs3 ->
      update_stack_return ge1 st1 cp rs1 = Some st1' ->
      st1' = st1 /\
        update_stack_return ge3 st3 cp rs3 = Some st3.
  Proof.
    intros * agr delta_zero nundef samecomp rs1_rs3 (* st_rel *).
    unfold update_stack_return.
    rewrite samecomp, Pos.eqb_refl.
    intros R; inv R.
    split; eauto.
    exploit (agrees_with_init_meminj_find_comp_preserved s W1 W3); eauto.
    intros ->. rewrite Pos.eqb_refl. reflexivity.
  Qed.

  (* Builtins and external calls arguments *)
  Lemma eval_builtin_arg_inject:
    forall (rs: regset) m j__δ rs' m' a v
      (eval: eval_builtin_arg ge1 rs (rs X2) m a v)
      (* (agr: agrees_with j__δ (init_meminj W1 W3)) *)
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (m_m': mem_rel s ge1 ge3 j__δ δ m m')
      (delta_zero: mem_delta_zero j__δ),
      regset_rel j__δ rs rs' ->
      Mem.inject j__δ m m' ->
      exists v',
        eval_builtin_arg ge3 rs' (rs' X2) m' a v'
        /\ Val.inject j__δ v v'.
  Proof.
    induction 1; intros AGR MREL DZ RS MI.
    - exists rs'#x; split; auto. constructor.
    - econstructor; eauto with barg.
    - econstructor; eauto with barg.
    - econstructor; eauto with barg.
    - econstructor; eauto with barg.
    - specialize (RS X2); destruct (rs X2); inv RS; simpl in H; try congruence.
      exploit DZ; eauto; intros ->.
      rewrite Ptrofs.add_zero in *.
      exploit Mem.load_inject; eauto.
      intros (v' & A & B). exists v'; split; auto with barg.
      rewrite Z.add_0_r in A.
      econstructor. simpl; eauto.
    - econstructor; split; eauto with barg.
      eapply Val.offset_ptr_inject. now apply RS.
    - assert (Val.inject j__δ (Senv.symbol_address ge1 id ofs) (Senv.symbol_address ge3 id ofs)).
      { unfold Senv.symbol_address in *; simpl; unfold Genv.symbol_address in *.
        destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; auto.
        unfold Senv.find_symbol in H.
        simpl in H. rewrite FS in H.
        simpl in H.
        Local Transparent Mem.load.
        unfold Mem.load in H. Local Opaque Mem.load.
        destruct (Mem.valid_access_dec) as [e | n]; try congruence.
        unfold Mem.valid_access in e.
        destruct e as [_ [e ?]]. simpl in e.
        exploit symbols_inject2; eauto. intros (b' & A & B). rewrite A.
        econstructor; eauto. rewrite Ptrofs.add_zero; auto. }
      exploit Mem.loadv_inject; eauto. intros (v' & A & B).
      exists v'; split; auto with barg.
      econstructor. simpl; eauto.
    - econstructor; split; eauto with barg.
      unfold Senv.symbol_address; simpl.
    (* - econstructor; split; eauto with barg. *)
    (*   subst res. *)
    (*   unfold Genv.symbol_address; simpl; unfold Genv.symbol_address. *)
      destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; auto.
      exploit symbols_inject2; eauto. intros (b' & A & B). rewrite A.
      econstructor; eauto. now rewrite Ptrofs.add_zero.
      (* destruct (Genv.find_comp_of_block ge1 b) eqn:FB; auto. *)
      (* erewrite <- (find_comp_of_block_preserved s W1 W3); eauto. rewrite FB. *)
      (* destruct (cp =? c)%positive; auto. *)
      (* econstructor; eauto. now rewrite Ptrofs.add_zero. *)
      (* destruct (Genv.find_def ge1 b) as [[] |] eqn:?; auto. *)
      (* exploit defs_inject; eauto. *)
      (* intros ([] & ? & _ & ? & ?). rewrite H. *)
      (* econstructor; eauto. now rewrite Ptrofs.add_zero. *)
      (* inv H0. *)
    - destruct IHeval1 as (v1' & A1 & B1); eauto using in_or_app.
      destruct IHeval2 as (v2' & A2 & B2); eauto using in_or_app.
      exists (Val.longofwords v1' v2'); split; auto with barg.
      apply Val.longofwords_inject; auto.
    - destruct IHeval1 as (v1' & A1 & B1); eauto using in_or_app.
      destruct IHeval2 as (v2' & A2 & B2); eauto using in_or_app.
      econstructor; split; eauto with barg.
      destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
  Qed.

  Lemma eval_builtin_args_inject:
    forall (rs: regset) m j__δ rs' m' al vl
      (eval: eval_builtin_args ge1 rs (rs X2) m al vl)
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (* (agr: agrees_with j__δ (init_meminj W1 W3)) *)
      (m_m': mem_rel s ge1 ge3 j__δ δ m m')
      (delta_zero: mem_delta_zero j__δ),
      regset_rel j__δ rs rs' ->
      Mem.inject j__δ m m' ->
      (* (forall id, In id (globals_of_builtin_args al) -> kept id) -> *)
      exists vl',
        eval_builtin_args ge3 rs' (rs' X2) m' al vl'
        /\ Val.inject_list j__δ vl vl'.
  Proof.
    induction 1; intros.
    - exists (@nil val); split; constructor.
    - exploit eval_builtin_arg_inject; eauto using in_or_app. intros (v1' & A & B).
      destruct IHeval as (vl' & C & D); eauto using in_or_app.
      exists (v1' :: vl'); split; constructor; auto.
  Qed.

  Lemma extcall_arguments_preserved:
    forall j__δ δ m1 m3 rs1 rs3,
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      regset_rel j__δ rs1 rs3 ->
      forall sig args, extcall_arguments rs1 m1 sig args ->
                  exists args', Val.inject_list j__δ args args'
                           /\ extcall_arguments rs3 m3 sig args'.
  Proof.
    intros * m1_m3 rs1_rs3 sig args H.
    unfold extcall_arguments in H.
    unfold extcall_arguments.
    induction H.
    - exists nil. split; auto. constructor.
    - assert (exists b1', Val.inject j__δ b1 b1' /\ extcall_arg_pair rs3 m3 a1 b1').
      { inv H.
        - inv H1.
          + specialize (rs1_rs3 (preg_of r)).
            exists (rs3 (preg_of r)). split; eauto. constructor; constructor.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            exists b1'; split. eauto. constructor. econstructor; eauto.
        - inv H1; inv H2.
          + pose proof (rs1_rs3 (preg_of r)).
            pose proof (rs1_rs3 (preg_of r0)).
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; constructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3. clear H1.
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            intros [b0' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto. }
      destruct IHlist_forall2 as [? [? ?]].
      destruct H1 as [? [? ?]].
      eexists (cons _ _); split.
      + constructor; eassumption.
      + constructor; eauto.
  Qed.


  (* External calls preserved *)
  Lemma external_call_inject_left:
    forall ef vargs m1 t vres m2 j__δ j__oppδ m1' vargs' m3 rs1 rs3 st1 st2 st3,
      s (comp_of ef) = δ ->
      meminj_preserves_globals s δ W1 W3 j__δ ->
      (* agrees_with j__δ (init_meminj W1 W3) -> *)
      external_call ef ge1 vargs m1 t vres m1' ->
      Val.inject_list j__δ vargs vargs' ->

      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      stack_rel s ge3 δ j__δ j__oppδ st1 st2 st3 ->

      exists j__δ', exists vres', exists m3',
        external_call ef ge3 vargs' m3 t vres' m3'
        /\ Val.inject j__δ' vres vres'
        /\ Mem.unchanged_on (loc_unmapped j__δ) m1 m1'
        /\ Mem.unchanged_on (loc_out_of_reach j__δ m1) m3 m3'
        /\ inject_incr j__δ j__δ'
        /\ inject_separated j__δ j__δ' m1 m3 /\
      (* agrees_with j__δ' (init_meminj W1 W3) /\ *)
          meminj_preserves_globals s δ W1 W3 j__δ' /\
          mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
          mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
          regset_rel j__δ' rs1 rs3 /\
          stack_rel s ge3 δ j__δ' j__oppδ st1 st2 st3.
  Proof.
    intros * s_ef inj_pres extcall1 inj_args m1_m3 m2_m3 rs1_rs3 st_rel.
    exploit external_call_mem_inject_gen;
      eauto using globals_symbols_inject, partial_mem_inject.
    intros
      (j__δ' & vres' & m3' & extcall3 & inj_res & inj_mem & unchanged1 & unchanged2 & incr & inj_sep & comp_new).

    eexists; eexists; eexists; intuition eauto.
    - assert (meminj_preserves_globals s δ W1 W3 j__δ ->
              mem_rel s ge1 ge3 j__δ δ m1 m3 ->
              inject_incr j__δ j__δ' ->
              inject_separated j__δ j__δ' m1 m3 ->
              meminj_preserves_globals s δ W1 W3 j__δ').
      { clear. intros m1_m3 inj_pres incr inj_sep.
        constructor.
        - (* symbols_inject1 *)
          intros.
          exploit symbols_inject2; eauto.
          intros [? [? ?]]. eapply symbols_inject1; eauto.
          erewrite (incr b) in *; eauto. congruence.
        - (* symbols_inject2 *)
          intros.
          exploit symbols_inject2; eauto.
          intros [? [? ?]].
          now erewrite (incr b) in *; eauto.
        - (* symbols_inject3 *)
          intros.
          exploit symbols_inject3; eauto.
          intros [? [? ?]]. eexists.
          erewrite (incr x) in *; eauto.
        - (* defs_inject *)
          intros. exploit defs_inject; eauto.
          destruct (j__δ b) as [[] |] eqn:j_b; [erewrite (incr b) in *; eauto |].
          exfalso.
          exploit inj_sep; eauto. exploit find_def_valid1; eauto. intros ? [? ?]; congruence.
        - (* defs_rev_inject *)
          intros. exploit defs_rev_inject; eauto.
          destruct (j__δ b) as [[] |] eqn:j_b; [erewrite (incr b) in *; eauto |].
          exfalso.
          exploit inj_sep; eauto. exploit find_def_valid2; eauto. intros ? [? ?]; congruence. }
      eauto.
    - exploit extcall_preserves_mem_rel_same_side; eauto.
    - exploit extcall_preserves_mem_rel_opp_side2; eauto.
      now destruct δ.
    - intros x. exploit val_inject_incr; eauto.
    - exploit inject_incr_stack_rel1; eauto.
      Admitted.
  (* Qed. *)

  (* Lemmas about correct register invalidation *)
  Lemma regset_rel_return_from_builtin:
    forall j rs1 rs2 vres vres' ef res
      (RES_NOT_PC : exists reg : builtin_res mreg, res = map_builtin_res preg_of reg),
      regset_rel j rs1 rs2 ->
      Val.inject j vres vres' ->
      regset_rel j
        (nextinstr (set_res res vres (undef_regs (map preg_of (destroyed_by_builtin ef)) (rs1 # X1 <- Vundef) # X31 <- Vundef)))
        (nextinstr (set_res res vres' (undef_regs (map preg_of (destroyed_by_builtin ef)) (rs2 # X1 <- Vundef) # X31 <- Vundef))).
  Proof.
    intros j rs1 rs2 vres vres' ef res RES_NOT_PC H res_inj.
    apply regset_rel_inject; auto.
    - assert (H': regset_rel j
                    (undef_regs (map preg_of (destroyed_by_builtin ef)) (rs1 # X1 <- Vundef) # X31 <- Vundef)
                    (undef_regs (map preg_of (destroyed_by_builtin ef)) (rs2 # X1 <- Vundef) # X31 <- Vundef)).
      { remember (map preg_of (destroyed_by_builtin ef)) as pregs eqn:X. clear X.
        assert (rel: regset_rel j ((rs1 # X1 <- Vundef) # X31 <- Vundef) ((rs2 # X1 <- Vundef) # X31 <- Vundef)).
        { do 2 (apply regset_rel_inject; auto). }
        remember ((rs2 # X1 <- Vundef) # X31 <- Vundef) as regs'.
        remember ((rs1 # X1 <- Vundef) # X31 <- Vundef) as regs.
        clear -rel.
        revert regs regs' rel.
        induction pregs.
        - now auto.
        - intros. simpl. apply IHpregs. apply regset_rel_inject; auto. }
      remember (undef_regs (map preg_of (destroyed_by_builtin ef)) (rs1 # X1 <- Vundef) # X31 <- Vundef)
        as regs1 eqn:X; clear X.
      remember (undef_regs (map preg_of (destroyed_by_builtin ef)) (rs2 # X1 <- Vundef) # X31 <- Vundef)
        as regs2 eqn:X; clear X.
      clear -res_inj H'.
      revert regs1 regs2 vres vres' res_inj H'.
      induction res; intros.
      + simpl; apply regset_rel_inject; auto.
      + simpl; auto.
      + simpl; auto. apply IHres2; auto using Val.loword_inject.
        eapply IHres1; auto using Val.hiword_inject.
    - destruct RES_NOT_PC as [reg ?]; subst res.
      assert (H': Asmgenproof0.preg_notin PC (destroyed_by_builtin ef)).
      { Local Transparent destroyed_by_builtin.
        unfold destroyed_by_builtin.
        destruct ef; simpl; auto.
        - destruct orb; simpl; intuition.
          destruct orb; simpl; intuition.
        - intuition.
        - induction clobbers.
          + simpl; auto.
          + simpl. destruct register_by_name; auto.
            simpl; intuition.
            destruct (destroyed_by_clobber clobbers); [| split]; now destruct m.
            Local Opaque destroyed_by_builtin. }
      rewrite 2!Asmgenproof0.set_res_other; auto.
      rewrite 2!Asmgenproof0.undef_regs_other_2; auto.
      Simpl. apply Val.offset_ptr_inject. now apply H.
  Qed.

  Lemma regset_rel_return_from_external:
    forall j rs1 rs2 ef res1 res2,
      regset_rel j rs1 rs2 ->
      Val.inject j res1 res2 ->
      regset_rel j ((set_pair (loc_external_result (ef_sig ef)) res1 (undef_caller_save_regs rs1)) # PC <- (rs1 X1))
        ((set_pair (loc_external_result (ef_sig ef)) res2 (undef_caller_save_regs rs2)) # PC <- (rs2 X1)).
  Proof.
    intros j rs1 rs2 ef res1 res2 H H0.
    eapply regset_rel_inject; eauto.
    destruct (loc_external_result (ef_sig ef)).
    - eapply regset_rel_inject; eauto.
      { unfold undef_caller_save_regs.
        intros x. destruct orb; auto. }
    - eapply regset_rel_inject; eauto using Val.loword_inject.
      eapply regset_rel_inject; eauto using Val.hiword_inject.
      { unfold undef_caller_save_regs.
        intros x. destruct orb; auto. }
  Qed.
