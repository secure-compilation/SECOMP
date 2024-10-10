Require Import Coqlib Maps Errors Integers.
Require Import Integers Floats AST Linking.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.
Require Import Op Locations Mach Conventions Asm.
Require Import Complements.

Require Import Split.

(* This is trivial *)
Lemma filter_all_mregs_find_one:
  forall r, r :: nil = filter (fun x0 : mreg => mreg_eq x0 r || false) all_mregs.
Proof.
  intros r.
  Local Transparent mreg_eq.
  destruct r; compute; trivial.
Qed.

Lemma filter_all_mregs_find_two:
  forall rhi rlo,
    rhi :: rlo :: nil =
      filter (fun x0 : mreg => mreg_eq x0 rhi || (mreg_eq x0 rlo || false)) all_mregs \/
      rlo :: rhi :: nil =
        filter (fun x0 : mreg => mreg_eq x0 rhi || (mreg_eq x0 rlo || false)) all_mregs \/
      rlo :: nil =
        filter (fun x0 : mreg => mreg_eq x0 rhi || (mreg_eq x0 rlo || false)) all_mregs.
Proof.
  intros rhi rlo.
  Local Transparent mreg_eq.
  destruct rhi, rlo; compute; auto.
Qed.

Lemma eq_distributes_longofwords:
  forall a b a' b',
    not_ptr (Val.longofwords a b) ->
    not_ptr (Val.longofwords a' b') ->
    Val.longofwords a b = Val.longofwords a' b' ->
    a = a' /\ b = b'.
Proof.
  intros a b a' b'.
  unfold Val.longofwords.
  destruct a, a'; simpl; try contradiction.
  destruct b, b'; simpl; try contradiction.
  intros _ _.
  unfold Int64.ofwords; simpl.
  rewrite 2!Int64.shifted_or_is_add.
  - simpl. intros H.
    assert (Int64.repr
              (Int64.unsigned (Int64.repr (Int.unsigned i)) * two_power_pos 32
               + Int64.unsigned (Int64.repr (Int.unsigned i1))) =
              Int64.repr (Int64.unsigned (Int64.repr (Int.unsigned i0)) * two_power_pos 32 +
                            Int64.unsigned (Int64.repr (Int.unsigned i2)))) as G.
    congruence.
    clear H.
    revert G.
    rewrite !Int64.unsigned_repr_eq.
    unfold Int64.modulus, Int.modulus; simpl. unfold two_power_nat, two_power_pos. simpl.
    unfold Int.unsigned. destruct i, i1, i0, i2; simpl.
    intros H.
    assert (intval = intval1 /\ intval0 = intval2) as [? ?].
    unfold Int.modulus, two_power_nat in *; simpl in *.
    rewrite !Z.mod_small in H; try lia.
    Local Transparent Int64.repr.
    unfold Int64.repr in H. inv H.
    rewrite !Int64.Z_mod_modulus_eq in H1.
    unfold Int64.modulus, two_power_nat in H1. simpl in H1.
    rewrite !Z.mod_small in H1; try lia.
    subst.
    assert (intrange = intrange1); subst.
    { eapply Axioms.proof_irr. }
    assert (intrange0 = intrange2); subst.
    { eapply Axioms.proof_irr. }
    split; auto.
  - unfold Int.zwordsize, Int64.zwordsize; simpl. lia.
  - rewrite Int64.unsigned_repr_eq. pose proof (Int.unsigned_range i2) as H. revert H.
    unfold Int64.modulus, Int.modulus; simpl. unfold two_power_nat, two_power_pos. simpl.
    rewrite Z.mod_small; try lia.
    pose proof (Int.unsigned_range i2) as H. unfold Int.modulus, two_power_nat in H; simpl in H.
    lia.
  - unfold Int.zwordsize, Int64.zwordsize; simpl. lia.
  - rewrite Int64.unsigned_repr_eq. pose proof (Int.unsigned_range i1) as H. revert H.
    unfold Int64.modulus, Int.modulus; simpl. unfold two_power_nat, two_power_pos. simpl.
    rewrite Z.mod_small; try lia.
    pose proof (Int.unsigned_range i1) as H. unfold Int.modulus, two_power_nat in H; simpl in H.
    lia.
    Local Opaque Int64.repr.
Qed.

Lemma inject_distributes_longofwords:
  forall j a b a' b',
    not_ptr (Val.longofwords a b) ->
    not_ptr (Val.longofwords a' b') ->
    Val.inject j (Val.longofwords a b) (Val.longofwords a' b') ->
    Val.inject j a a' /\ Val.inject j b b'.
Proof.
  intros.
  assert (Val.longofwords a b = Val.longofwords a' b').
  { revert H H0. unfold Val.longofwords.
    destruct a, a'; simpl; try contradiction.
    destruct b, b'; simpl; try contradiction.
    simpl in H1.
    revert H1.
    generalize (Int64.ofwords i i1).
    generalize (Int64.ofwords i0 i2).
    intros ? ? G. inv G; auto. }
  clear H1.
  eapply eq_distributes_longofwords in H2; eauto. destruct H2; subst.
  unfold not_ptr in *. revert H.
  unfold Val.longofwords.
  destruct a', b'; simpl; try contradiction. intros _. split; constructor.
Qed.


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
      | Some (Gfun fd) => true
      | Some (Gvar v) => side_eq (s (comp_of v)) δ
      end
  | None => false
  end.

Definition kept_prog (s: split) (p: program) (δ: side) (id: ident): bool :=
  match Genv.find_symbol (Genv.globalenv p) id with
  | Some b =>
      match (Genv.genv_defs (Genv.globalenv p))!b with
      | None => false
      | Some (Gfun (External ef)) => true
      | Some gd => side_eq (s (comp_of gd)) δ
      end
  | None => false
  end.

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

  Hypothesis senv_public: forall id,
      Senv.public_symbol ge__recomp id = Senv.public_symbol ge id.

  Hypothesis senv_wf: forall id cp b,
      Senv.find_symbol ge id = Some b ->
      Senv.find_comp ge id ⊆ cp ->
      exists fd, Genv.find_def ge b = Some fd.

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
    destruct (kept_prog s p δ id) eqn:kept.
    - erewrite match_prog_def in P by eauto.
      apply Genv.find_symbol_exists with g.
      apply in_prog_defmap. auto.
    - exploit match_prog_notdef; eauto.
      intros G; inv G; try congruence.
      eapply Genv.find_symbol_exists.
      apply in_prog_defmap; eauto.
  Qed.

  Hypothesis match_prog_comp_of_main:
    comp_of_main p__recomp = comp_of_main p.


  (** Injections that preserve used globals. *)
  Record meminj_preserves_globals (j: meminj): Prop := {
      symbols_inject1: forall id b b' delta,
        j b = Some (b', delta) ->
        Genv.find_symbol ge id = Some b ->
        delta = 0 /\ Genv.find_symbol ge__recomp id = Some b';
      symbols_inject2: forall id b,
        Genv.find_symbol ge id = Some b ->
        kept_genv s ge δ id = true ->
        exists b', Genv.find_symbol ge__recomp id = Some b' /\ j b = Some(b', 0);
      symbols_inject3: forall id b',
        Genv.find_symbol ge__recomp id = Some b' ->
        kept_genv s ge δ id = true ->
        exists b, Genv.find_symbol ge id = Some b /\ j b = Some (b', 0);
      defs_inject: forall b b' delta gd,
        j b = Some(b', delta) -> Genv.find_def ge b = Some gd ->
        exists gd', Genv.find_def ge__recomp b' = Some gd' /\
                 delta = 0 /\
                 match_globdef gd gd' /\
                 (forall id, Genv.find_symbol ge id = Some b -> kept_prog s p δ id = true ->
                        gd' = gd);
      defs_rev_inject: forall b b' delta gd,
        j b = Some(b', delta) -> Genv.find_def ge__recomp b' = Some gd ->
        exists gd', Genv.find_def ge b = Some gd' /\ delta = 0 /\ match_globdef gd' gd;
    }.

  Definition init_meminj: meminj :=
    fun b =>
      match Genv.invert_symbol ge b with
      | Some id =>
          if kept_genv s ge δ id then
            match Genv.find_symbol ge__recomp id with
            | Some b' => Some (b', 0)
            | None => None
            end
          else
            None
      | None => None
      end.

  Remark init_meminj_eq:
    forall id b b',
      Genv.find_symbol ge id = Some b -> Genv.find_symbol ge__recomp id = Some b' ->
      kept_genv s ge δ id = true ->
      init_meminj b = Some(b', 0).
  Proof.
    intros. unfold init_meminj. erewrite Genv.find_invert_symbol by eauto.
    rewrite H0, H1. auto.
  Qed.

  Remark init_meminj_invert:
    forall b b' delta,
      init_meminj b = Some(b', delta) ->
      delta = 0 /\ exists id, Genv.find_symbol ge id = Some b /\ Genv.find_symbol ge__recomp id = Some b'.
  Proof.
    unfold init_meminj; intros.
    destruct (Genv.invert_symbol ge b) as [id|] eqn:S; try discriminate.
    destruct (kept_genv s ge δ id) eqn:T; try discriminate.
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
      destruct (kept_prog s p δ id) eqn:kept.
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
        assert (id = id') by congruence; subst id'. intros ?. congruence.
    - exploit init_meminj_invert; eauto. intros (A & id & B & C).
      destruct (kept_prog s p δ id) eqn:kept.
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
      kept_genv s ge δ id = true ->
      Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address ge__recomp id ofs).
  Proof.
    intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    exploit symbols_inject2; eauto. intros (b' & TFS & INJ). rewrite TFS.
    econstructor; eauto. rewrite Ptrofs.add_zero; auto.
  Qed.

  Hypothesis no_bottom1': forall b v,
      Genv.find_def ge b = Some (Gvar v) ->
      comp_of v <> bottom.
  Hypothesis no_top1': forall b v,
      Genv.find_def ge b = Some (Gvar v) ->
      comp_of v <> top.

  Lemma globals_symbols_inject (cp: compartment) (not_top: cp <> top) (side_cp: s cp = δ):
    forall j, meminj_preserves_globals j -> symbols_inject j ge ge__recomp cp.
  Proof.
    intros.
    assert (E1: Genv.genv_public ge = p.(prog_public)).
    { unfold ge. apply Genv.globalenv_public. }
    assert (E2: Genv.genv_public ge__recomp = p.(prog_public)).
    { unfold ge__recomp; rewrite Genv.globalenv_public. eapply match_prog_public; eauto. }
    split; [| split; [| split; [| split]]]; intros.
    + eapply senv_public.
    + eapply symbols_inject1; eauto.
    + simpl in *; unfold Genv.public_symbol in H0.
      destruct (Genv.find_symbol ge id) as [b|] eqn:FS; try discriminate.
      rewrite E1 in H0.
      destruct (in_dec ident_eq id (prog_public p)); try discriminate. inv H1.
      exploit symbols_inject2; eauto.
      { unfold kept_genv. rewrite FS.
        exploit senv_wf; eauto. unfold Genv.find_def; intros ([] & R); rewrite R; auto.
        revert H2. unfold Genv.to_map_ident, ge, ge__recomp, Genv.globalenv.
        rewrite Genv.genv_pol_add_globals.
        unfold prog_pol_pub. simpl.
        pose proof (prog_agr_comps p) as G.
        unfold agr_comps in G. rewrite Forall_forall in G.
        specialize (G (id, Gvar v)).
        assert (X: In (id, Gvar v) (prog_defs p)).
        { apply in_prog_defmap.
          rewrite Genv.find_def_symbol. eexists; split; eauto. }
        destruct ((Policy.policy_comps (prog_pol p)) ! id) as [c |] eqn:EQ.
        - specialize (G X c EQ). simpl in G.
          assert (exists cp', comp_of v = Comp cp') as [cp' ?].
          { destruct (comp_of v) eqn:?; try now eauto.
            exploit no_bottom1'; eauto; contradiction.
            exploit no_top1'; eauto; contradiction. }
          intros A.
          assert (c <> top). { intros ->. inv A; try contradiction. }
          rewrite H1 in G.
          assert (c = Comp cp'). { inv G; try contradiction. reflexivity. }
          subst c.
          inv A; try contradiction. rewrite H1, side_cp.
          now destruct side_eq.
        - exploit prog_pol_complete; eauto.
          intros Y. unfold pol_complete in Y. eapply Forall_forall in Y; eauto.
          destruct Y as [? ?]; simpl in *; congruence. }
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
    + simpl. unfold Genv.to_map_ident. unfold ge, ge__recomp, Genv.globalenv.
      do 2 rewrite Genv.genv_pol_add_globals.
      unfold prog_pol_pub. simpl.
      erewrite <- match_prog_pol; eauto.
  Qed.

End MEMINJ.

Section Invariants.
  Variable s: split.
  Variable cp_main: compartment.

  Definition same_content_stack m1 m3 sp1 sp3 sg :=
    forall ofs ty,
      forall bofs,
        bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
        Stacklayout.is_valid_param_loc sg bofs ty ->
      (* (In (One (S Incoming ofs ty)) (loc_parameters sg) \/ *)
      (*    (exists l, In (Twolong (S Incoming ofs ty) l) (loc_parameters sg)) \/ *)
      (*    (exists l, In (Twolong l (S Incoming ofs ty)) (loc_parameters sg))) -> *)
      (* forall bofs, bofs = Stacklayout.fe_ofs_arg + 4 * ofs -> *)
        (forall b o, sp1 = Vptr b o ->
                Mem.range_perm m1 b (Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr bofs)))
                  (Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr bofs)) + size_chunk (chunk_of_type ty))
                  (* (Ptrofs.unsigned o + bofs + size_chunk (chunk_of_type ty)) *) Cur Readable) /\
          forall v, Mem.loadv (chunk_of_type ty) m1
                 (Val.offset_ptr sp1 (Ptrofs.repr bofs)) top = Some v ->
               not_ptr v /\ Mem.loadv (chunk_of_type ty) m3
                             (Val.offset_ptr sp3 (Ptrofs.repr bofs)) top = Some v.

  Definition at_most_readable (m: mem) (sp: val) :=
    match sp with
    | Vptr b _ => Mem.valid_block m b /\ forall ofs, not (Mem.perm m b ofs Max Writable)
    | _ => False
    end.

  Definition nonempty (m: mem) (sp: val) :=
    match sp with
    | Vptr b _ => Mem.perm m b 0 Max Nonempty
    | _ => False
    end.

  Definition not_fundef (ge: genv) (m: mem) (sp: val) :=
    match sp with
    | Vptr b _ => forall fd, Genv.find_def ge b <> Some (Gfun fd)
    | _ => False
    end.

  Definition empty_perm (m: mem) (b: block) :=
    Mem.valid_block m b /\ forall ofs, not (Mem.perm m b ofs Max Nonempty).

  Definition comp_sp_ok (m: mem) (sp: val) (cp: compartment) :=
    match sp with
    | Vptr b _ => Mem.block_compartment m b = cp
    | _ => True
    end.


  Variant stackframe_rel (ge1: genv) (ge2: genv) (ge3: genv) (δ: side)
    (j__δ j__oppδ: meminj) (m1 m2 m3: mem):
    stackframe -> stackframe -> stackframe -> Prop :=
    | stackframe_related_δ: forall cp cp' sg b1 b2 b3 sp1 sp2 sp3 ofs1 ofs2 ofs3
                              dummy_ra1 dummy_ra2 dummy_ra3 dummy_sp1 dummy_sp2 dummy_sp3,
        forall (NOTOP1: Genv.find_comp_of_block ge1 b1 <> top),
        forall (NOTOP2: Genv.find_comp_of_block ge2 b2 <> top),
        forall (NOTOP3: Genv.find_comp_of_block ge3 b3 <> top),
        forall (NOBOTTOM1: Genv.find_comp_of_block ge1 b1 <> bottom),
        forall (NOBOTTOM2: Genv.find_comp_of_block ge2 b2 <> bottom),
        forall (NOBOTTOM3: Genv.find_comp_of_block ge3 b3 <> bottom),
        Genv.find_comp_of_block ge3 b3 = cp ->
          s cp = δ ->
          Val.inject j__δ (Vptr b1 ofs1) (Vptr b3 ofs3) ->
          Val.inject j__δ sp1 sp3 ->
          Val.inject (if side_eq (s cp') δ then j__δ else j__oppδ)
            (Vptr (if side_eq (s cp') δ then dummy_ra1 else dummy_ra2) Ptrofs.zero)
            (Vptr dummy_ra3 Ptrofs.zero) ->
          Val.inject (if side_eq (s cp') δ then j__δ else j__oppδ)
            (Vptr (if side_eq (s cp') δ then dummy_sp1 else dummy_sp2) Ptrofs.zero) (Vptr dummy_sp3 Ptrofs.zero) ->
          forall (STACK_CONTENT1: same_content_stack m1 m3 sp1 sp3 sg),
          forall (STACK_CONTENT2: same_content_stack m2 m3 sp2 sp3 sg),
          forall (PERM1: at_most_readable m1 sp1),
          forall (PERM2: at_most_readable m2 sp2),
          forall (PERM3: at_most_readable m3 sp3),
          forall (NONEMPTY1: nonempty m1 sp1),
          forall (NONEMPTY2: nonempty m2 sp2),
          forall (NONEMPTY3: nonempty m3 sp3),
          forall (FD3: not_fundef ge1 m1 sp1),
          forall (FD3: not_fundef ge2 m2 sp2),
          forall (FD3: not_fundef ge3 m3 sp3),
          forall (EMPTY1: empty_perm m1 dummy_sp1),
          forall (EMPTY2: empty_perm m2 dummy_sp2),
          forall (EMPTY3: empty_perm m3 dummy_sp3),
            stackframe_rel ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3
              (Stackframe b1 sg cp' sp1 ofs1 dummy_ra1 dummy_sp1)
              (Stackframe b2 sg cp' sp2 ofs2 dummy_ra2 dummy_sp2)
              (Stackframe b3 sg cp' sp3 ofs3 dummy_ra3 dummy_sp3)
    | stackframe_related_opp_δ: forall cp cp' sg b1 b2 b3 sp1 sp2 sp3 ofs1 ofs2 ofs3
                                  dummy_ra1 dummy_ra2 dummy_ra3 dummy_sp1 dummy_sp2 dummy_sp3,
        forall (NOTOP1: Genv.find_comp_of_block ge1 b1 <> top),
        forall (NOTOP2: Genv.find_comp_of_block ge2 b2 <> top),
        forall (NOTOP3: Genv.find_comp_of_block ge3 b3 <> top),
        forall (NOBOTTOM1: Genv.find_comp_of_block ge1 b1 <> bottom),
        forall (NOBOTTOM2: Genv.find_comp_of_block ge2 b2 <> bottom),
        forall (NOBOTTOM3: Genv.find_comp_of_block ge3 b3 <> bottom),
        Genv.find_comp_of_block ge3 b3 = cp ->
          s cp = opposite δ ->
          Val.inject j__oppδ (Vptr b2 ofs2) (Vptr b3 ofs3) ->
          Val.inject j__oppδ sp2 sp3 ->
          Val.inject (if side_eq (s cp') δ then j__δ else j__oppδ)
            (Vptr (if side_eq (s cp') δ then dummy_ra1 else dummy_ra2) Ptrofs.zero)
            (Vptr dummy_ra3 Ptrofs.zero) ->
          Val.inject (if side_eq (s cp') δ then j__δ else j__oppδ)
            (Vptr (if side_eq (s cp') δ then dummy_sp1 else dummy_sp2) Ptrofs.zero) (Vptr dummy_sp3 Ptrofs.zero) ->
          forall (STACK_CONTENT1: same_content_stack m1 m3 sp1 sp3 sg),
          forall (STACK_CONTENT2: same_content_stack m2 m3 sp2 sp3 sg),
          forall (PERM1: at_most_readable m1 sp1),
          forall (PERM2: at_most_readable m2 sp2),
          forall (PERM3: at_most_readable m3 sp3),
          forall (NONEMPTY1: nonempty m1 sp1),
          forall (NONEMPTY2: nonempty m2 sp2),
          forall (NONEMPTY3: nonempty m3 sp3),
          forall (FD3: not_fundef ge1 m1 sp1),
          forall (FD3: not_fundef ge2 m2 sp2),
          forall (FD3: not_fundef ge3 m3 sp3),
          forall (EMPTY1: empty_perm m1 dummy_sp1),
          forall (EMPTY2: empty_perm m2 dummy_sp2),
          forall (EMPTY3: empty_perm m3 dummy_sp3),
            stackframe_rel ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3
              (Stackframe b1 sg cp' sp1 ofs1 dummy_ra1 dummy_sp1)
              (Stackframe b2 sg cp' sp2 ofs2 dummy_ra2 dummy_sp2)
              (Stackframe b3 sg cp' sp3 ofs3 dummy_ra3 dummy_sp3)
  .

  Inductive stack_rel (ge1 ge2: genv) (ge3: genv) (δ: side) (j__δ j__oppδ: meminj) m1 m2 m3: stack -> stack -> stack -> Prop :=
  | stack_rel_empty:
    stack_rel ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 nil nil nil
  | stack_rel_cons: forall st1 st2 st3 f1 f2 f3,
      stack_rel ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      stackframe_rel ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 f1 f2 f3 ->
      callee_comp cp_main st3 = call_comp ge3 (f3 :: st3) ->
      forall (DIFF1: diff_sp st1 f1),
      forall (DIFF1: diff_sp st2 f2),
      forall (DIFF1: diff_sp st3 f3),
      forall (DIFF: callee_comp cp_main st3 <> callee_comp cp_main (f3 :: st3)),
        stack_rel ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 (f1 :: st1) (f2 :: st2) (f3 :: st3)
  .

  Lemma stack_rel_comm ge1 ge2 (ge3: genv) (δ: side) (j__δ j__oppδ: meminj) m1 m2 m3:
    forall st1 st2 st3,
      stack_rel ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      stack_rel ge2 ge1 ge3 (opposite δ) j__oppδ j__δ m2 m1 m3 st2 st1 st3.
  Proof.
    intros st1 st2 st3 H.
    induction H.
    - constructor.
    - econstructor; eauto.
      inv H0.
      + eapply stackframe_related_opp_δ; eauto.
        now destruct s.
        destruct (s cp'), (s (Genv.find_comp_of_block _ _)); eauto; congruence.
        destruct (s cp'), (s (Genv.find_comp_of_block _ _)); eauto; congruence.
      + eapply stackframe_related_δ; eauto.
        destruct δ, (s cp'); eauto; congruence.
        destruct δ, (s cp'); eauto; congruence.
  Qed.

  Lemma inject_incr_stack_rel1:
    forall ge1 ge2 ge3 δ j1 j1' j2 m1 m2 m3 st1 st2 st3,
      inject_incr j1 j1' ->
      stack_rel ge1 ge2 ge3 δ j1 j2 m1 m2 m3 st1 st2 st3 ->
      stack_rel ge1 ge2 ge3 δ j1' j2 m1 m2 m3 st1 st2 st3.
  Proof.
    intros * incr st_rel.
    induction st_rel.
    - constructor; eauto.
    - econstructor; eauto.
      inv H.
      + econstructor; eauto.
        destruct (side_eq); eauto.
        destruct (side_eq); eauto.
      + eapply stackframe_related_opp_δ; eauto.
        destruct (side_eq); eauto.
        destruct (side_eq); eauto.
  Qed.

  Lemma inject_incr_stack_rel2:
    forall ge1 ge2 ge3 δ j1 j2' j2 m1 m2 m3 st1 st2 st3,
      inject_incr j2 j2' ->
      stack_rel ge1 ge2 ge3 δ j1 j2 m1 m2 m3 st1 st2 st3 ->
      stack_rel ge1 ge2 ge3 δ j1 j2' m1 m2 m3 st1 st2 st3.
  Proof.
    intros * incr st_rel.
    induction st_rel.
    - constructor; eauto.
    - econstructor; eauto.
      inv H.
      + econstructor; eauto.
        destruct (side_eq); eauto.
        destruct (side_eq); eauto.
      + eapply stackframe_related_opp_δ; eauto.
        destruct (side_eq); eauto.
        destruct (side_eq); eauto.
  Qed.

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
    forall b, (j b <> None <-> ((s, m) |= b ∈ δ /\ Mem.valid_block m b) \/ exists fd, Genv.find_def ge b = Some (Gfun fd)).

  Definition mem_delta_zero (j: meminj): Prop :=
    forall loc loc' delta, j loc = Some (loc', delta) -> delta = 0.

  Record mem_rel (ge1 ge2: genv) (j: meminj) (δ: side) (m1 m2: mem) :=
    { (* Uncomment as needed *)
      same_dom: same_domain s ge1 j δ m1;

      partial_mem_inject: Mem.inject j m1 m2;

      delta_zero: mem_delta_zero j;

      perm_compartment1: forall b ofs,
        Mem.perm m1 b ofs Max Nonempty ->
        exists cp', Mem.block_compartment m1 b = Comp cp';
      perm_compartment2: forall b ofs,
        Mem.perm m2 b ofs Max Nonempty ->
        exists cp', Mem.block_compartment m2 b = Comp cp';



      ple_nextblock1: Ple (Senv.nextblock ge1) (Mem.nextblock m1);
      ple_nextblock2: Ple (Senv.nextblock ge2) (Mem.nextblock m2);

      (* Find def valid *)
      find_def_valid1: forall b gd, Genv.find_def ge1 b = Some gd -> Mem.valid_block m1 b;
      find_def_valid2: forall b gd, Genv.find_def ge2 b = Some gd -> Mem.valid_block m2 b;

      (* Functions perm *)
      find_def_perm1: forall b fd, Genv.find_def ge1 b = Some (Gfun fd) -> forall ofs, not (Mem.perm m1 b ofs Max Readable);
      find_def_perm2: forall b fd, Genv.find_def ge2 b = Some (Gfun fd) -> forall ofs, not (Mem.perm m2 b ofs Max Readable);

      (* var comp *)
      find_var_comp1: forall b v, Genv.find_def ge1 b = Some (Gvar v) -> Mem.block_compartment m1 b = comp_of v;

      (* injective *)
      meminj_injective: forall (b0 b4 b1' b2' : block) (delta1 delta2 : Z),
        b0 <> b4 -> j b0 = Some (b1', delta1) -> j b4 = Some (b2', delta2) -> b1' <> b2';

      (* same_high_half: forall id ofs, *)
      (*   Val.inject j (high_half ge1 id ofs) (high_half ge2 id ofs) *)
    }.

  Variant comp_of_state (ge: genv): state -> compartment -> Prop :=
    | comp_of_state_internal: forall st rs m cp comp,
        Genv.find_comp_in_genv ge (rs PC) = comp ->
        comp <> bottom ->
        comp_of_state ge (State st rs m cp) comp
    (* | comp_of_state_external: forall st rs m cp comp, *)
    (*     Genv.find_comp_in_genv ge (rs PC) = bottom -> *)
    (*     comp = Genv.find_comp_in_genv ge (rs X1) -> *)
    (*     cp = comp -> *)
    (*     comp_of_state ge (State st rs m cp) comp *)
    | comp_of_returnstate_internal: forall st rs m rec_cp,
        rec_cp <> bottom ->
        comp_of_state ge (ReturnState st rs m rec_cp) rec_cp
    (* | comp_of_returnstate_external: forall st rs m comp, *)
    (*     comp = Genv.find_comp_in_genv ge (rs PC) -> *)
    (*     comp_of_state ge (ReturnState st rs m bottom) comp *)
  .

  Lemma comp_of_state_unique: forall ge st cp cp',
      comp_of_state ge st cp ->
      comp_of_state ge st cp' ->
      cp = cp'.
  Proof.
    intros ge st cp cp' H H'.
    inv H; inv H'; now auto.
  Qed.

  Inductive strong_equivalence (ge ge': genv) (j: meminj) (δ: side): state -> state -> Prop :=
  | strong_equivalence_State: forall st st' rs rs' m m' cp cp',
    (* Genv.find_comp_in_genv ge (rs PC) = cp -> *)
    forall (COMP1: comp_of_state ge (State st rs m cp') cp)
      (COMP2: comp_of_state ge' (State st' rs' m' cp') cp)
      (SIDE: s cp = δ),
    forall (NOTOP: cp <> top)
      (NOBOTTOM: cp <> bottom),
    forall (NOTOP': cp' <> top)
      (NOBOTTOM': cp' <> bottom),
    forall (ST_RS: callee_comp cp_main st' = cp),
      regset_rel j rs rs' ->
      mem_rel ge ge' j δ m m' ->
      strong_equivalence ge ge' j δ (State st rs m cp') (State st' rs' m' cp')
  | strong_equivalence_ReturnState: forall st st' (rs rs': regset) m m' cp rec_cp,
    (* careful, the current comp in a returnstate is given by [rec_cp] *)
    forall (COMP1: comp_of_state ge (ReturnState st rs m rec_cp) cp)
      (COMP2: comp_of_state ge' (ReturnState st' rs' m' rec_cp) cp)
      (SIDE: s cp = δ),
    forall (ST_RS: callee_comp cp_main st' = cp),
      regset_rel j rs rs' ->
      mem_rel ge ge' j δ m m' ->
      strong_equivalence ge ge' j δ (ReturnState st rs m rec_cp) (ReturnState st' rs' m' rec_cp)
  .


  Inductive weak_equivalence (ge ge': genv) (j: meminj) (δ: side): state -> state -> Prop :=
  | weak_equivalence_State: forall st st' rs rs' m m' cp cp' cp'',
    forall (COMP1: comp_of_state ge (State st rs m cp') cp)
      (COMP2: comp_of_state ge' (State st' rs' m' cp'') cp)
      (SIDE: s cp = opposite δ),
    forall (NOTOP: cp <> top)
      (NOBOTTOM: cp <> bottom),
    forall (NOTOP': cp' <> top)
      (NOBOTTOM': cp' <> bottom),
    forall (NOTOP'': cp'' <> top)
      (NOBOTTOM'': cp'' <> bottom),
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (State st rs m cp') (State st' rs' m' cp'')
  | weak_equivalence_ReturnState: forall st st' rs rs' m m' cp rec_cp rec_cp',
    (* careful, the current comp in a returnstate is given by [callee_comp] *)
    forall (COMP1: comp_of_state ge (ReturnState st rs m rec_cp) cp)
      (COMP2: comp_of_state ge' (ReturnState st' rs' m' rec_cp') cp)
      (SIDE: s cp = opposite δ),
    forall (NOTOP: cp <> top)
      (NOBOTTOM: cp <> bottom),
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (ReturnState st rs m rec_cp) (ReturnState st' rs' m' rec_cp')
  | weak_equivalence_State_ReturnState: forall st st' rs rs' m m' cp cp' rec_cp',
    forall (COMP1: comp_of_state ge (State st rs m cp') cp)
      (COMP2: comp_of_state ge' (ReturnState st' rs' m' rec_cp') cp)
      (SIDE: s cp = opposite δ),
    forall (NOTOP: cp <> top)
      (NOBOTTOM: cp <> bottom),
    forall (NOTOP': cp' <> top)
      (NOBOTTOM': cp' <> bottom),
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (State st rs m cp') (ReturnState st' rs' m' rec_cp')
  | weak_equivalence_ReturnState_State: forall st st' rs rs' m m' cp cp' rec_cp,
    forall (COMP1: comp_of_state ge (ReturnState st rs m rec_cp) cp)
      (COMP2: comp_of_state ge' (State st' rs' m' cp') cp)
      (SIDE: s cp = opposite δ),
    forall (NOTOP: cp <> top)
      (NOBOTTOM: cp <> bottom),
    forall (NOTOP': cp' <> top)
      (NOBOTTOM': cp' <> bottom),
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (ReturnState st rs m rec_cp) (State st' rs' m' cp')
  .

  Lemma weak_equivalence_inv1 (ge ge': genv) (j: meminj) (δ: side) (s1 s3: state) :
    weak_equivalence ge ge' j δ s1 s3 ->
    exists st1 rs1 m1,
      match s3 with
      | State st3 rs3 m3 _
      | ReturnState st3 rs3 m3 _ => mem_rel ge ge' j δ m1 m3
      end /\
        s1 = match s1 with
             | State _ _ _ cp => State st1 rs1 m1 cp
             | ReturnState _ _ _ cp => ReturnState st1 rs1 m1 cp
             end.
  Proof.
    intros weak_s1_s3.
    inv weak_s1_s3; eauto.
  Qed.

  Lemma weak_equivalence_inv (ge ge': genv) (j: meminj) (δ: side) (s1 s3: state) :
    weak_equivalence ge ge' j δ s1 s3 ->
    exists st1 st3 rs1 rs3 m1 m3,
      mem_rel ge ge' j δ m1 m3 /\
        s1 = match s1 with
             | State _ _ _ cp => State st1 rs1 m1 cp
             | ReturnState _ _ _ cp => ReturnState st1 rs1 m1 cp
             end /\
        s3 = match s3 with
             | State _ _ _ cp => State st3 rs3 m3 cp
             | ReturnState _ _ _ cp => ReturnState st3 rs3 m3 cp
             end.
  Proof.
    intros weak_s1_s3.
    inv weak_s1_s3; do 6 eexists; eauto.
  Qed.



End Invariants.


Arguments opposite /.

Lemma store_preserves_weak:
  forall s ge1 ge2 ge3 cp_main j j__oppδ ch cp b ofs v m1 m1' m2 m3 st1 st2 st3
    (not_bottom: cp <> bottom)
    (not_top: cp <> top),
    Mem.store ch m1 b ofs v cp = Some m1' ->
    stack_rel s cp_main ge1 ge2 ge3 (opposite (s cp)) j j__oppδ m1 m2 m3 st1 st2 st3 ->
    mem_rel s ge1 ge3 j (opposite (s cp)) m1 m3 ->


    mem_rel s ge1 ge3 j (opposite (s cp)) m1' m3 /\
      stack_rel s cp_main ge1 ge2 ge3 (opposite (s cp)) j j__oppδ m1' m2 m3 st1 st2 st3.
Proof.
  intros s ge1 ge2 ge3 cp_main j j__oppδ ch cp b ofs v m1 m1' m2 m3 st1 st2 st3
    not_bottom not_top exec st_rel m1_m3.
  assert (j b = None).
  { pose proof (same_dom _ _ _ _ _ m1 m3 m1_m3 b) as dom.
    exploit Mem.store_valid_access_3; eauto. intros (_ & access_block & _).
    simpl in access_block, dom, m1_m3.
    exploit Mem.store_valid_access_3; eauto.
    assert (sz: ofs <= ofs < ofs + size_chunk ch) by now (destruct ch; simpl; lia).
    intros [G [_ _]]. specialize (G ofs sz).
    eapply Mem.perm_max in G. eapply Mem.perm_implies in G; eauto using perm_any_N.
    exploit perm_compartment1; eauto. intros [id x]. rewrite x in *.
    inv access_block; try contradiction.
    destruct (j b) eqn:C; auto.
    assert (H: Some p <> None) by congruence.
    apply dom in H.
    destruct H as [[H ?] | (fd & H)].
    destruct (s (Comp id)); try discriminate.
    Local Transparent Mem.store.
    unfold Mem.store in exec.
    destruct Mem.valid_access_dec as [[e _] | n]; try congruence.
    eapply Mem.range_perm_max in e.
    specialize (e ofs sz). clear G.
    exploit find_def_perm1; eauto.
    eapply Mem.perm_implies; eauto; try constructor.
    now auto. }
  split.
  constructor.
  - intros b'; apply same_dom in m1_m3; specialize (m1_m3 b').
    simpl in *. erewrite Mem.store_block_compartment; eauto.
    split. intros A; apply m1_m3 in A as [[] |]; eauto.
    left; split; eauto.
    eapply Mem.store_valid_block_1; eauto.
    intros [[] |]; apply m1_m3; eauto.
    left; split; eauto.
    eapply Mem.store_valid_block_2; eauto.
  - eapply Mem.store_unmapped_inject; eauto using partial_mem_inject.
  - eapply delta_zero; eauto.
  - intros. erewrite <- Mem.store_preserves_comp; eauto.
    eapply perm_compartment1; eauto.
    eapply Mem.perm_store_2; eauto.
  - eapply perm_compartment2; eauto.
  - erewrite Mem.nextblock_store; eauto using ple_nextblock1.
  - eapply ple_nextblock2; eauto.
  - intros. eapply Mem.store_valid_block_1; eauto using find_def_valid1.
  - intros. eapply find_def_valid2; eauto.
  - intros. eapply find_def_perm1 with (b := b0) in m1_m3; eauto.
    intros n. apply m1_m3. eapply Mem.perm_store_2; eauto.
  - intros. eapply find_def_perm2 with (b := b0) in m1_m3; eauto.
  - intros. erewrite <- Mem.store_preserves_comp; eauto using find_var_comp1.
  - intros; eapply meminj_injective; eauto.
  - { rename H into j_b.
      induction st_rel.
      constructor; eauto.
      constructor; eauto.
      inv H; eauto.
      - econstructor; eauto.
        + unfold same_content_stack in *.
          intros ? ? ? R G.
          specialize (STACK_CONTENT1 _ _ _ R G) as [? STACK_CONTENT1].
          Opaque Stacklayout.fe_ofs_arg Z.mul. simpl in *.
          split; destruct sp1; simpl in *; try congruence.
          { intros. inv H1. intros ? ?. eapply Mem.perm_store_1; eauto. eapply H; eauto. }
          intros ? G''.
          erewrite Mem.load_store_other in G''; eauto.
          left.
          { intros ?; subst. eapply PERM1. eapply Mem.perm_max.
            exploit Mem.store_valid_access_3; eauto.
            intros [VA [_ _]]. eapply VA with (ofs := ofs).
            destruct ch; simpl; lia. }
        + unfold at_most_readable in *.
          destruct sp1; try auto.
          split. eapply Mem.store_valid_block_1; eauto; eapply PERM1.
          intros o N. eapply PERM1. now eapply Mem.perm_store_2; eauto.
        + unfold nonempty in *.
          destruct sp1; try contradiction.
          eapply Mem.perm_store_1; eauto.
        + unfold empty_perm in *.
          split. eapply Mem.store_valid_block_1; eauto; eapply EMPTY1.
          intros ? ?. eapply EMPTY1. eapply Mem.perm_store_2; eauto.
      - eapply stackframe_related_opp_δ; eauto.
        + unfold same_content_stack in *.
          intros ? ? ? R G.
          specialize (STACK_CONTENT1 _ _ _ R G) as [? STACK_CONTENT1].
          Opaque Stacklayout.fe_ofs_arg Z.mul. simpl in *.
          split; destruct sp1; simpl in *; try congruence.
          { intros. inv H1. intros ? ?. eapply Mem.perm_store_1; eauto. eapply H; eauto. }
          intros ? G''.
          erewrite Mem.load_store_other in G''; eauto.
          left.
          { intros ?; subst. eapply PERM1. eapply Mem.perm_max.
            exploit Mem.store_valid_access_3; eauto.
            intros [VA [_ _]]. eapply VA with (ofs := ofs).
            destruct ch; simpl; lia. }
        + unfold at_most_readable in *.
          destruct sp1; try auto.
          split. eapply Mem.store_valid_block_1; eauto; eapply PERM1.
          intros o N. eapply PERM1. now eapply Mem.perm_store_2; eauto.
        + unfold nonempty in *.
          destruct sp1; try contradiction.
          eapply Mem.perm_store_1; eauto.
        + unfold empty_perm in *.
          split. eapply Mem.store_valid_block_1; eauto; eapply EMPTY1.
          intros ? ?. eapply EMPTY1. eapply Mem.perm_store_2; eauto.
    }
Qed.

Lemma exec_store_preserves_weak:
  forall s cp_main ge1 ge2 ge3 j j__oppδ cp ch m1 m1' m2 m3 rs1 rs1' rs ra ofs st1 st2 st3
    (not_bottom: cp <> bottom)
    (not_top: cp <> top),

    stack_rel s cp_main ge1 ge2 ge3 (opposite (s cp)) j j__oppδ m1 m2 m3 st1 st2 st3 ->
    exec_store ge1 ch rs1 m1 rs ra ofs cp = Next rs1' m1' ->
    mem_rel s ge1 ge3 j (opposite (s cp)) m1 m3 ->

    mem_rel s ge1 ge3 j (opposite (s cp)) m1' m3 /\
      stack_rel s cp_main ge1 ge2 ge3 (opposite (s cp)) j j__oppδ m1' m2 m3 st1 st2 st3.
Proof.
  intros s cp_main ge1 ge2 ge3 j j' cp ch m1 m1' m2 m3 rs1 rs1' rs ra ofs st1 st2 st3 ? ? st_rel exec m1_m3.
  unfold exec_store in exec.
  destruct Mem.storev eqn:m1_m1'; try congruence; inv exec.
  destruct (rs1 ra); simpl in *; try congruence.
  eapply store_preserves_weak; eauto.
Qed.

Lemma alloc_preserves_weak:
  forall s δ W1 (_: list_norepet (prog_defs_names W1)) ge2 W3 cp_main j j__oppδ cp lo hi m1 m2 m1' b1 m3 st1 st2 st3
    (not_bottom: cp <> bottom)
    (not_top: cp <> top),
    Mem.alloc m1 cp lo hi = (m1', b1) ->
    meminj_preserves_globals s δ W1 W3 j ->
    mem_rel s (Genv.globalenv W1) (Genv.globalenv W3) j (opposite (s cp)) m1 m3 ->
    stack_rel s cp_main (Genv.globalenv W1) ge2 (Genv.globalenv W3) (opposite (s cp)) j j__oppδ m1 m2 m3 st1 st2 st3 ->
    exists j',
      meminj_preserves_globals s δ W1 W3 j' /\
        mem_rel s (Genv.globalenv W1) (Genv.globalenv W3) j' (opposite (s cp)) m1' m3 /\ inject_incr j j' /\
        stack_rel s cp_main (Genv.globalenv W1) ge2 (Genv.globalenv W3) (opposite (s cp)) j' j__oppδ m1' m2 m3 st1 st2 st3.
Proof.
  intros s δ W1 norepet1 W2 W3 cp_main j j__oppδ cp lo hi m1 m2 m1' b1 m3 st1 st2 st3 ? ? exec inj_pres m1_m3 st_rel.
  exploit Mem.alloc_left_unmapped_inject; eauto using partial_mem_inject.
  intros (j' & m1'_m3 & incr & j'_b1 & same_inj).
  exists j'. split; [| split; [| split]]; auto.
  { assert (G: forall s δ p1 p2 j j',
               meminj_preserves_globals s δ p1 p2 j ->
               (forall (id: ident) (b: block), Genv.find_symbol (Genv.globalenv p1) id = Some b ->
                                          j' b = j b) ->
               (forall (b: block) gd, Genv.find_def (Genv.globalenv p1) b = Some gd ->
                                 j' b = j b) ->
               (forall (b b': block) delta gd, Genv.find_def (Genv.globalenv p2) b' = Some gd ->
                                          j' b = Some (b', delta) ->
                                          j b = Some (b', delta)) ->
               inject_incr j j' ->
               meminj_preserves_globals s δ p1 p2 j').
    { clear.
      intros s δ p1 p2 j j' [A B C D E] rewr1 rewr2 rewr3 incr.
      constructor.
      - intros. erewrite rewr1 in H; eauto.
      - intros. exploit B; eauto. intros (? & ? & ?).
        exploit incr; eauto.
      - intros. exploit C; eauto. intros (? & ? & ?).
        exploit incr; eauto.
      - intros. erewrite rewr2 in H; eauto.
      - intros. eapply rewr3 in H; eauto. }
    eapply G; eauto.
    - clear G.
      intros. eapply same_inj.
      exploit Genv.find_symbol_find_def_inversion; eauto. intros [gd ?].
      eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
      eapply Mem.alloc_result in exec; subst. intros N; subst b; exploit Plt_strict; eauto.
    - clear G.
      intros. eapply same_inj.
      eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
      eapply Mem.alloc_result in exec; subst. intros N; subst b; exploit Plt_strict; eauto.
    - clear G.
      intros. rewrite <- same_inj; eauto.
      eapply find_def_valid2 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
      eapply Mem.alloc_result in exec; subst. intros N; subst b.
      assert (b' = Mem.nextblock m3) by congruence. subst b'.
      now exploit Plt_strict; eauto. }
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
    rewrite m1_m3.
    destruct (s cp); simpl in *; intuition congruence.
    split. intros A; eapply m1_m3 in A as [[] |]; eauto.
    left; split; eauto. eapply Mem.valid_block_alloc; eauto.
    intros [[] |]; eapply m1_m3; eauto.
    left; split; eauto. eapply Mem.valid_block_alloc_inv in H0 as []; eauto.
    congruence.
  - auto.
  - intros b b' delta.
    destruct (eq_block b b1); try congruence.
    rewrite same_inj; eauto.
    eapply delta_zero; eauto.
  - intros.
    pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ exec b ofs Max Nonempty H).
    eapply Mem.alloc_block_compartment with (b' := b) in exec.
    destruct (eq_block b b1); try subst b.
    + destruct cp; try contradiction. eauto.
    + rewrite exec. eapply perm_compartment1; eauto.
  - eapply perm_compartment2; eauto.
  - apply ple_nextblock1 in m1_m3.
    erewrite Mem.nextblock_alloc; eauto using ple_nextblock1.
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
  - intros. erewrite Mem.alloc_block_compartment; eauto.
    rewrite pred_dec_false; eauto using find_var_comp1.
    intros ?; subst; eapply Mem.fresh_block_alloc; eauto using find_def_valid1.
  - intros.
    assert (b0 <> b1) by congruence.
    assert (b4 <> b1) by congruence.
    rewrite same_inj in H0, H1; eauto.
    eapply meminj_injective with (b0 := b0) (b4 := b4) in m1_m3; eauto.
  - { eapply inject_incr_stack_rel1; eauto.
      induction st_rel.
      - constructor; eauto.
      - constructor; eauto.
        inv H.
        + econstructor; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? R G.
            specialize (STACK_CONTENT1 _ _ _ R G) as [? STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A.
              intros ? ?. eapply Mem.perm_alloc_1; eauto. eapply H; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto. eapply PERM1.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto; eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc; eauto.
            inv H4; eapply Mem.valid_block_inject_1; eauto using partial_mem_inject.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto; eapply EMPTY1.
            intros ? ?. eapply EMPTY1.
            eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc; eauto. eapply EMPTY1.
        + simpl in *.
          eapply stackframe_related_opp_δ; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? R G.
            specialize (STACK_CONTENT1 _ _ _ R G) as [? STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A.
              intros ? ?. eapply Mem.perm_alloc_1; eauto. eapply H; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto. eapply PERM1.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto; eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc; eauto.
            eapply PERM1.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto; eapply EMPTY1.
            intros ? ?. eapply EMPTY1.
            eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc; eauto. eapply EMPTY1.
    }
Qed.

Lemma extcall_preserves_mem_rel_same_side:
  forall s ge1 ge2 ge3 cp_main j j' j__oppδ m1 m1' m2 m3 m3' ef vres vres' t vargs vargs' δ cp st1 st2 st3
    (not_bottom: cp <> bottom)
    (not_top: cp <> top),
    stack_rel s cp_main ge1 ge2 ge3 (s cp) j j__oppδ m1 m2 m3 st1 st2 st3 ->
    Mem.unchanged_on (loc_unmapped j) m1 m1' ->
    inject_incr j j' ->
    inject_separated j j' m1 m3 ->
    (forall b : block,
        (Mem.valid_block m1 b -> False) ->
        Mem.valid_block m1' b ->
        exists b' : block,
          j' b = Some (b', 0)) ->
    forall (INJ: (forall (b1 b2 b1' b2' : block) (delta1 delta2 : Z),
                b1 <> b2 ->
                j b1 = None ->
                j b2 = None ->
                j' b1 = Some (b1', delta1) -> j' b2 = Some (b2', delta2) -> b1' <> b2')),
      s cp = δ ->
      mem_rel s ge1 ge3 j δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      Mem.inject j' m1' m3' ->
      external_call ef ge1 cp vargs m1 t vres m1' ->
      external_call ef ge3 cp vargs' m3 t vres' m3' ->
      mem_rel s ge1 ge3 j' δ m1' m3' /\
        stack_rel s cp_main ge1 ge2 ge3 (s cp) j' j__oppδ m1' m2 m3' st1 st2 st3.
Proof.
  intros s ge1 ge2 ge3 cp_main j j' j__oppδ m1 m1' m2 m3 m3' ef vres vres' t vargs vargs' δ cp st1 st2 st3
    ? ? st_rel unchanged inj_incr inj_sep comp_new ? comp_ef m1_m3 m2_m3 inj_m1'_m3' extcall1 extcall3.
  split.
  clear m2_m3.
  constructor.
  - (* same domain *)
    intros b. apply same_dom in m1_m3 as m1_m3'. specialize (m1_m3' b).
    destruct (j b) as [[b0 z] |] eqn:j_b.
    + apply inj_incr in j_b as j'_b.
      split; try congruence.
      intros _. destruct m1_m3' as [side_b _].
      exploit side_b; try congruence.
      intros [[] | ?]; try now auto.
      assert (Mem.valid_block m1 b).
      { destruct (Classical_Prop.classic (Mem.valid_block m1 b)); auto. }
      pose proof (ec_preserves_comp (external_call_spec ef cp)) as G.
      simpl. erewrite <- G; eauto. left; split; auto.
      eapply external_call_valid_block; eauto.
    + destruct m1_m3' as [C1 C2].
      simpl in C1, C2; simpl.
      split.
      * destruct (j' b) as [[] |] eqn:j'_b; try congruence; intros _.
        exploit inj_sep; eauto.
        intros [H _].
        assert (Mem.valid_block m1' b).
        { pose proof (Mem.mi_freeblocks _ _ _ inj_m1'_m3' b) as G.
          apply Classical_Prop.NNPP.
          intros ?. exploit G; eauto. congruence. }
        clear extcall3. exploit (ec_new_blocks_comp (external_call_spec ef cp)); eauto.
        intros ->. destruct cp; try contradiction.
        eauto.
      * clear C1.
        intros [H | H].
        -- assert (not (s (Mem.block_compartment m1 b) = δ /\
                          Mem.valid_block m1 b)). intros ?. exploit C2; eauto.
           intros G. eapply Classical_Prop.not_and_or in H0.
           destruct H.
           destruct (Classical_Prop.classic (Mem.valid_block m1 b)); auto.
           ++ destruct H0; try contradiction.
              exploit Mem.unchanged_on_own; eauto. intros R; rewrite R in *; congruence.
           ++ exploit comp_new; eauto.
              intros [? ?]. congruence.
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
      exploit comp_new; eauto. intros [? ?]; congruence.
  - intros b ofs ?.
    destruct (Classical_Prop.classic (Mem.valid_block m1 b)).
    + pose proof (ec_preserves_comp (external_call_spec ef cp)) as G.
      erewrite <- G; eauto.
      eapply external_call_max_perm in H; eauto.
      exploit perm_compartment1; eauto.
    + exploit Mem.perm_valid_block; eauto. intros ?. clear extcall3.
      exploit (ec_new_blocks_comp (external_call_spec ef cp)); eauto.
      intros ->. destruct cp; try contradiction.
      eauto.
  - intros b ofs ?. clear extcall1.
    destruct (Classical_Prop.classic (Mem.valid_block m3 b)).
    + pose proof (ec_preserves_comp (external_call_spec ef cp)) as G.
      erewrite <- G; eauto.
      eapply external_call_max_perm in H; eauto.
      exploit perm_compartment2; eauto.
    + exploit Mem.perm_valid_block; eauto. intros ?.
      exploit (ec_new_blocks_comp (external_call_spec ef cp)); eauto.
      intros ->. destruct cp; try contradiction.
      eauto.
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
  - intros. erewrite <- ec_preserves_comp; eauto using external_call_spec, find_var_comp1, find_def_valid1.
  - intros.
    destruct (j b0) as [[] |] eqn:j_b0; destruct (j b4) as [[] |] eqn:j_b4.
    + erewrite inj_incr in H0; eauto.
      erewrite inj_incr in H1; eauto. inv H0; inv H1.
      eapply meminj_injective; eauto.
    + erewrite inj_incr in H0; eauto. inv H0.
      exploit inj_sep; eauto. intros [].
      assert (Mem.valid_block m3 b1'). eapply Mem.valid_block_inject_2; eauto using partial_mem_inject.
      intros ?; subst; congruence.
    + erewrite inj_incr in H1; eauto. inv H1.
      exploit inj_sep; eauto. intros [].
      assert (Mem.valid_block m3 b2'). eapply Mem.valid_block_inject_2; eauto using partial_mem_inject.
      intros ?; subst; congruence.
    + eauto.
  (* same high half *)
  - eapply inject_incr_stack_rel1; eauto.
    induction st_rel;
      econstructor; eauto.
    inv H.
    + econstructor; eauto.
      * unfold same_content_stack in *.
        intros ? ? ? R G.
        specialize (STACK_CONTENT1 _ _ _ R G) as [X STACK_CONTENT1].
        (* intros ? ? G ? G'. *)
        (* specialize (STACK_CONTENT1 _ _ G _ G') as [X STACK_CONTENT1]. *)
        split; destruct sp1; simpl in *; try congruence.
        { intros ? ? A; inv A. intros ??.
          specialize (X b0 _ eq_refl).
          eapply Mem.range_perm_loadbytes with (cp := top) in X.
          destruct X as [? ?]. eapply ec_readonly' in H1; eauto.
          eapply Mem.loadbytes_range_perm in H1. eapply H1; eauto.
          eapply external_call_spec.
          eapply PERM1. intros. eapply PERM1. simpl; eauto with comps. }
        intros ? G''.
        eapply Mem.load_loadbytes in G'' as G'''.
        destruct G''' as [bytes [R1 R2]].
        eapply ec_readonly in R1; eauto using external_call_spec.
        eapply Mem.loadbytes_load in R1.
        specialize (STACK_CONTENT1 (* _ _ G _ G' *) _ R1) as [R' R'']; split; subst v; eauto.
        destruct sp3; simpl in *; try congruence.
        eapply Mem.load_loadbytes in R'' as R'''.
        destruct R''' as [bytes' [R1' R2']].
        eapply ec_readonly' in R1'; eauto using external_call_spec.
        rewrite R2'. eapply Mem.loadbytes_load; eauto.
        eapply Mem.load_valid_access; eauto.
        eapply PERM3. intros; eapply PERM3.
        eapply Mem.load_valid_access; eauto. eapply PERM1.
        intros; eapply PERM1.
      * unfold same_content_stack in *.
        intros ? ? ? E G.
        specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
        (* intros ? ? G ? G'. *)
        (* specialize (STACK_CONTENT2 _ _ G _ G') as [X STACK_CONTENT2]. *)
        split; destruct sp2; simpl in *; try congruence.
        { eapply X. }
        intros ? G''.
        specialize (STACK_CONTENT2 (* _ _ G _ G' *) _ G'') as [R R']; split; eauto.
        destruct sp3; simpl in *; try congruence.
        eapply Mem.load_loadbytes in R' as R''.
        destruct R'' as [bytes' [R1' R2']].
        eapply ec_readonly' in R1'; eauto using external_call_spec.
        rewrite R2'. eapply Mem.loadbytes_load; eauto.
        eapply Mem.load_valid_access; eauto.
        eapply PERM3. intros; eapply PERM3.
      * unfold at_most_readable in *.
        destruct sp1; try auto.
        split. eapply external_call_valid_block; eauto using external_call_spec.
        eapply PERM1.
        intros ofs N. eapply PERM1. eapply ec_max_perm; eauto using external_call_spec.
        inv H4. eapply Mem.valid_block_inject_1; eauto using partial_mem_inject.
      * unfold at_most_readable in *.
        destruct sp3; try auto.
        split. eapply external_call_valid_block; eauto using external_call_spec.
        eapply PERM3.
        intros ofs N. eapply PERM3. eapply ec_max_perm; eauto using external_call_spec.
        inv H4; try contradiction; eapply Mem.valid_block_inject_2; eauto using partial_mem_inject.
      * unfold nonempty in *.
        destruct sp1; try contradiction.
        rewrite <- ec_public_not_freeable; eauto using external_call_spec.
        eapply Mem.perm_valid_block. eauto.
        destruct PERM1. intros ?. eapply H1. eapply Mem.perm_implies; eauto. constructor.
      * unfold nonempty in *.
        destruct sp3; try contradiction.
        rewrite <- ec_public_not_freeable; eauto using external_call_spec.
        eapply Mem.perm_valid_block. eauto.
        destruct PERM3. intros ?. eapply H1. eapply Mem.perm_implies; eauto. constructor.
      * unfold empty_perm in *. split.
        eapply external_call_valid_block; eauto using external_call_spec.
        eapply EMPTY1.
        intros ofs N. eapply EMPTY1. eapply ec_max_perm; eauto using external_call_spec.
        eapply EMPTY1.
      * unfold empty_perm in *. split.
        eapply external_call_valid_block; eauto using external_call_spec.
        eapply EMPTY3.
        intros ofs N. eapply EMPTY3. eapply ec_max_perm; eauto using external_call_spec.
        eapply EMPTY3.
    + eapply stackframe_related_opp_δ; eauto.
      * unfold same_content_stack in *.
        intros ? ? ? E G.
        specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
        split; destruct sp1; simpl in *; try congruence.
        { intros ? ? A; inv A. intros ??.
          specialize (X b0 _ eq_refl).
          eapply Mem.range_perm_loadbytes with (cp := top) in X.
          destruct X as [? ?]. eapply ec_readonly' in H1; eauto.
          eapply Mem.loadbytes_range_perm in H1. eapply H1; eauto.
          eapply external_call_spec.
          eapply PERM1. intros. eapply PERM1. simpl; eauto with comps. }
        intros ? G''.
        eapply Mem.load_loadbytes in G'' as G'''.
        destruct G''' as [bytes [R1 R2]].
        eapply ec_readonly in R1; eauto using external_call_spec.
        eapply Mem.loadbytes_load in R1.
        specialize (STACK_CONTENT1 (* _ _ G _ G' *) _ R1) as [R R']; split; subst v; eauto.
        destruct sp3; simpl in *; try congruence.
        eapply Mem.load_loadbytes in R' as R''.
        destruct R'' as [bytes' [R1' R2']].
        eapply ec_readonly' in R1'; eauto using external_call_spec.
        rewrite R2'. eapply Mem.loadbytes_load; eauto.
        eapply Mem.load_valid_access; eauto.
        eapply PERM3. intros; eapply PERM3.
        eapply Mem.load_valid_access; eauto. eapply PERM1.
        intros; eapply PERM1.
      * unfold same_content_stack in *.
        intros ? ? ? E G.
        specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
        split; destruct sp2; simpl in *; try congruence.
        { eapply X. }
        intros ? G''.
        specialize (STACK_CONTENT2 (* _ _ G _ G' *) _ G'') as [R R']; split; eauto.
        destruct sp3; simpl in *; try congruence.
        eapply Mem.load_loadbytes in R' as R''.
        destruct R'' as [bytes' [R1' R2']].
        eapply ec_readonly' in R1'; eauto using external_call_spec.
        rewrite R2'. eapply Mem.loadbytes_load; eauto.
        eapply Mem.load_valid_access; eauto.
        eapply PERM3. intros; eapply PERM3.
      * unfold at_most_readable in *.
        destruct sp1; try auto.
        split. eapply external_call_valid_block; eauto using external_call_spec.
        eapply PERM1.
        intros ofs N. eapply PERM1. eapply ec_max_perm; eauto using external_call_spec.
        eapply PERM1.
      * unfold at_most_readable in *.
        destruct sp3; try auto.
        split. eapply external_call_valid_block; eauto using external_call_spec.
        eapply PERM3.
        intros ofs N. eapply PERM3. eapply ec_max_perm; eauto using external_call_spec.
        inv H4; try contradiction; eapply Mem.valid_block_inject_2; eauto using partial_mem_inject.
      * unfold nonempty in *.
        destruct sp1; try contradiction.
        rewrite <- ec_public_not_freeable; eauto using external_call_spec.
        eapply Mem.perm_valid_block. eauto.
        destruct PERM1. intros ?. eapply H1. eapply Mem.perm_implies; eauto. constructor.
      * unfold nonempty in *.
        destruct sp3; try contradiction.
        rewrite <- ec_public_not_freeable; eauto using external_call_spec.
        eapply Mem.perm_valid_block. eauto.
        destruct PERM3. intros ?. eapply H1. eapply Mem.perm_implies; eauto. constructor.
      * unfold empty_perm in *. split.
        eapply external_call_valid_block; eauto using external_call_spec.
        eapply EMPTY1.
        intros ofs N. eapply EMPTY1. eapply ec_max_perm; eauto using external_call_spec.
        eapply EMPTY1.
      * unfold empty_perm in *. split.
        eapply external_call_valid_block; eauto using external_call_spec.
        eapply EMPTY3.
        intros ofs N. eapply EMPTY3. eapply ec_max_perm; eauto using external_call_spec.
        eapply EMPTY3.
Qed.

Lemma extcall_preserves_mem_rel_opp_side1: forall s cp cp_main ge1 ge2 ge3 j j__oppδ δ m1 m1' m2 m3 ef vargs t vres st1 st2 st3
                                             (not_bottom: cp <> bottom)
                                             (not_top: cp <> top),
    s cp = opposite δ ->
    mem_rel s ge1 ge3 j δ m1 m3 ->
    stack_rel s cp_main ge1 ge2 ge3 δ j j__oppδ m1 m2 m3 st1 st2 st3 ->
    external_call ef ge1 cp vargs m1 t vres m1' ->

    mem_rel s ge1 ge3 j δ m1' m3 /\
      stack_rel s cp_main ge1 ge2 ge3 δ j j__oppδ m1' m2 m3 st1 st2 st3.
Proof.
  intros s cp cp_main ge1 ge2 ge3 j j__oppδ δ m1 m1' m2 m3 ef vargs t vres st1 st2 st3 ? ? side_ef m1_m3 st_rel extcall.
  split.
  constructor.
  - (* same domain *)
    intros b. apply same_dom in m1_m3 as m1_m3'. specialize (m1_m3' b).
    destruct (j b) as [[b0 z] |] eqn:j_b.
    + split; try congruence.
      intros _. destruct m1_m3' as [side_b _].
      exploit side_b; try congruence.
      intros [[] | ?]; try now auto.
      pose proof (ec_preserves_comp (external_call_spec ef cp)) as G.
      simpl. erewrite <- G; eauto. left; split; eauto.
      eapply external_call_valid_block; eauto.
    + destruct m1_m3' as [C1 C2].
      simpl in C1, C2; simpl.
      split.
      * congruence.
      * clear C1.
        intros [H | H].
        -- assert (not (s (Mem.block_compartment m1 b) = δ /\
                          Mem.valid_block m1 b)). intros ?. exploit C2; eauto.
           intros G. eapply Classical_Prop.not_and_or in H0.
           destruct H.
           destruct (Classical_Prop.classic (Mem.valid_block m1 b)); auto.
           ++ destruct H0; try contradiction.
              exploit ec_outside_comp; eauto using external_call_spec.
              intros ?.
              exploit Mem.unchanged_on_own; eauto. intros R; rewrite R in *; congruence.
           ++ exploit (ec_new_blocks_comp (external_call_spec ef cp)); eauto.
              intros R; rewrite R in H. destruct (s cp), δ; simpl in *; congruence.
        -- now specialize (C2 (or_intror H)).
  - (* injection *)
    exploit partial_mem_inject; eauto. intros m1_inject_m3.
    assert (UNCH1: Mem.unchanged_on (fun b ofs => not (Mem.can_access_block m1 b cp)) m1 m1').
    { eapply ec_outside_comp; eauto using external_call_spec. }
    assert (UNCH: Mem.unchanged_on
                    (fun b ofs => ((s, m1) |= b ∈ δ /\ Mem.valid_block m1 b) \/ (exists fd : fundef, Genv.find_def ge1 b = Some (Gfun fd))) m1 m1').
    { constructor.
      - (* unchanged_on_nextblock *)
        eapply Mem.unchanged_on_nextblock; eauto.
      - (* unchanged_on_perm *)
        intros. destruct H.
        + pose proof (Mem.unchanged_on_perm _ _ _ UNCH1).
          split.
          * intros ?.
            eapply H1; eauto.
            eapply Mem.perm_max in H2. eapply Mem.perm_implies with (p2 := Nonempty) in H2.
            exploit perm_compartment1; eauto. intros [? G].
            simpl in *; rewrite G in *. intros n. inv n; eauto. destruct H.
            now destruct s, δ.
            destruct p; constructor.
          * intros G.
            eapply Mem.perm_max in G as G'. eapply Mem.perm_implies with (p2 := Nonempty) in G'.
            eapply external_call_max_perm in G'; eauto.
            eapply H1; eauto.
            exploit perm_compartment1; eauto. intros [? G''].
            simpl in *; rewrite G'' in *. intros n. inv n; eauto. now destruct s, δ.
            destruct p; constructor.
        +           assert (Mem.perm m1 b ofs k p -> p = Nonempty).
                    { destruct H as [? H].
                      eapply find_def_perm1 with (ofs := ofs) in H; eauto.
                      intros G. eapply Mem.perm_max in G.
                      destruct p; auto;
                        eapply Mem.perm_implies with (p2 := Readable) in G; try contradiction; try constructor. }
                    assert (Mem.perm m1' b ofs k p -> p = Nonempty).
                    { destruct H as [? H].
                      intros G. eapply Mem.perm_max in G.
                      eapply external_call_max_perm in G; eauto.
                      eapply find_def_perm1 with (ofs := ofs) in H; eauto.
                      destruct p; auto;
                        eapply Mem.perm_implies with (p2 := Readable) in G; try contradiction; try constructor. }
                    destruct H as [? H].
                    split.
                    * intros G. exploit H1; eauto. intros ->.
                      revert G. eapply proj1.
                      eapply ec_public_not_freeable; eauto using external_call_spec.
                      eapply find_def_perm1 with (ofs := ofs) in H; eauto. intros G.
                      eapply Mem.perm_implies with (p2 := Readable) in G; try contradiction.
                      constructor.
                    * intros G. exploit H2; eauto. intros ->.
                      revert G. eapply proj2.
                      eapply ec_public_not_freeable; eauto using external_call_spec.
                      eapply find_def_perm1 with (ofs := ofs) in H; eauto. intros G.
                      eapply Mem.perm_implies with (p2 := Readable) in G; try contradiction.
                      constructor.
      - (* unchanged_on_contents *)
        intros. destruct H.
        + eapply Mem.unchanged_on_contents; eauto. simpl in *.
          eapply Mem.perm_max in H0. eapply Mem.perm_implies with (p2 := Nonempty) in H0.
          exploit perm_compartment1; eauto. intros [? G].
          simpl in *; rewrite G in *. intros n. inv n; eauto. now destruct s, δ.
          constructor.
        + (* contradiction *)
          exfalso.
          destruct H as [? H].
          eapply find_def_perm1 with (ofs := ofs) in H; eauto.
          eapply H. eapply Mem.perm_max; eauto.
      - (* unchanged_on_own *)
        eapply Mem.unchanged_on_own; eauto.
    }
    constructor.
    + apply Mem.mi_inj in m1_inject_m3 as mi_inj.
      apply same_dom in m1_m3 as domain. unfold same_domain in domain.
      constructor.
      * intros.
        eapply Mem.mi_perm; eauto.

        assert (G: j b1 <> None) by congruence.
        eapply domain in G.
        eapply Mem.perm_unchanged_on_2; eauto; eauto.
        eapply Mem.valid_block_inject_1; eauto.
      * intros.
        erewrite <- Mem.mi_access with (m1 := m1) (m2 := m3); eauto with mem.
        simpl in *. erewrite <- ec_preserves_comp; eauto using external_call_spec.
        eapply Mem.valid_block_inject_1; eauto with mem.
        eapply ec_max_perm; eauto using external_call_spec.
        eapply Mem.valid_block_inject_1; eauto with mem.
        eapply Mem.perm_max; eauto.
      * intros. exploit delta_zero; eauto. intros ->. now apply Z.divide_0_r.
      * intros.
        assert (G: j b1 <> None) by congruence.
        eapply domain in G.
        erewrite Mem.unchanged_on_contents; eauto.
        eapply Mem.mi_memval; eauto.
        eapply Mem.perm_unchanged_on_2; eauto; eauto.
        eapply Mem.valid_block_inject_1; eauto.
        eapply Mem.perm_unchanged_on_2; eauto; eauto.
        eapply Mem.valid_block_inject_1; eauto.
    + intros. destruct (j b) as [[]|] eqn:?; auto.
      exfalso.
      exploit (Mem.mi_freeblocks j m1 m3 m1_inject_m3 b); eauto.
      intros ?. exploit Mem.valid_block_unchanged_on; eauto.
      congruence.
    + intros. exploit Mem.mi_mappedblocks; eauto.
    + unfold Mem.meminj_no_overlap. intros.
      eapply ec_max_perm in H2; eauto using external_call_spec.
      eapply ec_max_perm in H3; eauto using external_call_spec.
      exploit Mem.mi_no_overlap; eauto.
      eapply Mem.valid_block_inject_1; eauto.
      eapply Mem.valid_block_inject_1; eauto.
    + intros. destruct H0 as [G | G].
      * eapply ec_max_perm in G; eauto using external_call_spec.
        eapply Mem.mi_representable; eauto.
        eapply Mem.valid_block_inject_1; eauto.
      * eapply ec_max_perm in G; eauto using external_call_spec.
        eapply Mem.mi_representable; eauto.
        eapply Mem.valid_block_inject_1; eauto.
    + intros.
      exploit Mem.mi_perm_inv; eauto. intros [G | G].
      * left.
        assert (G': j b1 <> None) by congruence.
        apply same_dom in m1_m3 as domain. unfold same_domain in domain.
        eapply domain in G'.
        eapply Mem.perm_unchanged_on; eauto.
      * right. intros N.
        eapply ec_max_perm in N; eauto using external_call_spec.
        eapply Mem.valid_block_inject_1; eauto.
  - (* Delta zero *)
    intros b b' delta j'_b.
    apply delta_zero in m1_m3; eauto.
  - intros b ofs ?.
    destruct (Classical_Prop.classic (Mem.valid_block m1 b)).
    + pose proof (ec_preserves_comp (external_call_spec ef cp)) as G.
      erewrite <- G; eauto.
      eapply external_call_max_perm in H; eauto.
      exploit perm_compartment1; eauto.
    + exploit Mem.perm_valid_block; eauto. intros ?.
      exploit (ec_new_blocks_comp (external_call_spec ef cp)); eauto.
      intros ->. destruct cp; try contradiction.
      eauto.
  - eapply perm_compartment2; eauto.
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
  (* - (* same high half *) *)
  (*   intros. eapply same_high_half in m1_m3; eauto. *)
  - intros. erewrite <- ec_preserves_comp; eauto using external_call_spec, find_var_comp1, find_def_valid1.
  - intros.
    eapply meminj_injective; eauto.
  - induction st_rel;
      constructor; eauto.
    inv H.
    + econstructor; eauto.
      * unfold same_content_stack in *.
        intros ? ? ? E G.
        specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
        split; destruct sp1; simpl in *; try congruence.
        { intros ? ? A; inv A. intros ??.
          specialize (X b0 _ eq_refl).
          eapply Mem.range_perm_loadbytes with (cp := top) in X.
          destruct X as [? ?]. eapply ec_readonly' in H1; eauto.
          eapply Mem.loadbytes_range_perm in H1. eapply H1; eauto.
          eapply external_call_spec.
          eapply PERM1. intros. eapply PERM1. simpl; eauto with comps. }
        intros ? G''.
        eapply Mem.load_loadbytes in G'' as G'''.
        destruct G''' as [bytes [R1 R2]].
        eapply ec_readonly in R1; eauto using external_call_spec.
        eapply Mem.loadbytes_load in R1.
        specialize (STACK_CONTENT1 (* _ _ G _ G' *) _ R1) as [R R']; split; subst v; eauto.
        eapply Mem.load_valid_access; eauto.
        eapply PERM1. intros; eapply PERM1.
      * unfold at_most_readable in *.
        destruct sp1; try auto.
        split. eapply external_call_valid_block; eauto. eapply PERM1.
        intros ofs N. eapply PERM1. eapply ec_max_perm; eauto using external_call_spec.
        inv H4. eapply Mem.valid_block_inject_1; eauto using partial_mem_inject.
      * unfold nonempty in *.
        destruct sp1; try contradiction.
        rewrite <- ec_public_not_freeable; eauto using external_call_spec.
        eapply Mem.perm_valid_block. eauto.
        destruct PERM1. intros ?. eapply H1. eapply Mem.perm_implies; eauto. constructor.
      * unfold empty_perm in *. split.
        eapply external_call_valid_block; eauto using external_call_spec.
        eapply EMPTY1.
        intros ofs N. eapply EMPTY1. eapply ec_max_perm; eauto using external_call_spec.
        eapply EMPTY1.
    + eapply stackframe_related_opp_δ; eauto.
      * unfold same_content_stack in *.
        intros ? ? ? E G.
        specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
        split; destruct sp1; simpl in *; try congruence.
        { intros ? ? A; inv A. intros ??.
          specialize (X b0 _ eq_refl).
          eapply Mem.range_perm_loadbytes with (cp := top) in X.
          destruct X as [? ?]. eapply ec_readonly' in H1; eauto.
          eapply Mem.loadbytes_range_perm in H1. eapply H1; eauto.
          eapply external_call_spec.
          eapply PERM1. intros. eapply PERM1. simpl; eauto with comps. }
        intros ? G''.
        eapply Mem.load_loadbytes in G'' as G'''.
        destruct G''' as [bytes [R1 R2]].
        eapply ec_readonly in R1; eauto using external_call_spec.
        eapply Mem.loadbytes_load in R1.
        specialize (STACK_CONTENT1 (* _ _ G _ G' *) _ R1) as [R R']; split; subst v; eauto.
        eapply Mem.load_valid_access; eauto.
        eapply PERM1. intros; eapply PERM1.
      * unfold at_most_readable in *.
        destruct sp1; try auto.
        split. eapply external_call_valid_block; eauto. eapply PERM1.
        intros ofs N. eapply PERM1. eapply ec_max_perm; eauto using external_call_spec.
        eapply PERM1.
      * unfold nonempty in *.
        destruct sp1; try contradiction.
        rewrite <- ec_public_not_freeable; eauto using external_call_spec.
        eapply Mem.perm_valid_block. eauto.
        destruct PERM1. intros ?. eapply H1. eapply Mem.perm_implies; eauto. constructor.
      * unfold empty_perm in *. split.
        eapply external_call_valid_block; eauto using external_call_spec.
        eapply EMPTY1.
        intros ofs N. eapply EMPTY1. eapply ec_max_perm; eauto using external_call_spec.
        eapply EMPTY1.
Qed.

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

  Notation ge1 := (Genv.globalenv W1).
  Notation ge2 := (Genv.globalenv W2).
  Notation ge3 := (Genv.globalenv W3).

  Lemma find_funct_ptr_preserved:
    forall j__δ b b' fd,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      j__δ b = Some (b', 0) ->
      Genv.find_funct_ptr ge1 b = Some fd ->
      exists fd',
        Genv.find_funct_ptr ge3 b' = Some fd' /\
          match_fundef fd fd' /\
          (forall id : ident, Genv.find_symbol ge1 id = Some b -> kept_prog s W1 δ id = true -> fd = fd').
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

    intros; exploit left_implies_eq; eauto. intros A; inv A; auto.
  Qed.

  Lemma find_def_preserved:
    forall j__δ b b' gd,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      j__δ b = Some (b', 0) ->
      Genv.find_def ge1 b = Some gd ->
      exists gd',
        Genv.find_def ge3 b' = Some gd' /\
          match_globdef gd gd' /\
          (forall id : ident, Genv.find_symbol ge1 id = Some b -> kept_prog s W1 δ id = true -> gd' = gd).
  Proof.
    intros j__δ b b' gd inj_pres inj_b_b' find_b_gd.
    exploit defs_inject; eauto. intros [gd' [find_def_b' [_ [match_fd_gd' left_implies_eq]]]].
    eauto.
  Qed.

  Lemma extcall_preserves_mem_rel_opp_side2: forall cp j m1 m3 m3' ef vargs t vres
                                               (not_bottom: cp <> bottom)
                                               (not_top: cp <> top),
      s cp = opposite δ ->
      meminj_preserves_globals s δ W1 W3 j ->
      mem_rel s ge1 ge3 j δ m1 m3 ->
      external_call ef ge3 cp vargs m3 t vres m3' ->
      mem_rel s ge1 ge3 j δ m1 m3'.
  Proof.
    intros cp j m1 m3 m3' ef vargs t vres ? ? side_ef inj_pres m1_m3 extcall.
    constructor.
    - (* same dom *)
      eapply same_dom in m1_m3; eauto.
    - (* injection *)
      exploit partial_mem_inject; eauto. intros m1_inject_m3.
      assert (UNCH1: Mem.unchanged_on (fun b ofs => not (Mem.can_access_block m3 b cp)) m3 m3').
      { eapply ec_outside_comp; eauto using external_call_spec. }
      assert (UNCH: Mem.unchanged_on (fun b ofs => (s, m3) |= b ∈ δ \/ (exists fd : fundef, Genv.find_def ge3 b = Some (Gfun fd))) m3 m3').
      { constructor.
        - (* unchanged_on_nextblock *)
          eapply Mem.unchanged_on_nextblock; eauto.
        - (* unchanged_on_perm *)
          intros. destruct H.
          + pose proof (Mem.unchanged_on_perm _ _ _ UNCH1).
            split.
            * intros ?.
              eapply H1; eauto.
              eapply Mem.perm_max in H2. eapply Mem.perm_implies with (p2 := Nonempty) in H2.
              exploit perm_compartment2; eauto. intros [? G].
              simpl in *; rewrite G in *. intros n. inv n; eauto. now destruct s.
              destruct p; constructor.
            * intros G.
              eapply Mem.perm_max in G as G'. eapply Mem.perm_implies with (p2 := Nonempty) in G'.
              eapply external_call_max_perm in G'; eauto.
              eapply H1; eauto.
              exploit perm_compartment2; eauto. intros [? G''].
              simpl in *; rewrite G'' in *. intros n. inv n; eauto. now destruct s.
              destruct p; constructor.
          + assert (Mem.perm m3 b ofs k p -> p = Nonempty).
            { destruct H as [? H].
              eapply find_def_perm2 with (ofs := ofs) in H; eauto.
              intros G. eapply Mem.perm_max in G.
              destruct p; auto;
                eapply Mem.perm_implies with (p2 := Readable) in G; try contradiction; try constructor. }
            assert (Mem.perm m3' b ofs k p -> p = Nonempty).
            { destruct H as [? H].
              intros G. eapply Mem.perm_max in G.
              eapply external_call_max_perm in G; eauto.
              eapply find_def_perm2 with (ofs := ofs) in H; eauto.
              destruct p; auto;
                eapply Mem.perm_implies with (p2 := Readable) in G; try contradiction; try constructor. }
            destruct H as [? H].
            split.
            * intros G. exploit H1; eauto. intros ->.
              revert G. eapply proj1.
              eapply ec_public_not_freeable; eauto using external_call_spec.
              eapply find_def_perm2 with (ofs := ofs) in H; eauto. intros G.
              eapply Mem.perm_implies with (p2 := Readable) in G; try contradiction.
              constructor.
            * intros G. exploit H2; eauto. intros ->.
              revert G. eapply proj2.
              eapply ec_public_not_freeable; eauto using external_call_spec.
              eapply find_def_perm2 with (ofs := ofs) in H; eauto. intros G.
              eapply Mem.perm_implies with (p2 := Readable) in G; try contradiction.
              constructor.
        - (* unchanged_on_contents *)
          intros. destruct H.
          + eapply Mem.unchanged_on_contents; eauto. simpl in *.
            eapply Mem.perm_max in H0. eapply Mem.perm_implies with (p2 := Nonempty) in H0.
            exploit perm_compartment2; eauto. intros [? G].
            simpl in *; rewrite G in *. intros n. inv n; eauto. now destruct s.
            constructor.
          + (* contradiction *)
            exfalso.
            destruct H as [? H].
            eapply find_def_perm2 with (ofs := ofs) in H; eauto.
            eapply H. eapply Mem.perm_max; eauto.
        - (* unchanged_on_own *)
          eapply Mem.unchanged_on_own; eauto.
      }
      constructor.
      + apply Mem.mi_inj in m1_inject_m3 as mi_inj.
        apply same_dom in m1_m3 as domain. unfold same_domain in domain.

        constructor.
        * intros.
          eapply Mem.perm_unchanged_on; eauto. simpl.
          assert (G: j b1 <> None) by congruence.
          apply domain in G. simpl in G.
          destruct G as [G | G].
          -- left. exploit perm_compartment1; eauto. eapply Mem.perm_max.
             eapply Mem.perm_implies with (p1 := p); eauto. constructor.
             intros [cp' G'].
             assert (Mem.can_access_block m3 b2 (Comp cp')).
             eapply Mem.mi_own; eauto. simpl; rewrite G'; auto with comps.
             simpl in H1.
             exploit perm_compartment2; eauto. eapply Mem.perm_max.
             eapply Mem.perm_implies with (p1 := p); eauto.
             eapply Mem.mi_perm; eauto. constructor.
             intros [? G'']. rewrite G'' in *. inv H1. destruct G. congruence.
          -- right. destruct G as [? G].
             exploit delta_zero; eauto. intros ->.
             exploit find_def_preserved; eauto. intros [? [? [X ?]]]; inv X.
             eauto.
          -- eapply Mem.mi_perm; eauto.
        * intros. simpl in *.
          erewrite Mem.mi_access with (m1 := m1) (m2 := m3); eauto.
          erewrite ec_preserves_comp; eauto using external_call_spec.
          eapply Mem.valid_block_inject_2; eauto.
        * intros. exploit delta_zero; eauto. intros ->. now apply Z.divide_0_r.
        * intros.
          erewrite Mem.unchanged_on_contents with (m_after := m3'); eauto.
          eapply Mem.mi_memval; eauto. simpl.
          assert (G: j b1 <> None) by congruence.
          apply domain in G. simpl in G.
          destruct G as [G | G].
          -- left. exploit perm_compartment1; eauto. eapply Mem.perm_max.
             eapply Mem.perm_implies with (p1 := Readable); eauto. constructor.
             intros [cp' G'].
             assert (Mem.can_access_block m3 b2 (Comp cp')).
             eapply Mem.mi_own; eauto. simpl; rewrite G'; auto with comps.
             simpl in H1.
             exploit perm_compartment2; eauto. eapply Mem.perm_max.
             eapply Mem.perm_implies with (p1 := Readable); eauto.
             eapply Mem.mi_perm; eauto. constructor.
             intros [? G'']. rewrite G'' in *. inv H1. destruct G. congruence.
          -- right. destruct G as [? G].
             exploit delta_zero; eauto. intros ->.
             exploit find_def_preserved; eauto. intros [? [? [X ?]]]; inv X.
             eauto.
          -- eapply Mem.mi_perm; eauto.
      + intros. destruct (j b) as [[]|] eqn:?; auto.
        exfalso.
        exploit (Mem.mi_freeblocks j m1 m3 m1_inject_m3 b); eauto. congruence.
      + intros. exploit Mem.mi_mappedblocks; eauto.
        intros. eapply Mem.valid_block_unchanged_on; eauto.
      + eapply Mem.mi_no_overlap; eauto.
      + eapply Mem.mi_representable; eauto.
      + intros.
        (* exploit Mem.perm_unchanged_on_2; eauto. *)
        simpl.
        apply same_dom in m1_m3 as domain. unfold same_domain in domain.
        assert (G: j b1 <> None) by congruence.
        apply domain in G. simpl in G.
        destruct G as [G | G].
        -- destruct (Mem.perm_dec m1 b1 ofs Max Nonempty); try now right.
           eapply Mem.perm_unchanged_on_2 in H0; try exact UNCH1; eauto.
           eapply Mem.mi_perm_inv; eauto.
           simpl.
           exploit perm_compartment2; eauto. eapply ec_max_perm; eauto using external_call_spec.
           eapply Mem.valid_block_inject_2; eauto.
           eapply Mem.perm_max.
           eapply Mem.perm_implies with (p1 := p); eauto. constructor.
           intros [cp' G'].
           exploit perm_compartment1; eauto.
           intros [cp'' G''].
           assert (cp' = cp'') as <-.
           { assert (Mem.can_access_block m3 b2 (Comp cp'')).
             { eapply Mem.mi_own; eauto. eapply Mem.mi_inj; eauto.
               simpl; rewrite G''; auto with comps. }
             simpl in H1. rewrite G' in H1. now inv H1. }
           rewrite G'. intros X; inv X. congruence. destruct G.
           rewrite G'' in *; now destruct s, δ.
           eapply Mem.valid_block_inject_2; eauto.
        -- destruct G as [? G].
           eapply Mem.perm_unchanged_on_2 in H0; try exact UNCH; eauto.
           eapply Mem.mi_perm_inv; eauto.
           simpl. right.
           exploit delta_zero; eauto. intros ->.
           exploit find_def_preserved; eauto. intros [? [? [X ?]]]; inv X.
           eauto.
           eapply Mem.valid_block_inject_2; eauto.
    - (* Delta zero *)
      intros b b' delta j'_b.
      apply delta_zero in m1_m3; eauto.
    - eapply perm_compartment1; eauto.
    - intros b ofs ?.
      destruct (Classical_Prop.classic (Mem.valid_block m3 b)).
      + pose proof (ec_preserves_comp (external_call_spec ef cp)) as G.
        erewrite <- G; eauto.
        eapply external_call_max_perm in H; eauto.
        exploit perm_compartment2; eauto.
      + exploit Mem.perm_valid_block; eauto. intros ?.
        exploit (ec_new_blocks_comp (external_call_spec ef cp)); eauto.
        intros ->. destruct cp; try contradiction.
        eauto.
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
    - eapply find_var_comp1; eauto.
    - eapply meminj_injective; eauto.
      (* - (* same high half *) *)
  Qed.

  Lemma alloc_preserves_rel1:
    forall cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3 st1 st2 st3
      (not_bottom: cp <> bottom)
      (not_top: cp <> top),
      s |= cp ∈ δ ->
      meminj_preserves_globals s δ W1 W3 j__δ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      meminj_preserves_globals s δ W1 W3 j__δ' /\
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      regset_rel j__δ' rs1 rs3 /\
                      j__δ' b1 = Some (b3, 0) /\
                      inject_incr j__δ j__δ' /\
                      stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ m1' m2 m3' st1 st2 st3.

  Proof.
    intros cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3 st1 st2 st3? ?
      side_cp inj_pres m1_m3 m2_m3 rs1_rs3 alloc1 st_rel1.
    exploit (Mem.alloc_parallel_inject j__δ m1); eauto using partial_mem_inject, Z.le_refl.
    intros [j' [m3' [b3 [? [? [? [? diff]]]]]]].
    exists j', m3', b3.
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]];
      [assumption | (* eapply agrees_with_incr2; eauto | *) (* eapply def_on_addressable_incr; eauto *) | | | intros ?; eauto using val_inject_incr | assumption | assumption |].
    { assert (G: forall s δ p1 p2 j j',
                 meminj_preserves_globals s δ p1 p2 j ->
                 (forall (id: ident) (b: block), Genv.find_symbol (Genv.globalenv p1) id = Some b ->
                                            j' b = j b) ->
                 (forall (b: block) gd, Genv.find_def (Genv.globalenv p1) b = Some gd -> j' b = j b) ->
                 (forall (b b': block) delta gd, Genv.find_def (Genv.globalenv p2) b' = Some gd ->
                                            j' b = Some (b', delta) ->
                                            j b = Some (b', delta)) ->
                 inject_incr j j' ->
                 meminj_preserves_globals s δ p1 p2 j').
      { clear.
        intros s δ p1 p2 j j' [A B C D E] rewr1 rewr2 rewr3 incr.
        constructor.
        - intros. erewrite rewr1 in H; eauto.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. exploit C; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. erewrite rewr2 in H; eauto.
        - intros. eapply rewr3 in H; eauto. }
      eapply G; eauto.
      - clear G.
        intros. eapply diff.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [gd ?].
        eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc1; subst. intros N; subst b; exploit Plt_strict; eauto.
      - clear G.
        intros. eapply diff.
        eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc1; subst. intros N; subst b; exploit Plt_strict; eauto.
      - clear G.
        intros. rewrite <- diff; eauto.
        eapply find_def_valid2 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in H; subst. intros N; subst b.
        assert (b' = Mem.nextblock m3) by congruence. subst b'.
        now exploit Plt_strict; eauto.
    }
    { clear dependent j__oppδ.
      constructor.
      - intros b. destruct (Pos.eq_dec b b1); subst.
        + split; [| congruence].
          intros _. apply Mem.owned_new_block in alloc1 as alloc1'. simpl in alloc1'.
          left; simpl; rewrite alloc1'. split; auto.
          eapply Mem.valid_new_block; eauto.
        + rewrite (diff _ n).
          eapply same_dom in m1_m3. specialize (m1_m3 b).
          eapply Mem.alloc_block_compartment with (b' := b) in alloc1 as alloc1'.
          simpl. rewrite alloc1'. rewrite peq_false; eauto.
          split; eauto. intros A; eapply m1_m3 in A as [[] |]; eauto.
          left; split; eauto. eapply Mem.valid_block_alloc; eauto.
          intros [[] |]; eapply m1_m3; eauto.
          left; split; eauto. eapply Mem.valid_block_alloc_inv in alloc1; eauto.
          destruct alloc1; eauto; contradiction.
      - assumption.
      - intros b b' delta.
        destruct (Pos.eq_dec b b1); subst.
        + congruence.
        + rewrite (diff _ n).
          intros G. exploit delta_zero; eauto.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ alloc1 b ofs Max Nonempty H3).
        eapply Mem.alloc_block_compartment with (b' := b) in alloc1.
        destruct (eq_block b b1); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite alloc1. eapply perm_compartment1; eauto.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ H b ofs Max Nonempty H3).
        eapply Mem.alloc_block_compartment with (b' := b) in H.
        destruct (eq_block b b3); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite H. eapply perm_compartment2; eauto.
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
      - intros. erewrite Mem.alloc_block_compartment; eauto.
        rewrite pred_dec_false; eauto using find_var_comp1.
        intros ?; subst; eapply (Mem.fresh_block_alloc m1); eauto using find_def_valid1.
      - intros b. destruct (Pos.eq_dec b b1); subst; intros.
        + assert (b1' = b3) by congruence. assert (delta1 = 0) by congruence. subst.
          rewrite diff in H5; eauto.
          assert (Mem.valid_block m3 b2'). { eapply Mem.valid_block_inject_2; eauto using partial_mem_inject. }
          apply Mem.fresh_block_alloc in H; eauto.
          intros ?; subst; congruence.
        + rewrite (diff _ n) in H4.
          destruct (Pos.eq_dec b1 b4).
          * assert (b2' = b3) by congruence. assert (delta2 = 0) by congruence. subst.
            assert (Mem.valid_block m3 b1'). { eapply Mem.valid_block_inject_2; eauto using partial_mem_inject. }
            apply Mem.fresh_block_alloc in H; eauto. intros ?; subst; congruence.
          * rewrite diff in H5; eauto.
            clear n0.
            eapply meminj_injective; eauto.
    }
    { clear dependent j__δ.
      destruct m2_m3.
      constructor; eauto.
      - eapply Mem.alloc_right_inject; eauto using partial_mem_inject.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ H b ofs Max Nonempty H1).
        eapply Mem.alloc_block_compartment with (b' := b) in H.
        destruct (eq_block b b3); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite H. eapply perm_compartment4; eauto.
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
    { eapply inject_incr_stack_rel1; eauto.
      induction st_rel1.
      - constructor; eauto.
      - constructor; eauto.
        inv H3.
        + econstructor; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_alloc_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
            inv H8; eapply Mem.valid_block_inject_1; eauto using partial_mem_inject.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; auto.
            intros ? G''. specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM1.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM3.
            intros ? N. eapply PERM3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM3.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp1); eauto.
            eapply EMPTY1.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp3); eauto.
            eapply EMPTY3.
        + simpl in *.
          eapply stackframe_related_opp_δ; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_alloc_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
            eapply PERM1.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; auto.
            intros ? G''. specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM1.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM3.
            intros ? N. eapply PERM3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM3.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp1); eauto.
            eapply EMPTY1.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp3); eauto.
            eapply EMPTY3.
    }
  Qed.

  Lemma alloc_preserves_rel2:
    forall cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3 st1 st2 st3
      (not_bottom: cp <> bottom)
      (not_top: cp <> top),
      s |= cp ∈ opposite δ ->
      meminj_preserves_globals s δ W1 W3 j__δ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      meminj_preserves_globals s δ W1 W3 j__δ' /\
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      regset_rel j__δ' rs1 rs3 /\
                      inject_incr j__δ j__δ' /\
                      stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ m1' m2 m3' st1 st2 st3.
  Proof.
    intros cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3 st1 st2 st3
      ? ? side_cp inj_pres m1_m3 m2_m3 rs1_rs3 alloc1 st_rel1.
    exploit (Mem.alloc_parallel_inject j__δ m1); eauto using partial_mem_inject, Z.le_refl.
    intros [_ [m3' [b3 [alloc3 [_ [_ [_ _]]]]]]].
    exploit (Mem.alloc_left_unmapped_inject j__δ m1); eauto using partial_mem_inject.
    intros [j' [inj [incr [isnone diff]]]].
    exploit Mem.alloc_right_inject; eauto. intros inj'.
    exists j', m3', b3.  split; [| split; [| split; [| split; [| split; [| split]]]]];
      [assumption | (* eapply agrees_with_incr1; eauto | eapply def_on_addressable_incr; eauto *) | | | intros ?; eauto using val_inject_incr | assumption |].
    { assert (G: forall s δ p1 p2 j j',
                 meminj_preserves_globals s δ p1 p2 j ->
                 (forall (id: ident) (b: block), Genv.find_symbol (Genv.globalenv p1) id = Some b ->
                                            j' b = j b) ->
                 (forall (b: block) gd, Genv.find_def (Genv.globalenv p1) b = Some gd -> j' b = j b) ->
                 (forall (b b': block) delta gd, Genv.find_def (Genv.globalenv p2) b' = Some gd ->
                                            j' b = Some (b', delta) ->
                                            j b = Some (b', delta)) ->
                 inject_incr j j' ->
                 meminj_preserves_globals s δ p1 p2 j').
      { clear.
        intros s δ p1 p2 j j' [A B C D E] rewr1 rewr2 rewr3 incr.
        constructor.
        - intros. erewrite rewr1 in H; eauto.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. exploit C; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. erewrite rewr2 in H; eauto.
        - intros. eapply rewr3 in H; eauto. }
      eapply G; eauto.
      - clear G.
        intros. eapply diff.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [gd ?].
        eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc1; subst. intros N; subst b; exploit Plt_strict; eauto.
      - clear G.
        intros. eapply diff.
        eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc1; subst. intros N; subst b; exploit Plt_strict; eauto.
      - clear G.
        intros. rewrite <- diff; eauto.
        eapply find_def_valid2 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc3; subst. intros N; subst b.
        assert (b' = Mem.nextblock m3) by congruence. subst b'.
        now exploit Plt_strict; eauto. }
    { clear dependent j__oppδ.
      constructor; auto.
      - intros b. destruct (Pos.eq_dec b b1); subst.
        + split; [congruence |].
          intros ?. apply Mem.owned_new_block in alloc1. simpl in *. rewrite alloc1 in H.
          apply same_dom in m1_m3. specialize (m1_m3 b1).
          destruct m1_m3 as [_ m1_m3].
          destruct H as [[] |].
          * now destruct δ; congruence.
          * specialize (m1_m3 (or_intror H)).
            assert (exists b1' delta, j__δ b1 = Some (b1', delta)) as [b1' [? G]]
                by now (destruct (j__δ b1) as [[]|]; try congruence; eauto).
            apply incr in G. congruence.
        + rewrite (diff _ n).
          eapply same_dom in m1_m3. specialize (m1_m3 b).
          eapply Mem.alloc_block_compartment with (b' := b) in alloc1 as alloc1'.
          simpl. rewrite alloc1'. rewrite peq_false; eauto.
          split. intros A; eapply m1_m3 in A as [[? ?] | ?]; eauto.
          left; split; eauto. eapply Mem.valid_block_alloc; eauto.
          intros [[] |]; eapply m1_m3; eauto.
          left; split; eauto. eapply Mem.valid_block_alloc_inv in alloc1 as []; eauto.
          congruence.
      - intros b b' delta.
        destruct (Pos.eq_dec b b1); subst.
        + congruence.
        + rewrite (diff _ n).
          intros G. exploit delta_zero; eauto.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ alloc1 b ofs Max Nonempty H).
        eapply Mem.alloc_block_compartment with (b' := b) in alloc1.
        destruct (eq_block b b1); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite alloc1. eapply perm_compartment1; eauto.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ alloc3 b ofs Max Nonempty H).
        eapply Mem.alloc_block_compartment with (b' := b) in alloc3.
        destruct (eq_block b b3); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite alloc3. eapply perm_compartment2; eauto.
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
      - intros. erewrite Mem.alloc_block_compartment; eauto.
        rewrite pred_dec_false; eauto using find_var_comp1.
        intros ?; subst; eapply (Mem.fresh_block_alloc m1); eauto using find_def_valid1.
      - intros b. destruct (Pos.eq_dec b b1); subst; intros.
        + assert (b1' = b3) by congruence. assert (delta1 = 0) by congruence. subst.
          rewrite diff in H1; eauto.
          assert (Mem.valid_block m3 b2'). { eapply Mem.valid_block_inject_2; eauto using partial_mem_inject. }
          apply Mem.fresh_block_alloc in alloc3; eauto.
          intros ?; subst; congruence.
        + rewrite (diff _ n) in H0.
          destruct (Pos.eq_dec b1 b4).
          * assert (b2' = b3) by congruence. assert (delta2 = 0) by congruence. subst.
            assert (Mem.valid_block m3 b1'). { eapply Mem.valid_block_inject_2; eauto using partial_mem_inject. }
            apply Mem.fresh_block_alloc in alloc3; eauto. intros ?; subst; congruence.
          * rewrite diff in H1; eauto.
            clear n0.
            eapply meminj_injective; eauto.
    }
    { clear dependent j__δ.
      destruct m2_m3.
      constructor; eauto.
      - eapply Mem.alloc_right_inject; eauto using partial_mem_inject.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ alloc3 b ofs Max Nonempty H).
        eapply Mem.alloc_block_compartment with (b' := b) in alloc3.
        destruct (eq_block b b3); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite alloc3. eapply perm_compartment4; eauto.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_alloc; eauto.
      - intros. intros n. eapply find_def_perm4; eauto.
        eapply Mem.perm_alloc_4; eauto.
        intros ->.
        exploit (Mem.alloc_result m3); eauto. intros ->.
        eapply Genv.find_def_find_symbol_inversion in H as [id H]; eauto.
        exploit (Senv.find_symbol_below (Genv.globalenv W3)); eauto. intros ?.
        eapply Plt_strict. eapply Plt_Ple_trans; eauto using ple_nextblock2. }
    {
      eapply inject_incr_stack_rel1; eauto. induction st_rel1.
      - constructor; eauto.
      - constructor; eauto.
        inv H.
        + econstructor; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_alloc_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
            eapply PERM1.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; auto.
            intros ? G''. specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM1.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM3.
            intros ? N. eapply PERM3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM3.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp1); eauto.
            eapply EMPTY1.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp3); eauto.
            eapply EMPTY3.
        + simpl in *.
          eapply stackframe_related_opp_δ; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_alloc_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
            eapply PERM1.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; auto.
            intros ? G''. specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM1.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM3.
            intros ? N. eapply PERM3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM3.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp1); eauto.
            eapply EMPTY1.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp3); eauto.
            eapply EMPTY3.
    }
  Qed.

  Lemma alloc_preserves_rel:
    forall cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3 st1 st2 st3
      (not_bottom: cp <> bottom)
      (not_top: cp <> top),
      meminj_preserves_globals s δ W1 W3 j__δ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      meminj_preserves_globals s δ W1 W3 j__δ' /\
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      regset_rel j__δ' rs1 rs3 /\
                      (s |= cp ∈ δ -> j__δ' b1 = Some (b3, 0)) /\
                      inject_incr j__δ j__δ' /\
                      stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ m1' m2 m3' st1 st2 st3.
  Proof.
    intros.
    destruct (side_eq (s cp) δ) as [s_cp | s_cp].
    - exploit alloc_preserves_rel1; eauto.
      intros [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto).
    - exploit alloc_preserves_rel2; eauto. now simpl; destruct (s cp); destruct δ.
      intros [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto). simpl; congruence.
  Qed.

  Lemma alloc_preserves_rel1_no_regset:
    forall cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 st1 st2 st3
      (not_bottom: cp <> bottom)
      (not_top: cp <> top),
      s |= cp ∈ δ ->
      meminj_preserves_globals s δ W1 W3 j__δ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      meminj_preserves_globals s δ W1 W3 j__δ' /\
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      j__δ' b1 = Some (b3, 0) /\
                      inject_incr j__δ j__δ' /\
                      stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ m1' m2 m3' st1 st2 st3.
  Proof.
    intros cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 st1 st2 st3 ? ?
      side_cp inj_pres m1_m3 m2_m3 st_rel alloc1.
    exploit (Mem.alloc_parallel_inject j__δ m1); eauto using partial_mem_inject, Z.le_refl.
    intros [j' [m3' [b3 [? [? [? [? diff]]]]]]].
    exists j', m3', b3.
    split; [| split; [| split; [| split; [| split; [| split]]]]];
      [assumption | (* eapply agrees_with_incr2; eauto | *) (* eapply def_on_addressable_incr; eauto *) | | | assumption | assumption |].
    { assert (G: forall s δ p1 p2 j j',
                 meminj_preserves_globals s δ p1 p2 j ->
                 (forall (id: ident) (b: block), Genv.find_symbol (Genv.globalenv p1) id = Some b ->
                                            j' b = j b) ->
                 (forall (b: block) gd, Genv.find_def (Genv.globalenv p1) b = Some gd -> j' b = j b) ->
                 (forall (b b': block) delta gd, Genv.find_def (Genv.globalenv p2) b' = Some gd ->
                                            j' b = Some (b', delta) ->
                                            j b = Some (b', delta)) ->
                 inject_incr j j' ->
                 meminj_preserves_globals s δ p1 p2 j').
      { clear.
        intros s δ p1 p2 j j' [A B C D E] rewr1 rewr2 rewr3 incr.
        constructor.
        - intros. erewrite rewr1 in H; eauto.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. exploit C; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. erewrite rewr2 in H; eauto.
        - intros. eapply rewr3 in H; eauto. }
      eapply G; eauto.
      - clear G.
        intros. eapply diff.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [gd ?].
        eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc1; subst. intros N; subst b; exploit Plt_strict; eauto.
      - clear G.
        intros. eapply diff.
        eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc1; subst. intros N; subst b; exploit Plt_strict; eauto.
      - clear G.
        intros. rewrite <- diff; eauto.
        eapply find_def_valid2 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in H; subst. intros N; subst b.
        assert (b' = Mem.nextblock m3) by congruence. subst b'.
        now exploit Plt_strict; eauto.
    }
    { clear dependent j__oppδ.
      constructor.
      - intros b. destruct (Pos.eq_dec b b1); subst.
        + split; [| congruence].
          intros _. apply Mem.owned_new_block in alloc1 as alloc1'. simpl in alloc1'.
          left; simpl; rewrite alloc1'. split; auto.
          eapply Mem.valid_new_block; eauto.
        + rewrite (diff _ n).
          eapply same_dom in m1_m3. specialize (m1_m3 b).
          eapply Mem.alloc_block_compartment with (b' := b) in alloc1 as alloc1'.
          simpl. rewrite alloc1'. rewrite peq_false; eauto.
          split; eauto. intros A; eapply m1_m3 in A as [[] |]; eauto.
          left; split; eauto. eapply Mem.valid_block_alloc; eauto.
          intros [[] |]; eapply m1_m3; eauto.
          left; split; eauto. eapply Mem.valid_block_alloc_inv in alloc1; eauto.
          destruct alloc1; eauto; contradiction.
      - assumption.
      - intros b b' delta.
        destruct (Pos.eq_dec b b1); subst.
        + congruence.
        + rewrite (diff _ n).
          intros G. exploit delta_zero; eauto.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ alloc1 b ofs Max Nonempty H3).
        eapply Mem.alloc_block_compartment with (b' := b) in alloc1.
        destruct (eq_block b b1); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite alloc1. eapply perm_compartment1; eauto.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ H b ofs Max Nonempty H3).
        eapply Mem.alloc_block_compartment with (b' := b) in H.
        destruct (eq_block b b3); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite H. eapply perm_compartment2; eauto.
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
      - intros. erewrite Mem.alloc_block_compartment; eauto.
        rewrite pred_dec_false; eauto using find_var_comp1.
        intros ?; subst; eapply (Mem.fresh_block_alloc m1); eauto using find_def_valid1.
      - intros b. destruct (Pos.eq_dec b b1); subst; intros.
        + assert (b1' = b3) by congruence. assert (delta1 = 0) by congruence. subst.
          rewrite diff in H5; eauto.
          assert (Mem.valid_block m3 b2'). { eapply Mem.valid_block_inject_2; eauto using partial_mem_inject. }
          apply Mem.fresh_block_alloc in H; eauto.
          intros ?; subst; congruence.
        + rewrite (diff _ n) in H4.
          destruct (Pos.eq_dec b1 b4).
          * assert (b2' = b3) by congruence. assert (delta2 = 0) by congruence. subst.
            assert (Mem.valid_block m3 b1'). { eapply Mem.valid_block_inject_2; eauto using partial_mem_inject. }
            apply Mem.fresh_block_alloc in H; eauto. intros ?; subst; congruence.
          * rewrite diff in H5; eauto.
            clear n0.
            eapply meminj_injective; eauto.
    }
    { clear dependent j__δ.
      destruct m2_m3.
      constructor; eauto.
      - eapply Mem.alloc_right_inject; eauto using partial_mem_inject.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ H b ofs Max Nonempty H1).
        eapply Mem.alloc_block_compartment with (b' := b) in H.
        destruct (eq_block b b3); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite H. eapply perm_compartment4; eauto.
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
    { eapply inject_incr_stack_rel1; eauto.
      induction st_rel.
      - constructor; eauto.
      - constructor; eauto.
        inv H3.
        + econstructor; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_alloc_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
            inv H8; eapply Mem.valid_block_inject_1; eauto using partial_mem_inject.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; auto.
            intros ? G''. specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM1.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM3.
            intros ? N. eapply PERM3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM3.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp1); eauto.
            eapply EMPTY1.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp3); eauto.
            eapply EMPTY3.
        + simpl in *.
          eapply stackframe_related_opp_δ; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_alloc_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
            eapply PERM1.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; auto.
            intros ? G''. specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM1.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM3.
            intros ? N. eapply PERM3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM3.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp1); eauto.
            eapply EMPTY1.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp3); eauto.
            eapply EMPTY3.
    }
  Qed.

  Lemma alloc_preserves_rel2_no_regset:
    forall cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 st1 st2 st3
      (not_bottom: cp <> bottom)
      (not_top: cp <> top),
      s |= cp ∈ opposite δ ->
      meminj_preserves_globals s δ W1 W3 j__δ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      meminj_preserves_globals s δ W1 W3 j__δ' /\
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      inject_incr j__δ j__δ' /\
                      stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ m1' m2 m3' st1 st2 st3.
  Proof.
    intros cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 st1 st2 st3
      ? ? side_cp inj_pres m1_m3 m2_m3 st_rel alloc1.
    exploit (Mem.alloc_parallel_inject j__δ m1); eauto using partial_mem_inject, Z.le_refl.
    intros [_ [m3' [b3 [alloc3 [_ [_ [_ _]]]]]]].
    exploit (Mem.alloc_left_unmapped_inject j__δ m1); eauto using partial_mem_inject.
    intros [j' [inj [incr [isnone diff]]]].
    exploit Mem.alloc_right_inject; eauto. intros inj'.
    exists j', m3', b3.  split; [| split; [| split; [| split; [| split]]]];
      [assumption | | | | assumption |].
    { assert (G: forall s δ p1 p2 j j',
                 meminj_preserves_globals s δ p1 p2 j ->
                 (forall (id: ident) (b: block), Genv.find_symbol (Genv.globalenv p1) id = Some b ->
                                            j' b = j b) ->
                 (forall (b: block) gd, Genv.find_def (Genv.globalenv p1) b = Some gd -> j' b = j b) ->
                 (forall (b b': block) delta gd, Genv.find_def (Genv.globalenv p2) b' = Some gd ->
                                            j' b = Some (b', delta) ->
                                            j b = Some (b', delta)) ->
                 inject_incr j j' ->
                 meminj_preserves_globals s δ p1 p2 j').
      { clear.
        intros s δ p1 p2 j j' [A B C D E] rewr1 rewr2 rewr3 incr.
        constructor.
        - intros. erewrite rewr1 in H; eauto.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. exploit C; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. erewrite rewr2 in H; eauto.
        - intros. eapply rewr3 in H; eauto. }
      eapply G; eauto.
      - clear G.
        intros. eapply diff.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [gd ?].
        eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc1; subst. intros N; subst b; exploit Plt_strict; eauto.
      - clear G.
        intros. eapply diff.
        eapply find_def_valid1 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc1; subst. intros N; subst b; exploit Plt_strict; eauto.
      - clear G.
        intros. rewrite <- diff; eauto.
        eapply find_def_valid2 in m1_m3; eauto. unfold Mem.valid_block in m1_m3.
        eapply Mem.alloc_result in alloc3; subst. intros N; subst b.
        assert (b' = Mem.nextblock m3) by congruence. subst b'.
        now exploit Plt_strict; eauto. }
    { clear dependent j__oppδ.
      constructor; auto.
      - intros b. destruct (Pos.eq_dec b b1); subst.
        + split; [congruence |].
          intros ?. apply Mem.owned_new_block in alloc1. simpl in *. rewrite alloc1 in H.
          apply same_dom in m1_m3. specialize (m1_m3 b1).
          destruct m1_m3 as [_ m1_m3].
          destruct H as [[] |].
          * now destruct δ; congruence.
          * specialize (m1_m3 (or_intror H)).
            assert (exists b1' delta, j__δ b1 = Some (b1', delta)) as [b1' [? G]]
                by now (destruct (j__δ b1) as [[]|]; try congruence; eauto).
            apply incr in G. congruence.
        + rewrite (diff _ n).
          eapply same_dom in m1_m3. specialize (m1_m3 b).
          eapply Mem.alloc_block_compartment with (b' := b) in alloc1 as alloc1'.
          simpl. rewrite alloc1'. rewrite peq_false; eauto.
          split. intros A; eapply m1_m3 in A as [[? ?] | ?]; eauto.
          left; split; eauto. eapply Mem.valid_block_alloc; eauto.
          intros [[] |]; eapply m1_m3; eauto.
          left; split; eauto. eapply Mem.valid_block_alloc_inv in alloc1 as []; eauto.
          congruence.
      - intros b b' delta.
        destruct (Pos.eq_dec b b1); subst.
        + congruence.
        + rewrite (diff _ n).
          intros G. exploit delta_zero; eauto.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ alloc1 b ofs Max Nonempty H).
        eapply Mem.alloc_block_compartment with (b' := b) in alloc1.
        destruct (eq_block b b1); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite alloc1. eapply perm_compartment1; eauto.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ alloc3 b ofs Max Nonempty H).
        eapply Mem.alloc_block_compartment with (b' := b) in alloc3.
        destruct (eq_block b b3); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite alloc3. eapply perm_compartment2; eauto.
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
      - intros. erewrite Mem.alloc_block_compartment; eauto.
        rewrite pred_dec_false; eauto using find_var_comp1.
        intros ?; subst; eapply (Mem.fresh_block_alloc m1); eauto using find_def_valid1.
      - intros b. destruct (Pos.eq_dec b b1); subst; intros.
        + assert (b1' = b3) by congruence. assert (delta1 = 0) by congruence. subst.
          rewrite diff in H1; eauto.
          assert (Mem.valid_block m3 b2'). { eapply Mem.valid_block_inject_2; eauto using partial_mem_inject. }
          apply Mem.fresh_block_alloc in alloc3; eauto.
          intros ?; subst; congruence.
        + rewrite (diff _ n) in H0.
          destruct (Pos.eq_dec b1 b4).
          * assert (b2' = b3) by congruence. assert (delta2 = 0) by congruence. subst.
            assert (Mem.valid_block m3 b1'). { eapply Mem.valid_block_inject_2; eauto using partial_mem_inject. }
            apply Mem.fresh_block_alloc in alloc3; eauto. intros ?; subst; congruence.
          * rewrite diff in H1; eauto.
            clear n0.
            eapply meminj_injective; eauto.
    }
    { clear dependent j__δ.
      destruct m2_m3.
      constructor; eauto.
      - eapply Mem.alloc_right_inject; eauto using partial_mem_inject.
      - intros.
        pose proof (Mem.perm_alloc_inv _ _ _ _ _ _ alloc3 b ofs Max Nonempty H).
        eapply Mem.alloc_block_compartment with (b' := b) in alloc3.
        destruct (eq_block b b3); try subst b.
        + destruct cp; try contradiction. eauto.
        + rewrite alloc3. eapply perm_compartment4; eauto.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_alloc; eauto.
      - intros. intros n. eapply find_def_perm4; eauto.
        eapply Mem.perm_alloc_4; eauto.
        intros ->.
        exploit (Mem.alloc_result m3); eauto. intros ->.
        eapply Genv.find_def_find_symbol_inversion in H as [id H]; eauto.
        exploit (Senv.find_symbol_below (Genv.globalenv W3)); eauto. intros ?.
        eapply Plt_strict. eapply Plt_Ple_trans; eauto using ple_nextblock2. }

    { eapply inject_incr_stack_rel1; eauto. induction st_rel.
      - constructor; eauto.
      - constructor; eauto.
        inv H.
        + econstructor; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_alloc_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
            eapply PERM1.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; auto.
            intros ? G''. specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM1.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM3.
            intros ? N. eapply PERM3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM3.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp1); eauto.
            eapply EMPTY1.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp3); eauto.
            eapply EMPTY3.
        + simpl in *.
          eapply stackframe_related_opp_δ; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_alloc_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_alloc_unchanged in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
            eapply PERM1.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; auto.
            intros ? G''. specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_alloc_other; eauto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM1.
            intros ? N. eapply PERM1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM1.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_alloc; eauto. eapply PERM3.
            intros ? N. eapply PERM3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := b); eauto.
            eapply PERM3.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_alloc_1; eauto.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp1); eauto.
            eapply EMPTY1.
          * unfold empty_perm in *. split.
            eapply Mem.valid_block_alloc; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3. eapply Mem.perm_alloc_4; eauto.
            intros <-. eapply Mem.fresh_block_alloc with (b := dummy_sp3); eauto.
            eapply EMPTY3.
    }
  Qed.

  Lemma alloc_preserves_rel_no_regset:
    forall cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 st1 st2 st3
      (not_bottom: cp <> bottom)
      (not_top: cp <> top),
      meminj_preserves_globals s δ W1 W3 j__δ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      meminj_preserves_globals s δ W1 W3 j__δ' /\
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      (s |= cp ∈ δ -> j__δ' b1 = Some (b3, 0)) /\
                      inject_incr j__δ j__δ' /\
                      stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ m1' m2 m3' st1 st2 st3.
  Proof.
    intros.
    destruct (side_eq (s cp) δ) as [s_cp | s_cp].
    - exploit alloc_preserves_rel1_no_regset; eauto.
      intros [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto).
    - exploit alloc_preserves_rel2_no_regset; eauto. now simpl; destruct (s cp); destruct δ.
      intros [? [? [? [? [? [? [? [? ?]]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto). simpl; congruence.
  Qed.

  Lemma free_preserves_rel:
    forall cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 b3 st1 st2 st3,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
      j__δ b1 = Some (b3, 0) -> (* we are necessarily in the δ case *)
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      Mem.free m1 b1 lo hi cp = Some m1' ->
      exists m3', Mem.free m3 b3 lo hi cp = Some m3' /\
               mem_rel s ge1 ge3 j__δ δ m1' m3' /\
               mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
               stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1' m2 m3' st1 st2 st3.
  Proof.
    intros cp cp_main j__δ j__oppδ m1 m1' m2 m3 lo hi b1 b3 st1 st2 st3
      pres_globs1 pres_globs2 ptr_inj m1_m3 m2_m3 st_rel1 free1 .
    exploit (Mem.free_parallel_inject j__δ m1); eauto using partial_mem_inject.
    intros [m3' [free3 m1'_m3']].
    rewrite 2!Z.add_0_r in free3.
    exists m3'; split; [| split; [| split]]; [assumption | | |].
    { clear dependent j__oppδ.
      constructor.
      - intros b. apply same_dom in m1_m3.
        specialize (m1_m3 b).
        simpl in *. apply Mem.free_result in free1. unfold Mem.unchecked_free in free1.
        destruct (zle hi lo); now subst.
      - assumption.
      - intros b b' delta.
        intros G. exploit delta_zero; eauto.
      - intros. erewrite <- Mem.free_preserves_comp; eauto.
        exploit perm_compartment1; eauto.
        eapply Mem.perm_free_3; eauto.
      - intros. erewrite <- Mem.free_preserves_comp; eauto.
        exploit perm_compartment2; eauto.
        eapply Mem.perm_free_3; eauto.
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
      - intros. erewrite <- Mem.free_preserves_comp; eauto using find_var_comp1.
      - eapply meminj_injective; eauto.
    }
    { destruct m2_m3.
      constructor; auto.
      - eapply Mem.free_right_inject; eauto.
        intros.
        apply Mem.mi_inj in partial_mem_inject0.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m2 b0)) in partial_mem_inject0; eauto.
        specialize (same_dom0 b0).
        assert (X: j__oppδ b0 <> None) by congruence.
        apply same_dom0 in X. simpl in *.
        apply same_dom in m1_m3 as G.
        specialize (G b1).
        assert (Y: j__δ b1 <> None) by congruence.
        apply G in Y. simpl in *. clear G.
        assert (m1_m3' := m1_m3).
        apply partial_mem_inject in m1_m3.
        apply Mem.mi_inj in m1_m3.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m1 b1)) in m1_m3; eauto.
        unfold Mem.can_access_block in *.
        assert (R1: Mem.block_compartment m3 b3 = Mem.block_compartment m1 b1).
        { exploit Mem.free_range_perm; eauto. intros P.
          apply Mem.perm_max in P. apply Mem.perm_implies with (p2 := Nonempty) in P;
            try now constructor.
          exploit perm_compartment4; eauto. intros [? G].
          clear free3 P.
          exploit Mem.free_range_perm; eauto. intros P'.
          apply Mem.perm_max in P'. apply Mem.perm_implies with (p2 := Nonempty) in P';
            try now constructor.
          exploit perm_compartment1; eauto. intros [? G'].
          rewrite G, G' in m1_m3. inv m1_m3. congruence. }
        assert (R2: Mem.block_compartment m3 b3 = Mem.block_compartment m2 b0).
        { exploit Mem.free_range_perm; eauto. intros P.
          apply Mem.perm_max in P. apply Mem.perm_implies with (p2 := Nonempty) in P;
            try now constructor.
          exploit perm_compartment4; eauto. intros [? G].
          apply Mem.perm_max in H0. apply Mem.perm_implies with (p2 := Nonempty) in H0;
            try now constructor.
          exploit perm_compartment3; eauto. intros [? G'].
          rewrite G, G' in partial_mem_inject0. inv partial_mem_inject0. congruence. }
        { destruct X as [[? ?] | [? X]], Y as [[? ?] | [? Y]], δ; simpl in *; try congruence.
          - exploit find_def_perm1; eauto.
            instantiate (1 := (ofs + delta)).
            exploit Mem.free_range_perm. exact free1. eauto.
            intros R. eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply R. constructor.
          - exploit find_def_perm1; eauto.
            instantiate (1 := (ofs + delta)).
            exploit Mem.free_range_perm. exact free1. eauto.
            intros R. eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply R. constructor.
          - clear m1_m3'.
            assert (exists x', Genv.find_def ge3 b3 = Some (Gfun x')) as [? ?].
            { exploit defs_inject; eauto. intros [? [? [_ [G _]]]].
              inv G; eauto. }
            exploit find_def_perm4; eauto.
            instantiate (1 := (ofs + delta)).
            exploit Mem.free_range_perm. exact free3. eauto.
            intros R. eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply R. constructor.
          - clear m1_m3'.
            assert (exists x', Genv.find_def ge3 b3 = Some (Gfun x')) as [? ?].
            { exploit defs_inject; eauto. intros [? [? [_ [G _]]]].
              inv G; eauto. }
            exploit find_def_perm4; eauto.
            instantiate (1 := (ofs + delta)).
            exploit Mem.free_range_perm. exact free3. eauto.
            intros R. eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply R. constructor.
          - clear m1_m3'.
            assert (exists x', Genv.find_def ge3 b3 = Some (Gfun x')) as [? ?].
            { exploit defs_inject; eauto. intros [? [? [_ [G _]]]].
              inv G; eauto. }
            exploit find_def_perm4; eauto.
            instantiate (1 := (ofs + delta)).
            exploit Mem.free_range_perm. exact free3. eauto.
            intros R. eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply R. constructor.
          - clear m1_m3'.
            assert (exists x', Genv.find_def ge3 b3 = Some (Gfun x')) as [? ?].
            { exploit defs_inject; eauto. intros [? [? [_ [G _]]]].
              inv G; eauto. }
            exploit find_def_perm4; eauto.
            instantiate (1 := (ofs + delta)).
            exploit Mem.free_range_perm. exact free3. eauto.
            intros R. eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply R. constructor.
        }
        assert (delta = 0). { eapply delta_zero0; eauto. }
        eapply Mem.free_range_perm in free1. eapply free1. instantiate (1 := ofs). lia.

        simpl in *.
        simpl; auto with comps.
        simpl; auto with comps.
      - intros. erewrite <- Mem.free_preserves_comp; eauto.
        exploit perm_compartment4; eauto.
        eapply Mem.perm_free_3; eauto.
      - erewrite Mem.nextblock_free; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_free_1; eauto.
      - intros. intros n.
        eapply find_def_perm4; eauto.
        eapply Mem.perm_free_3; eauto. }
    { induction st_rel1.
      - constructor; eauto.
      - constructor; eauto.
        inv H.
        + econstructor; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_free_1; eauto.
              destruct (Pos.eqb_spec b5 b1); auto; subst; right.
              destruct (zlt ofs0 lo); auto; right.
              destruct (zle hi ofs0); auto. exfalso.
              clear free3.
              exploit Mem.free_range_perm; eauto. instantiate (1 := ofs0); lia. intros ?.
              eapply PERM1. eapply Mem.perm_max, Mem.perm_implies; eauto. constructor.
              eapply X; eauto. }
            intros ? G''.
            eapply Mem.load_free_2 in G'' as G'''; eauto.
            specialize (STACK_CONTENT1 _ G''') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_free; eauto.
            destruct (zlt lo hi).
            exploit Mem.free_range_perm; eauto. instantiate (1 := lo); lia.
            intros ?. left; intros ?; subst.
            eapply PERM3, Mem.perm_max, Mem.perm_implies; eauto. constructor.
            right; left; auto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; destruct sp2; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?. eapply X; eauto. }
            intros ? G''.
            specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_free; eauto.
            destruct (zlt lo hi).
            exploit Mem.free_range_perm; eauto. instantiate (1 := lo); lia.
            intros ?. left; intros ?; subst.
            eapply PERM3, Mem.perm_max, Mem.perm_implies; eauto. constructor.
            right; left; auto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_free_1; eauto. eapply PERM1.
            intros ? N. eapply PERM1.
            eapply Mem.perm_free_3; eauto.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_free_1; eauto. eapply PERM3.
            intros ? N. eapply PERM3.
            eapply Mem.perm_free_3; eauto.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.free_range_perm in free1 as ?.
            destruct (eq_block b b1). subst.
            -- destruct (zlt 0 lo); auto.
               eapply Mem.perm_free_1; eauto.
               destruct (zle hi 0); auto.
               eapply Mem.perm_free_1; eauto. exfalso.
               eapply PERM1.
               apply Mem.range_perm_max in H.
               eapply Mem.perm_implies.
               eapply H. instantiate (1 := lo). lia. constructor.
            -- eapply Mem.perm_free_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.free_range_perm in free3 as ?.
            destruct (eq_block b b3). subst.
            -- destruct (zlt 0 lo); auto.
               eapply Mem.perm_free_1; eauto.
               destruct (zle hi 0); auto.
               eapply Mem.perm_free_1; eauto. exfalso.
               eapply PERM3.
               apply Mem.range_perm_max in H.
               eapply Mem.perm_implies.
               eapply H. instantiate (1 := lo). lia. constructor.
            -- eapply Mem.perm_free_1; eauto.
          * split.
            eapply Mem.valid_block_free_1; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1.
            eapply Mem.perm_free_3; eauto.
          * split.
            eapply Mem.valid_block_free_1; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3.
            eapply Mem.perm_free_3; eauto.
        + simpl in *.
          eapply stackframe_related_opp_δ; eauto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?.
              eapply Mem.perm_free_1; eauto.
              destruct (Pos.eqb_spec b5 b1); auto; subst; right.
              destruct (zlt ofs0 lo); auto; right.
              destruct (zle hi ofs0); auto. exfalso.
              clear free3.
              exploit Mem.free_range_perm; eauto. instantiate (1 := ofs0); lia. intros ?.
              eapply PERM1. eapply Mem.perm_max, Mem.perm_implies; eauto. constructor.
              eapply X; eauto. }
            intros ? G''.
            eapply Mem.load_free_2 in G'' as G'''; eauto.
            specialize (STACK_CONTENT1 _ G''') as [? ?]. split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_free; eauto.
            destruct (zlt lo hi).
            exploit Mem.free_range_perm; eauto. instantiate (1 := lo); lia.
            intros ?. left; intros ?; subst.
            eapply PERM3, Mem.perm_max, Mem.perm_implies; eauto. constructor.
            right; left; auto.
          * unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; destruct sp2; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?. eapply X; eauto. }
            intros ? G''.
            specialize (STACK_CONTENT2 _ G'') as [? ?].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_free; eauto.
            destruct (zlt lo hi).
            exploit Mem.free_range_perm; eauto. instantiate (1 := lo); lia.
            intros ?. left; intros ?; subst.
            eapply PERM3, Mem.perm_max, Mem.perm_implies; eauto. constructor.
            right; left; auto.
          * unfold at_most_readable in *. destruct sp1; try auto.
            split. eapply Mem.valid_block_free_1; eauto. eapply PERM1.
            intros ? N. eapply PERM1.
            eapply Mem.perm_free_3; eauto.
          * unfold at_most_readable in *. destruct sp3; try auto.
            split. eapply Mem.valid_block_free_1; eauto. eapply PERM3.
            intros ? N. eapply PERM3.
            eapply Mem.perm_free_3; eauto.
          * unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.free_range_perm in free1 as ?.
            destruct (eq_block b b1). subst.
            -- destruct (zlt 0 lo); auto.
               eapply Mem.perm_free_1; eauto.
               destruct (zle hi 0); auto.
               eapply Mem.perm_free_1; eauto. exfalso.
               eapply PERM1.
               apply Mem.range_perm_max in H.
               eapply Mem.perm_implies.
               eapply H. instantiate (1 := lo). lia. constructor.
            -- eapply Mem.perm_free_1; eauto.
          * unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.free_range_perm in free3 as ?.
            destruct (eq_block b b3). subst.
            -- destruct (zlt 0 lo); auto.
               eapply Mem.perm_free_1; eauto.
               destruct (zle hi 0); auto.
               eapply Mem.perm_free_1; eauto. exfalso.
               eapply PERM3.
               apply Mem.range_perm_max in H.
               eapply Mem.perm_implies.
               eapply H. instantiate (1 := lo). lia. constructor.
            -- eapply Mem.perm_free_1; eauto.
          * split.
            eapply Mem.valid_block_free_1; eauto. eapply EMPTY1.
            intros ? N. eapply EMPTY1.
            eapply Mem.perm_free_3; eauto.
          * split.
            eapply Mem.valid_block_free_1; eauto. eapply EMPTY3.
            intros ? N. eapply EMPTY3.
            eapply Mem.perm_free_3; eauto.
    }
  Qed.

  Lemma store_preserves_rel:
    forall cp cp_main (j__δ j__oppδ: meminj) m1 m1' m2 m3 ch ofs v1 v3 b1 b3 st1 st2 st3
      (not_bottom: cp <> bottom)
      (not_top: cp <> top),
      meminj_preserves_globals s δ W1 W3 j__δ ->
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
      j__δ b1 = Some (b3, 0) -> (* we are necessarily in the δ case *)
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      Val.inject j__δ v1 v3 ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      Mem.store ch m1 b1 ofs v1 cp = Some m1' ->
      exists m3', Mem.store ch m3 b3 ofs v3 cp = Some m3' /\
               mem_rel s ge1 ge3 j__δ δ m1' m3' /\
               mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
               stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1' m2 m3' st1 st2 st3.
  Proof.
    intros cp cp_main j__δ j__oppδ m1 m1' m2 m3 ch ofs v1 v3 b1 b3 st1 st2 st3 ? ?
      pres_globs1 pres_globs2 ptr_inj m1_m3 m2_m3 val_inj st_rel store1.
    exploit (Mem.store_mapped_inject j__δ); eauto using partial_mem_inject.
    intros [m3' [store3 ?]].
    rewrite Z.add_0_r in store3.
    exists m3'; split; [| split; [| split]]; [assumption | | |].
    { clear dependent j__oppδ.
      constructor.
      - intros b. apply same_dom in m1_m3.
        specialize (m1_m3 b). simpl in *.
        eapply Mem.store_block_compartment in store1 as store1'. rewrite store1'.
        split. intros A; eapply m1_m3 in A as [[] |]; eauto.
        left; split; eauto. eapply Mem.store_valid_block_1; eauto.
        intros [[] |]; eapply m1_m3; eauto.
        left; split; eauto. eapply Mem.store_valid_block_2; eauto.
      - assumption.
      - now eapply delta_zero; eauto.
      - intros. erewrite <- Mem.store_preserves_comp; eauto.
        eapply perm_compartment1; eauto.
        eapply Mem.perm_store_2; eauto.
      - intros. erewrite <- Mem.store_preserves_comp; eauto.
        eapply perm_compartment2; eauto.
        eapply Mem.perm_store_2; eauto.
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock2.
      - intros. exploit find_def_valid1; eauto. eapply Mem.store_valid_block_1; eauto.
      - intros. exploit find_def_valid2; eauto. eapply Mem.store_valid_block_1; eauto.
      - intros; intros n. exploit find_def_perm1; eauto.
        eapply Mem.perm_store_2; eauto.
      - intros; intros n. exploit find_def_perm2; eauto.
        eapply Mem.perm_store_2; eauto.
      - intros. erewrite <- Mem.store_preserves_comp; eauto using find_var_comp1.
      - eapply meminj_injective; eauto.
    }
    { destruct m2_m3.
      constructor; eauto.
      - eapply Mem.store_outside_inject; eauto.
        intros.
        apply Mem.mi_inj in partial_mem_inject0.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m2 b')) in partial_mem_inject0; eauto.
        specialize (same_dom0 b').
        assert (X: j__oppδ b' <> None) by congruence.
        apply same_dom0 in X. simpl in *.
        apply same_dom in m1_m3 as G.
        specialize (G b1).
        assert (Y: j__δ b1 <> None) by congruence.
        apply G in Y. simpl in *. clear G.
        assert (m1_m3' := m1_m3).
        apply partial_mem_inject in m1_m3.
        apply Mem.mi_inj in m1_m3.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m1 b1)) in m1_m3; eauto.
        simpl in m1_m3.
        assert (R1: Mem.block_compartment m3 b3 = Mem.block_compartment m1 b1).
        { exploit Mem.store_valid_access_3; eauto.
          intros [G [_ _]]. specialize (G ofs). exploit G; try lia.
          intros P.
          apply Mem.perm_max in P. apply Mem.perm_implies with (p2 := Nonempty) in P;
            try now constructor.
          exploit perm_compartment4; eauto. intros [? G'].
          clear store3 P.
          exploit Mem.store_valid_access_3; eauto.
          intros [A [_ _]]. specialize (A ofs). exploit A; try lia.
          intros P'.
          apply Mem.perm_max in P'. apply Mem.perm_implies with (p2 := Nonempty) in P';
            try now constructor.
          exploit perm_compartment1; eauto. intros [? A'].
          rewrite G', A' in m1_m3. inv m1_m3. congruence. }
        assert (R2: Mem.block_compartment m3 b3 = Mem.block_compartment m2 b').
        { exploit Mem.store_valid_access_3; eauto.
          intros [G [_ _]]. specialize (G ofs). exploit G; try lia.
          intros P.
          apply Mem.perm_max in P. apply Mem.perm_implies with (p2 := Nonempty) in P;
            try now constructor.
          exploit perm_compartment4; eauto. intros [? G'].
          clear store3 P.
          apply Mem.perm_max in H1. apply Mem.perm_implies with (p2 := Nonempty) in H1;
            try now constructor.
          exploit perm_compartment3; eauto. intros [? A'].
          rewrite A', G' in partial_mem_inject0. inv partial_mem_inject0. congruence. }
        rewrite <- R1, <- R2 in *.
        { destruct X as [[? X] | [? X]], Y as [[? Y] | [? Y]], δ; simpl in *; try congruence.
          - exploit find_def_perm1; eauto.
            exploit Mem.store_valid_access_4. exact store1. intros [].
            instantiate (1 := ofs).
            eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply H4. lia. constructor.
          - exploit find_def_perm1; eauto.
            exploit Mem.store_valid_access_4. exact store1. intros [].
            instantiate (1 := ofs).
            eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply H4. lia. constructor.
          - clear m1_m3'.
            assert (exists x', Genv.find_def ge3 b3 = Some (Gfun x')) as [? ?].
            { exploit defs_inject; eauto. intros [? [? [_ [G _]]]].
              inv G; eauto. }
            exploit find_def_perm4; eauto.
            exploit Mem.store_valid_access_4. exact store3. intros [].
            instantiate (1 := ofs).
            eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply H5. lia. constructor.
          - clear m1_m3'.
            assert (exists x', Genv.find_def ge3 b3 = Some (Gfun x')) as [? ?].
            { exploit defs_inject; eauto. intros [? [? [_ [G _]]]].
              inv G; eauto. }
            exploit find_def_perm4; eauto.
            exploit Mem.store_valid_access_4. exact store3. intros [].
            instantiate (1 := ofs).
            eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply H5. lia. constructor.
          - exploit find_def_perm1; eauto.
            exploit Mem.store_valid_access_4. exact store1. intros [].
            instantiate (1 := ofs).
            eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply H3. lia. constructor.
          - exploit find_def_perm1; eauto.
            exploit Mem.store_valid_access_4. exact store1. intros [].
            instantiate (1 := ofs).
            eapply Mem.perm_cur_max. eapply Mem.perm_implies.
            eapply H3. lia. constructor. }
        eapply Mem.store_valid_access_3; eauto.
        simpl; auto with comps.
        simpl; auto with comps.
      - intros. erewrite <- Mem.store_preserves_comp; eauto.
        exploit perm_compartment4; eauto.
        eapply Mem.perm_store_2; eauto.
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. exploit find_def_valid2; eauto. eapply Mem.store_valid_block_1; eauto.
      - intros; intros n. exploit find_def_perm2; eauto.
        eapply Mem.perm_store_2; eauto. }
    - { induction st_rel.
        constructor; eauto.
        constructor; eauto.
        inv H0; eauto.
        - econstructor; eauto.
          + unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            Opaque Stacklayout.fe_ofs_arg Z.mul. simpl in *.
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?. eapply Mem.perm_store_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_store_other in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? R].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_store_other; eauto.
            { left.
              intros ?; subst.
              exploit Mem.store_valid_access_3; eauto. intros [VA [? ?]].
              eapply PERM3, Mem.perm_max, VA; eauto.
              instantiate (1 := ofs).
              destruct ch; simpl; lia. }
            { left.
              intros ?; subst.
              eapply Mem.store_valid_access_3 in store1; eauto.
              destruct store1 as [VA [? ?]].
              eapply PERM1, Mem.perm_max, VA; eauto.
              instantiate (1 := ofs).
              destruct ch; simpl; lia. }
          + unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            Opaque Stacklayout.fe_ofs_arg Z.mul. simpl in *.
            split; destruct sp2; simpl in *; try congruence.
            { eapply X. }
            intros ? G''.
            specialize (STACK_CONTENT2 _ G'') as [? R].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_store_other; eauto.
            { left.
              intros ?; subst.
              exploit Mem.store_valid_access_3; eauto. intros [VA [? ?]].
              eapply PERM3, Mem.perm_max, VA; eauto.
              instantiate (1 := ofs).
              destruct ch; simpl; lia. }
          + unfold at_most_readable in *.
            destruct sp1; try auto.
            split. eapply Mem.store_valid_block_1; eauto. eapply PERM1.
            intros o N. eapply PERM1. now eapply Mem.perm_store_2; eauto.
          + unfold at_most_readable in *.
            destruct sp3; try auto.
            split. eapply Mem.store_valid_block_1; eauto. eapply PERM3.
            intros o N. eapply PERM3. now eapply Mem.perm_store_2; eauto.
          + unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_store_1; eauto.
          + unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_store_1; eauto.
          + split. eapply Mem.store_valid_block_1; eauto. eapply EMPTY1.
            intros o N. eapply EMPTY1. now eapply Mem.perm_store_2; eauto.
          + split. eapply Mem.store_valid_block_1; eauto. eapply EMPTY3.
            intros o N. eapply EMPTY3. now eapply Mem.perm_store_2; eauto.
        - eapply stackframe_related_opp_δ; eauto.
          + unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT1 _ _ _ E G) as [X STACK_CONTENT1].
            Opaque Stacklayout.fe_ofs_arg Z.mul. simpl in *.
            split; destruct sp1; simpl in *; try congruence.
            { intros ? ? A; inv A. intros ? ?. eapply Mem.perm_store_1; eauto. eapply X; eauto. }
            intros ? G''.
            erewrite Mem.load_store_other in G''; eauto.
            specialize (STACK_CONTENT1 _ G'') as [? R].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_store_other; eauto.
            { left.
              intros ?; subst.
              exploit Mem.store_valid_access_3; eauto. intros [VA [? ?]].
              eapply PERM3, Mem.perm_max, VA; eauto.
              instantiate (1 := ofs).
              destruct ch; simpl; lia. }
            { left.
              intros ?; subst.
              eapply Mem.store_valid_access_3 in store1; eauto.
              destruct store1 as [VA [? ?]].
              eapply PERM1, Mem.perm_max, VA; eauto.
              instantiate (1 := ofs).
              destruct ch; simpl; lia. }
          + unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            Opaque Stacklayout.fe_ofs_arg Z.mul. simpl in *.
            split; destruct sp2; simpl in *; try congruence.
            { eapply X. }
            intros ? G''.
            specialize (STACK_CONTENT2 _ G'') as [? R].
            split; auto.
            destruct sp3; simpl in *; try congruence.
            erewrite Mem.load_store_other; eauto.
            { left.
              intros ?; subst.
              exploit Mem.store_valid_access_3; eauto. intros [VA [? ?]].
              eapply PERM3, Mem.perm_max, VA; eauto.
              instantiate (1 := ofs).
              destruct ch; simpl; lia. }
          + unfold at_most_readable in *.
            destruct sp1; try auto.
            split. eapply Mem.store_valid_block_1; eauto. eapply PERM1.
            intros o N. eapply PERM1. now eapply Mem.perm_store_2; eauto.
          + unfold at_most_readable in *.
            destruct sp3; try auto.
            split. eapply Mem.store_valid_block_1; eauto. eapply PERM3.
            intros o N. eapply PERM3. now eapply Mem.perm_store_2; eauto.
          + unfold nonempty in *.
            destruct sp1; try contradiction.
            eapply Mem.perm_store_1; eauto.
          + unfold nonempty in *.
            destruct sp3; try contradiction.
            eapply Mem.perm_store_1; eauto.
          + split. eapply Mem.store_valid_block_1; eauto. eapply EMPTY1.
            intros o N. eapply EMPTY1. now eapply Mem.perm_store_2; eauto.
          + split. eapply Mem.store_valid_block_1; eauto. eapply EMPTY3.
            intros o N. eapply EMPTY3. now eapply Mem.perm_store_2; eauto.
      }
  Qed.

  Lemma regset_rel_inject: forall j rs1 rs3 rd v v',
      regset_rel j rs1 rs3 ->
      Val.inject j v v' ->
      regset_rel j (rs1 # rd <- v) (rs3 # rd <- v').
  Proof.
    intros.
    intros r.
    destruct (Pregmap.elt_eq r rd); now try subst r; Simpl.
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


  Lemma find_comp_preserved:
    forall j__δ v v'
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      v <> Vundef ->
      Val.inject j__δ v v' ->
      Genv.find_comp_in_genv ge1 v = Genv.find_comp_in_genv ge3 v'.
  Proof.
    intros j v v' inj_pres delta_zero nundef H.
    inv H; simpl; auto; try congruence.
    exploit find_comp_of_block_preserved; eauto.
  Qed.


  Lemma update_stack_call_preserved_internal:
    forall j__δ sg rs1 rs1' rs3 st1 st1' m1 m1' m3 st3 cp
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      (rs1 PC <> Vundef) ->
      Genv.find_comp_in_genv ge1 (rs1 PC) = cp ->
      regset_rel j__δ rs1 rs3 ->
      update_stack_call ge1 st1 sg cp rs1 m1 = Some (st1', rs1', m1') ->
      st1' = st1 /\ rs1' = rs1 /\ m1' = m1 /\
        update_stack_call ge3 st3 sg cp rs3 m3 = Some (st3, rs3, m3).
  Proof.
    intros * inj_pres delta_zero nundef samecomp rs1_rs3.
    unfold update_stack_call.
    destruct cp_eq_dec; try contradiction.
    intros R; inv R.
    repeat split; eauto.
    erewrite <- find_comp_preserved; eauto.
    destruct cp_eq_dec; try contradiction. reflexivity.
  Qed.

  Lemma set_perm_preserves_rel:
    forall cp_main j j' m1 m2 m3 m1' m2' b1 b2 b3 delta st1 st2 st3,
      j b1 = Some (b3, delta) ->
      Mem.set_perm m1 b1 Readable = Some m1' ->
      forall (NOTDEF1: forall fd, Genv.find_def ge1 b1 <> Some (Gfun fd)),
        Mem.set_perm m2 b2 Readable = Some m2' ->
        forall (NOTDEF2: forall fd, Genv.find_def ge2 b2 <> Some (Gfun fd)),
        forall (NOTDEF3: forall fd, Genv.find_def ge3 b3 <> Some (Gfun fd)),
          mem_rel s ge1 ge3 j δ m1 m3 ->
          mem_rel s ge2 ge3 j' (opposite δ) m2 m3 ->
          stack_rel s cp_main ge1 ge2 ge3 δ j j' m1 m2 m3 st1 st2 st3 ->
          exists m3', Mem.set_perm m3 b3 Readable = Some m3' /\
                   mem_rel s ge1 ge3 j δ m1' m3' /\
                   mem_rel s ge2 ge3 j' (opposite δ) m2' m3' /\
                   stack_rel s cp_main ge1 ge2 ge3 δ j j' m1' m2' m3' st1 st2 st3.
  Proof.
    intros cp_main j j' m1 m2 m3 m1' m2' b1 b2 b3 delta st1 st2 st3 j_b1 set1 ? set2 ? ? m1_m3 m2_m3 st_rel.
    exploit (Mem.set_parallel_inject j m1 m3); eauto;
      [eapply partial_mem_inject; eauto | |].
    { eapply meminj_injective; eauto. }
    intros [m3' [set3 m1'_m3'_inj]].
    eexists; split; eauto.
    split; [| split].
    - constructor; eauto.
      + eapply same_dom in m1_m3; eauto.
        unfold same_domain. intros; split; intros.
        * eapply m1_m3 in H. destruct H as [[] |].
          -- left. simpl. erewrite <- Mem.set_preserves_comp; eauto.
             split; eauto. eapply Mem.set_perm_valid_block_1; eauto.
          -- right. eauto.
        * destruct H as [[] |].
          -- eapply m1_m3; left. simpl; erewrite Mem.set_preserves_comp; eauto.
             split; eauto. eapply Mem.set_perm_valid_block_2; eauto.
          -- eapply m1_m3; right; eauto.
      + eapply delta_zero; eauto.
      + intros. clear set3 set2 m2_m3. exploit Mem.set_perm_perm; eauto.
        intros [? ?]. exploit perm_compartment1; eauto. eapply Mem.perm_implies; eauto. constructor.
        intros [? ?]. erewrite <- Mem.set_preserves_comp; eauto.
      + intros. clear set1 set2 m2_m3. exploit Mem.set_perm_perm; eauto.
        intros [? ?]. exploit perm_compartment2; eauto. eapply Mem.perm_implies; eauto. constructor.
        intros [? ?]. erewrite <- Mem.set_preserves_comp; eauto.
      + unfold Mem.set_perm in set1. destruct plt; try discriminate.
        inv set1. simpl. eapply ple_nextblock1; eauto.
      + unfold Mem.set_perm in set3. destruct plt; try discriminate.
        inv set3. simpl. eapply ple_nextblock2; eauto.
      + intros. eapply Mem.set_perm_valid_block_1; eauto. eapply find_def_valid1; eauto.
      + intros. eapply Mem.set_perm_valid_block_1; eauto. eapply find_def_valid2; eauto.
      + intros.
        intros n. clear set2 set3.
        assert (b <> b1).
        { intros ?; subst b1.
          exploit NOTDEF1; eauto. }
        exploit Mem.perm_set_2'; eauto. eapply find_def_perm1; eauto.
      + intros.
        intros n. clear set1 set2.
        assert (b <> b3).
        { intros ?; subst b3.
          exploit NOTDEF3; eauto. }
        exploit Mem.perm_set_2'; eauto. eapply find_def_perm2; eauto.
      + intros. erewrite <- Mem.set_preserves_comp; eauto. eapply find_var_comp1; eauto.
      + intros. clear m2_m3. eapply meminj_injective; eauto.
    - constructor; eauto.
      + eapply same_dom in m2_m3; eauto.
        unfold same_domain. intros; split; intros.
        * eapply m2_m3 in H. destruct H as [[] |].
          -- left. simpl. erewrite <- Mem.set_preserves_comp; eauto.
             split; eauto. eapply Mem.set_perm_valid_block_1; eauto.
          -- right. eauto.
        * destruct H as [[] |].
          -- eapply m2_m3; left. simpl; erewrite Mem.set_preserves_comp; eauto.
             split; eauto. eapply Mem.set_perm_valid_block_2; eauto.
          -- eapply m2_m3; right; eauto.
      + eapply Mem.set_outside_inject_parallel; eauto.
        constructor.
        eapply partial_mem_inject; eauto.
        eapply partial_mem_inject; eauto.
      + eapply delta_zero; eauto.
      + intros. clear set3 set1 m1_m3. exploit Mem.set_perm_perm; eauto.
        intros [? ?]. exploit perm_compartment1; eauto. eapply Mem.perm_implies; eauto. constructor.
        intros [? ?]. erewrite <- Mem.set_preserves_comp; eauto.
      + intros. clear set1 set2 m2_m3. exploit Mem.set_perm_perm; eauto.
        intros [? ?]. exploit perm_compartment2; eauto. eapply Mem.perm_implies; eauto. constructor.
        intros [? ?]. erewrite <- Mem.set_preserves_comp; eauto.
      + unfold Mem.set_perm in set2. destruct plt; try discriminate.
        inv set2. simpl. eapply ple_nextblock1; eauto.
      + unfold Mem.set_perm in set3. destruct plt; try discriminate.
        inv set3. simpl. eapply ple_nextblock2; eauto.
      + intros. eapply Mem.set_perm_valid_block_1; eauto. eapply find_def_valid1; eauto.
      + intros. eapply Mem.set_perm_valid_block_1; eauto. eapply find_def_valid2; eauto.
      + intros.
        intros n. clear set1 set3.
        assert (b <> b2).
        { intros ?; subst b2.
          exploit NOTDEF2; eauto. }
        exploit Mem.perm_set_2'; eauto. eapply find_def_perm1; eauto.
      + intros.
        intros n. clear set1 set2.
        assert (b <> b3).
        { intros ?; subst b3.
          exploit NOTDEF3; eauto. }
        exploit Mem.perm_set_2'; eauto. eapply find_def_perm2; eauto.
      + intros. erewrite <- Mem.set_preserves_comp; eauto. eapply find_var_comp1; eauto.
      + intros. clear m1_m3. eapply meminj_injective; eauto.
    - induction st_rel; try now constructor.
      constructor; eauto.
      inv H.
      + econstructor; eauto.
        * intros ?????.
          split.
          { intros ? ? A; inv A. intros ? ?.
            exploit STACK_CONTENT1; eauto. intros [X _].
            exploit X; eauto.
            destruct (Pos.eqb_spec b b1).
            -- subst.
               unfold Mem.set_perm in set1.
               destruct (plt b1 (Mem.nextblock m1)); try discriminate.
               inv set1. unfold Mem.perm in *. simpl in *.
               rewrite PMap.gsspec in *. destruct peq; try congruence.
               destruct (((Mem.mem_access m1) !! b1 ofs0 Cur)) eqn:R; auto.
               pose proof (Mem.access_max m1 b1 ofs0) as G. rewrite R in G; simpl in G.
               destruct ((Mem.mem_access m1) !! b1 ofs0 Max) eqn:R'; auto.
               intros _; constructor.
               intros G'; inv G'.
            -- intros ?. eapply Mem.perm_set_2; eauto. }
          intros ??.
          assert (G: Mem.loadv (chunk_of_type ty) m1 (Val.offset_ptr sp1 (Ptrofs.repr bofs)) top = Some v).
          { destruct sp1; simpl in *; try congruence.
            eapply Mem.load_set' in H2; eauto. constructor.
            exploit STACK_CONTENT1; eauto. intros [X ?]. intros ? ?. eapply X; eauto. }
          exploit STACK_CONTENT1; eauto. intros [? STACK_CONTENT1'].
          exploit STACK_CONTENT1'; eauto. intros []; split; eauto.
          destruct sp3; simpl in *; try congruence.
          eapply Mem.load_set; eauto. constructor.
        * intros ?????.
          split.
          { intros ? ? A; inv A. intros ? ?.
            exploit STACK_CONTENT2; eauto. intros [X _].
            exploit X; eauto.
            destruct (Pos.eqb_spec b b2).
            -- subst.
               unfold Mem.set_perm in set2.
               destruct (plt b2 (Mem.nextblock m2)); try discriminate.
               inv set2. unfold Mem.perm in *. simpl in *.
               rewrite PMap.gsspec in *. destruct peq; try congruence.
               destruct (((Mem.mem_access m2) !! b2 ofs0 Cur)) eqn:R; auto.
               pose proof (Mem.access_max m2 b2 ofs0) as G. rewrite R in G; simpl in G.
               destruct ((Mem.mem_access m2) !! b2 ofs0 Max) eqn:R'; auto.
               intros _; constructor.
               intros G'; inv G'.
            -- intros ?. eapply Mem.perm_set_2; eauto. }
          intros ??.
          assert (G: Mem.loadv (chunk_of_type ty) m2 (Val.offset_ptr sp2 (Ptrofs.repr bofs)) top = Some v).
          { destruct sp2; simpl in *; try congruence.
            eapply Mem.load_set' in H2; eauto. constructor.
            exploit STACK_CONTENT2; eauto. intros [X ?]. intros ? ?. eapply X; eauto. }
          exploit STACK_CONTENT2; eauto. intros [? STACK_CONTENT2'].
          exploit STACK_CONTENT2'; eauto. intros []; split; eauto.
          destruct sp3; simpl in *; try congruence.
          eapply Mem.load_set; eauto. constructor.
        * destruct sp1; simpl in *; eauto.
          destruct PERM1.
          split; eauto using Mem.set_perm_valid_block_1.
          destruct (Pos.eqb_spec b b1).
          -- subst. intros. intros ?.
             unfold Mem.set_perm in set1.
             destruct (plt b1 (Mem.nextblock m1)); try discriminate.
             inv set1. unfold Mem.perm in *. simpl in *.
             rewrite PMap.gsspec in *. destruct peq; try congruence.
             specialize (H1 ofs).
             destruct (((Mem.mem_access m1) !! b1 ofs Max)); auto. inv H2.
          -- intros ? ?. eapply H1. eapply Mem.perm_set_4; eauto.
        * destruct sp2; simpl in *; eauto.
          destruct PERM2.
          split; eauto using Mem.set_perm_valid_block_1.
          destruct (Pos.eqb_spec b b2).
          -- subst. intros. intros ?.
             unfold Mem.set_perm in set2.
             destruct (plt b2 (Mem.nextblock m2)); try discriminate.
             inv set2. unfold Mem.perm in *. simpl in *.
             rewrite PMap.gsspec in *. destruct peq; try congruence.
             specialize (H1 ofs).
             destruct (((Mem.mem_access m2) !! b2 ofs Max)); auto. inv H2.
          -- intros ? ?. eapply H1. eapply Mem.perm_set_4; eauto.
        * destruct sp3; simpl in *; eauto.
          destruct PERM3.
          split; eauto using Mem.set_perm_valid_block_1.
          destruct (Pos.eqb_spec b b3).
          -- subst. intros. intros ?.
             unfold Mem.set_perm in set3.
             destruct (plt b3 (Mem.nextblock m3)); try discriminate.
             inv set3. unfold Mem.perm in *. simpl in *.
             rewrite PMap.gsspec in *. destruct peq; try congruence.
             specialize (H1 ofs).
             destruct (((Mem.mem_access m3) !! b3 ofs Max)); auto. inv H2.
          -- intros ? ?. eapply H1. eapply Mem.perm_set_4; eauto.
        * unfold nonempty in *.
          destruct sp1; try contradiction.
          destruct (eq_block b1 b).
          -- subst. eapply Mem.perm_implies. eapply Mem.perm_set_1; eauto.
             constructor.
          -- eapply Mem.perm_implies. eapply Mem.perm_set_2; eauto.
             constructor.
        * unfold nonempty in *.
          destruct sp2; try contradiction.
          destruct (eq_block b2 b).
          -- subst. eapply Mem.perm_implies. eapply Mem.perm_set_1; eauto.
             constructor.
          -- eapply Mem.perm_implies. eapply Mem.perm_set_2; eauto.
             constructor.
        * unfold nonempty in *.
          destruct sp3; try contradiction.
          destruct (eq_block b3 b).
          -- subst. eapply Mem.perm_implies. eapply Mem.perm_set_1; eauto.
             constructor.
          -- eapply Mem.perm_implies. eapply Mem.perm_set_2; eauto.
             constructor.
        * unfold empty_perm in *.
          destruct EMPTY1. split; eauto using Mem.set_perm_valid_block_1.
          intros ? n.
          eapply Mem.set_perm_perm in n as [? G]; eauto. eapply Mem.perm_implies in G. now eapply H1; eauto.
          constructor.
        * unfold empty_perm in *.
          destruct EMPTY2. split; eauto using Mem.set_perm_valid_block_1.
          intros ? n.
          eapply Mem.set_perm_perm in n as [? G]; eauto. eapply Mem.perm_implies in G. now eapply H1; eauto.
          constructor.
        * unfold empty_perm in *.
          destruct EMPTY3. split; eauto using Mem.set_perm_valid_block_1.
          intros ? n.
          eapply Mem.set_perm_perm in n as [? G]; eauto. eapply Mem.perm_implies in G. now eapply H1; eauto.
          constructor.
      + eapply stackframe_related_opp_δ; eauto.
        * intros ?????.
          split.
          { intros ? ? A; inv A. intros ? ?.
            exploit STACK_CONTENT1; eauto. intros [X _].
            exploit X; eauto.
            destruct (Pos.eqb_spec b b1).
            -- subst.
               unfold Mem.set_perm in set1.
               destruct (plt b1 (Mem.nextblock m1)); try discriminate.
               inv set1. unfold Mem.perm in *. simpl in *.
               rewrite PMap.gsspec in *. destruct peq; try congruence.
               destruct (((Mem.mem_access m1) !! b1 ofs0 Cur)) eqn:R; auto.
               pose proof (Mem.access_max m1 b1 ofs0) as G. rewrite R in G; simpl in G.
               destruct ((Mem.mem_access m1) !! b1 ofs0 Max) eqn:R'; auto.
               intros _; constructor.
               intros G'; inv G'.
            -- intros ?. eapply Mem.perm_set_2; eauto. }
          intros ??.
          assert (G: Mem.loadv (chunk_of_type ty) m1 (Val.offset_ptr sp1 (Ptrofs.repr bofs)) top = Some v).
          { destruct sp1; simpl in *; try congruence.
            eapply Mem.load_set' in H7; eauto. constructor.
            exploit STACK_CONTENT1; eauto. intros [X ?]. intros ? ?. eapply X; eauto. }
          exploit STACK_CONTENT1; eauto. intros [? STACK_CONTENT1'].
          exploit STACK_CONTENT1'; eauto. intros []; split; eauto.
          destruct sp3; simpl in *; try congruence.
          eapply Mem.load_set; eauto. constructor.
        * intros ?????.
          split.
          { intros ? ? A; inv A. intros ? ?.
            exploit STACK_CONTENT2; eauto. intros [X _].
            exploit X; eauto.
            destruct (Pos.eqb_spec b b2).
            -- subst.
               unfold Mem.set_perm in set2.
               destruct (plt b2 (Mem.nextblock m2)); try discriminate.
               inv set2. unfold Mem.perm in *. simpl in *.
               rewrite PMap.gsspec in *. destruct peq; try congruence.
               destruct (((Mem.mem_access m2) !! b2 ofs0 Cur)) eqn:R; auto.
               pose proof (Mem.access_max m2 b2 ofs0) as G. rewrite R in G; simpl in G.
               destruct ((Mem.mem_access m2) !! b2 ofs0 Max) eqn:R'; auto.
               intros _; constructor.
               intros G'; inv G'.
            -- intros ?. eapply Mem.perm_set_2; eauto. }
          intros ??.
          assert (G: Mem.loadv (chunk_of_type ty) m2 (Val.offset_ptr sp2 (Ptrofs.repr bofs)) top = Some v).
          { destruct sp2; simpl in *; try congruence.
            eapply Mem.load_set' in H7; eauto. constructor.
            exploit STACK_CONTENT2; eauto. intros [X ?]. intros ? ?. eapply X; eauto. }
          exploit STACK_CONTENT2; eauto. intros [? STACK_CONTENT2'].
          exploit STACK_CONTENT2'; eauto. intros []; split; eauto.
          destruct sp3; simpl in *; try congruence.
          eapply Mem.load_set; eauto. constructor.
        * destruct sp1; simpl in *; eauto.
          destruct PERM1.
          split; eauto using Mem.set_perm_valid_block_1.
          destruct (Pos.eqb_spec b b1).
          -- subst. intros. intros ?.
             unfold Mem.set_perm in set1.
             destruct (plt b1 (Mem.nextblock m1)); try discriminate.
             inv set1. unfold Mem.perm in *. simpl in *.
             rewrite PMap.gsspec in *. destruct peq; try congruence.
             specialize (H1 ofs).
             destruct (((Mem.mem_access m1) !! b1 ofs Max)); auto. inv H7.
          -- intros ? ?. eapply H1. eapply Mem.perm_set_4; eauto.
        * destruct sp2; simpl in *; eauto.
          destruct PERM2.
          split; eauto using Mem.set_perm_valid_block_1.
          destruct (Pos.eqb_spec b b2).
          -- subst. intros. intros ?.
             unfold Mem.set_perm in set2.
             destruct (plt b2 (Mem.nextblock m2)); try discriminate.
             inv set2. unfold Mem.perm in *. simpl in *.
             rewrite PMap.gsspec in *. destruct peq; try congruence.
             specialize (H1 ofs).
             destruct (((Mem.mem_access m2) !! b2 ofs Max)); auto. inv H7.
          -- intros ? ?. eapply H1. eapply Mem.perm_set_4; eauto.
        * destruct sp3; simpl in *; eauto.
          destruct PERM3.
          split; eauto using Mem.set_perm_valid_block_1.
          destruct (Pos.eqb_spec b b3).
          -- subst. intros. intros ?.
             unfold Mem.set_perm in set3.
             destruct (plt b3 (Mem.nextblock m3)); try discriminate.
             inv set3. unfold Mem.perm in *. simpl in *.
             rewrite PMap.gsspec in *. destruct peq; try congruence.
             specialize (H1 ofs).
             destruct (((Mem.mem_access m3) !! b3 ofs Max)); auto. inv H7.
          -- intros ? ?. eapply H1. eapply Mem.perm_set_4; eauto.
        * unfold nonempty in *.
          destruct sp1; try contradiction.
          destruct (eq_block b1 b).
          -- subst. eapply Mem.perm_implies. eapply Mem.perm_set_1; eauto.
             constructor.
          -- eapply Mem.perm_implies. eapply Mem.perm_set_2; eauto.
             constructor.
        * unfold nonempty in *.
          destruct sp2; try contradiction.
          destruct (eq_block b2 b).
          -- subst. eapply Mem.perm_implies. eapply Mem.perm_set_1; eauto.
             constructor.
          -- eapply Mem.perm_implies. eapply Mem.perm_set_2; eauto.
             constructor.
        * unfold nonempty in *.
          destruct sp3; try contradiction.
          destruct (eq_block b3 b).
          -- subst. eapply Mem.perm_implies. eapply Mem.perm_set_1; eauto.
             constructor.
          -- eapply Mem.perm_implies. eapply Mem.perm_set_2; eauto.
             constructor.
        * unfold empty_perm in *.
          destruct EMPTY1. split; eauto using Mem.set_perm_valid_block_1.
          intros ? n.
          eapply Mem.set_perm_perm in n as [? G]; eauto. eapply Mem.perm_implies in G. now eapply H1; eauto.
          constructor.
        * unfold empty_perm in *.
          destruct EMPTY2. split; eauto using Mem.set_perm_valid_block_1.
          intros ? n.
          eapply Mem.set_perm_perm in n as [? G]; eauto. eapply Mem.perm_implies in G. now eapply H1; eauto.
          constructor.
        * unfold empty_perm in *.
          destruct EMPTY3. split; eauto using Mem.set_perm_valid_block_1.
          intros ? n.
          eapply Mem.set_perm_perm in n as [? G]; eauto. eapply Mem.perm_implies in G. now eapply H1; eauto.
          constructor.
  Qed.

  Lemma set_perm_preserves_rel':
    forall j j' m1 m2 m3 m1' m2' b1 b2 b3 delta,
      j b1 = Some (b3, delta) ->
      Mem.set_perm m1 b1 Freeable = Some m1' ->
      forall (NOTDEF1: forall fd, Genv.find_def ge1 b1 <> Some (Gfun fd)),
        Mem.set_perm m2 b2 Freeable = Some m2' ->
        forall (NOTDEF2: forall fd, Genv.find_def ge2 b2 <> Some (Gfun fd)),
        forall (NOTDEF3: forall fd, Genv.find_def ge3 b3 <> Some (Gfun fd)),
          mem_rel s ge1 ge3 j δ m1 m3 ->
          mem_rel s ge2 ge3 j' (opposite δ) m2 m3 ->
          exists m3', Mem.set_perm m3 b3 Freeable = Some m3' /\
                   mem_rel s ge1 ge3 j δ m1' m3' /\
                   mem_rel s ge2 ge3 j' (opposite δ) m2' m3'.
  Proof.
    intros j j' m1 m2 m3 m1' m2' b1 b2 b3 delta j_b1 set1 ? set2 ? ?
      m1_m3 m2_m3.
    exploit (Mem.set_parallel_inject j m1 m3); eauto;
      [eapply partial_mem_inject; eauto | |].
    { eapply meminj_injective; eauto. }
    intros [m3' [set3 m1'_m3'_inj]].
    eexists; split; eauto.
    split.
    - constructor; eauto.
      + eapply same_dom in m1_m3; eauto.
        unfold same_domain. intros; split; intros.
        * eapply m1_m3 in H. destruct H as [[] |].
          -- left. simpl. erewrite <- Mem.set_preserves_comp; eauto.
             split; eauto. eapply Mem.set_perm_valid_block_1; eauto.
          -- right. eauto.
        * destruct H as [[] |].
          -- eapply m1_m3; left. simpl; erewrite Mem.set_preserves_comp; eauto.
             split; eauto. eapply Mem.set_perm_valid_block_2; eauto.
          -- eapply m1_m3; right; eauto.
      + eapply delta_zero; eauto.
      + intros. clear set3 set2 m2_m3. exploit Mem.set_perm_perm; eauto.
        intros [? ?]. exploit perm_compartment1; eauto. eapply Mem.perm_implies; eauto. constructor.
        intros [? ?]. erewrite <- Mem.set_preserves_comp; eauto.
      + intros. clear set1 set2 m2_m3. exploit Mem.set_perm_perm; eauto.
        intros [? ?]. exploit perm_compartment2; eauto. eapply Mem.perm_implies; eauto. constructor.
        intros [? ?]. erewrite <- Mem.set_preserves_comp; eauto.
      + unfold Mem.set_perm in set1. destruct plt; try discriminate.
        inv set1. simpl. eapply ple_nextblock1; eauto.
      + unfold Mem.set_perm in set3. destruct plt; try discriminate.
        inv set3. simpl. eapply ple_nextblock2; eauto.
      + intros. eapply Mem.set_perm_valid_block_1; eauto. eapply find_def_valid1; eauto.
      + intros. eapply Mem.set_perm_valid_block_1; eauto. eapply find_def_valid2; eauto.
      + intros.
        intros n. clear set2 set3.
        assert (b <> b1).
        { intros ?; subst b1.
          exploit NOTDEF1; eauto. }
        exploit Mem.perm_set_2'; eauto. eapply find_def_perm1; eauto.
      + intros.
        intros n. clear set1 set2.
        assert (b <> b3).
        { intros ?; subst b3.
          exploit NOTDEF3; eauto. }
        exploit Mem.perm_set_2'; eauto. eapply find_def_perm2; eauto.
      + intros. erewrite <- Mem.set_preserves_comp; eauto. eapply find_var_comp1; eauto.
      + intros. clear m2_m3. eapply meminj_injective; eauto.
    - constructor; eauto.
      + eapply same_dom in m2_m3; eauto.
        unfold same_domain. intros; split; intros.
        * eapply m2_m3 in H. destruct H as [[] |].
          -- left. simpl. erewrite <- Mem.set_preserves_comp; eauto.
             split; eauto. eapply Mem.set_perm_valid_block_1; eauto.
          -- right. eauto.
        * destruct H as [[] |].
          -- eapply m2_m3; left. simpl; erewrite Mem.set_preserves_comp; eauto.
             split; eauto. eapply Mem.set_perm_valid_block_2; eauto.
          -- eapply m2_m3; right; eauto.
      + eapply Mem.set_outside_inject_parallel; eauto.
        constructor.
        eapply partial_mem_inject; eauto.
        eapply partial_mem_inject; eauto.
      + eapply delta_zero; eauto.
      + intros. clear set3 set1 m1_m3. exploit Mem.set_perm_perm; eauto.
        intros [? ?]. exploit perm_compartment1; eauto. eapply Mem.perm_implies; eauto. constructor.
        intros [? ?]. erewrite <- Mem.set_preserves_comp; eauto.
      + intros. clear set1 set2 m2_m3. exploit Mem.set_perm_perm; eauto.
        intros [? ?]. exploit perm_compartment2; eauto. eapply Mem.perm_implies; eauto. constructor.
        intros [? ?]. erewrite <- Mem.set_preserves_comp; eauto.
      + unfold Mem.set_perm in set2. destruct plt; try discriminate.
        inv set2. simpl. eapply ple_nextblock1; eauto.
      + unfold Mem.set_perm in set3. destruct plt; try discriminate.
        inv set3. simpl. eapply ple_nextblock2; eauto.
      + intros. eapply Mem.set_perm_valid_block_1; eauto. eapply find_def_valid1; eauto.
      + intros. eapply Mem.set_perm_valid_block_1; eauto. eapply find_def_valid2; eauto.
      + intros.
        intros n. clear set1 set3.
        assert (b <> b2).
        { intros ?; subst b2.
          exploit NOTDEF2; eauto. }
        exploit Mem.perm_set_2'; eauto. eapply find_def_perm1; eauto.
      + intros.
        intros n. clear set1 set2.
        assert (b <> b3).
        { intros ?; subst b3.
          exploit NOTDEF3; eauto. }
        exploit Mem.perm_set_2'; eauto. eapply find_def_perm2; eauto.
      + intros. erewrite <- Mem.set_preserves_comp; eauto. eapply find_var_comp1; eauto.
      + intros. clear m1_m3. eapply meminj_injective; eauto.
  Qed.

End Lemmas.

Ltac eexists_and_split :=
  fun k =>
    match goal with
    | m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
        rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
        exists j; eexists; eexists; split; [| split; [| split; [| split; [| split; [| split]]]]]; eauto;
        k j rs1 rs3 rs1_rs3 m1 m3 m1_m3
    end.

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
              destruct ofs eqn:?; subst; simpl in *

          | _: context [low_half] |- _ =>
              unfold low_half in *; simpl in *


          | H: Mem.alloc ?m1 ?cp ?lo1 ?hi1 = (?m1', ?b1),
              m1_m3: mem_rel _ _ _ ?j__δ ?δ ?m1 ?m3,
                m2_m3: mem_rel _ _ _ ?j__oppδ (opposite ?δ) ?m2 ?m3,
                  inj_pres : meminj_preserves_globals _ ?δ _ _ ?j__δ,
                    rs1_rs3: regset_rel _ _ _,
                      not_bottom: ?cp <> bottom,
                        not_top: ?cp <> top,
                          st_rel: stack_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
              let j__δ' := fresh "j__δ" in
              let m3' := fresh "m3" in
              let b3 := fresh "b3" in
              let alloc3 := fresh "alloc3" in
              let inj_pres' := fresh "inj_pres" in
              let m1'_m3' := fresh "m1'_m3'" in
              let m2_m3' := fresh "m2_m3'" in
              let proj := fresh "proj" in
              let incr := fresh "incr" in
              let st_rel' := fresh "st_rel" in
              eapply (alloc_preserves_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        not_bottom not_top
                        inj_pres m1_m3 m2_m3 rs1_rs3 st_rel) in H as
                  [j__δ' [m3' [b3 [alloc3 [inj_pres' [m1'_m3' [m2_m3' [? [proj [incr st_rel']]]]]]]]]];
              clear m1_m3 rs1_rs3 m2_m3 inj_pres st_rel
          | H: ?s ?cp = ?δ -> _,
              side_cp: ?s ?cp = ?δ |- _ =>
              specialize (H side_cp)
          | H: ?x = ?x -> _ |- _ =>
              specialize (H eq_refl)

          | H: Mem.store ?ch ?m1 ?b1 ?ofs (?rs1 ?r) ?cp = Some ?m1',
              m1_m3: mem_rel _ _ _ ?j__δ ?δ ?m1 ?m3,
                m2_m3: mem_rel _ _ _ ?j__oppδ (opposite ?δ) ?m2 ?m3,
                  ptr_inj: ?j__δ ?b1 = Some (?b3, 0),
                    inj_pres1 : meminj_preserves_globals _ ?δ _ _ ?j__δ,
                      inj_pres2 : meminj_preserves_globals _ (opposite ?δ) _ _ ?j__oppδ,
                        rs1_rs3: regset_rel ?j__δ ?rs1 ?rs3,
                          st_rel: stack_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _,
                            not_bottom: ?cp <> bottom,
                              not_top: ?cp <> top |- _ =>
              let m3' := fresh "m3" in
              eapply (store_preserves_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        not_bottom not_top
                        inj_pres1 inj_pres2 ptr_inj m1_m3 m2_m3 (rs1_rs3 r) st_rel) in H as
                  [m3' [? [? [? ?]]]];
              clear m1_m3 m2_m3

          | H: Mem.free ?m1 ?b1 ?lo ?hi ?cp = Some ?m1',
              m1_m3: mem_rel _ _ _ ?j__δ ?δ ?m1 ?m3,
                m2_m3: mem_rel _ _ _ ?j__oppδ (opposite ?δ) ?m2 ?m3,
                  inj_pres1 : meminj_preserves_globals _ ?δ _ _ ?j__δ,
                    inj_pres2 : meminj_preserves_globals _ (opposite ?δ) _ _ ?j__oppδ,
                      st_rel: stack_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _,
                        ptr_inj: ?j__δ ?b1 = Some (?b3, 0) |- _ =>
              let m3' := fresh "m3" in
              eapply (free_preserves_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        inj_pres1 inj_pres2 ptr_inj m1_m3 m2_m3 st_rel) in H as
                  [m3' [? [? ?]]];
              clear m1_m3

          | H: Mem.load ?ch ?m1 ?b1 ?ofs ?cp = Some ?v1,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                ptr_inj: ?j ?b1 = Some (?b3, 0) |- _ =>
              let v3 := fresh "v3" in
              let load3 := fresh "load3" in
              destruct (Mem.load_inject _ _ _ _ _ _ _ _ _ _ (partial_mem_inject _ _ _ _ _ _ _ m1_m3) H ptr_inj) as
                [v3 [load3 ?]];
              rewrite Z.add_0_r in load3;
              clear H

          | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              eapply cmpu_bool_preserved with (m3 := m3) in H; eauto using rs1_rs3;
              try rewrite H in *;
              try congruence

          | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (Vint ?x) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              eapply cmpu_bool_preserved with (m3 := m3) (v1' := Vint x) in H; eauto using rs1_rs3;
              try rewrite H in *;
              try congruence

          | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (Vint ?x) = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              eapply cmpu_bool_preserved with (m3 := m3) (v2' := Vint x) in H; eauto using rs1_rs3;
              try rewrite H in *;
              try congruence

          | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (Vint ?x) (Vint ?y) = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              eapply cmpu_bool_preserved with (m3 := m3) (v1' := Vint x) (v2' := Vint y) in H; eauto using rs1_rs3;
              try rewrite H in *;
              try congruence

          | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              eapply cmplu_bool_preserved with (m3 := m3) in H; eauto using rs1_rs3;
              try rewrite H in *;
              try congruence

          | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (Vlong ?x) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              eapply cmplu_bool_preserved with (m3 := m3) (v1' := Vlong x) in H; eauto using rs1_rs3;
              try rewrite H in *;
              try congruence

          | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (Vlong ?x) = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              eapply cmplu_bool_preserved with (m3 := m3) (v2' := Vlong x) in H; eauto using rs1_rs3;
              try rewrite H in *;
              try congruence

          | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (Vlong ?x) (Vlong ?y) = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              eapply cmplu_bool_preserved with (m3 := m3) (v1' := Vlong x) (v2' := Vlong y) in H; eauto using rs1_rs3;
              try rewrite H in *;
              try congruence

          | H: Val.cmp_bool ?op (?rs1 ?r) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              eapply Val.cmp_bool_inject in H; eauto using rs1_rs3;
              try rewrite H in *;
              try congruence

          | d: Z |- _ =>
              match goal with
              | H: ?j _ = Some (_, d) ,
                  m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3 |- _ =>
                  let G := fresh "G" in
                  pose proof (delta_zero _ _ _ _ _ _ _ m1_m3 _ _ _ H) as G;
                  subst d
              end


          | |- context [Ptrofs.repr 0] => replace (Ptrofs.repr 0) with Ptrofs.zero by reflexivity; auto
          | H: context [Ptrofs.repr 0] |- _ => replace (Ptrofs.repr 0) with Ptrofs.zero in H by reflexivity; auto
          | |- context [Ptrofs.add _ Ptrofs.zero] => rewrite Ptrofs.add_zero; auto
          | H: context [Ptrofs.add _ Ptrofs.zero] |- _ => rewrite Ptrofs.add_zero in H; simpl in *; try congruence
          | |- context [Ptrofs.sub _ Ptrofs.zero] => rewrite Ptrofs.sub_zero_l; auto
          | H: context [Ptrofs.sub _ Ptrofs.zero] |- _ => rewrite Ptrofs.sub_zero_l in H; simpl in *; try congruence

          (* hypothesis manipulation *)
          | rs1_rs3: regset_rel ?j ?rs1 ?rs3,
              _: context [match ?rs1 ?i with | _ => _ end] |- _ =>
              let H := fresh "rs1_rs3" in
              assert (H := rs1_rs3 i);
              destruct (rs1 i); inv H; try congruence; simpl in *; eauto

          | rs1_rs3: regset_rel ?j ?rs1 ?rs3,
              _: context [Val.offset_ptr (?rs1 ?i) _] |- _ =>
              let H := fresh "rs1_rs3" in
              assert (H := rs1_rs3 i);
              destruct (rs1 i); inv H; try congruence; simpl in *; eauto

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
          | H: Int.lt ?x ?x = true |- _ => rewrite lt_xx_false in H
          | H: Int64.lt ?x ?x = true |- _ => rewrite lt64_xx_false in H
          | H: Int.ltu ?x ?x = true |- _ => rewrite ltu_xx_false in H
          | H: Int64.ltu ?x ?x = true |- _ => rewrite ltu64_xx_false in H
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
              setoid_rewrite H; simpl
          | H: ?x = _ |- context [match ?x with | _ => _ end] =>
              setoid_rewrite H; simpl
          | |- context [(if ?x then _ else _) = Next _ _] =>
              let eq := fresh "eq" in destruct x eqn:eq; simpl in *
          | |- context [(match ?x with | _ => _ end) = Next _ _] =>
              let eq := fresh "eq" in destruct x eqn:eq; simpl in *

          end);
  simpl.

Ltac solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3:=
  repeat (Simpl;
          match goal with
          | |- regset_rel j (nextinstr _) (nextinstr _) => unfold nextinstr
          | |- regset_rel j (_ # _ <- _) (_ # _ <- _) => eapply regset_rel_inject
          | |- regset_rel j rs1 rs3 => assumption

          | |- stack_rel _ _ _ _ _ _ _ _ _ => eauto using inject_incr_stack_rel1, inject_incr_stack_rel2, inject_incr_refl

          | _: ?x |- ?x => assumption

          | d: Z |- _ =>
              match goal with
              | H: j _ = Some (_, d) |- _ =>
                  let G := fresh "G" in
                  pose proof (delta_zero _ _ _ _ _ _ _ m1_m3 _ _ _ H) as G;
                  subst d
              end


          | |- Ptrofs.add (Ptrofs.add ?ofs1 ?delta) ?imm = Ptrofs.add (Ptrofs.add ?ofs1 ?imm) ?delta =>
              now rewrite (Ptrofs.add_assoc ofs1 delta imm), (Ptrofs.add_commut delta imm), <- Ptrofs.add_assoc

          | |- context [_ ### ?rs] =>
              let i := fresh "i" in destruct rs as [| i]; simpl in *
          | |- context [_ ## ?rs] =>
              let i := fresh "i" in destruct rs as [| i]; simpl in *

          | |- context [Ptrofs.sub (Ptrofs.add _ _) _] => rewrite Ptrofs.sub_add_l; simpl; auto
          | |- context [Ptrofs.repr 0] => replace (Ptrofs.repr 0) with Ptrofs.zero by reflexivity; auto
          | |- context [Ptrofs.add _ Ptrofs.zero] => rewrite Ptrofs.add_zero; auto
          | |- context [Ptrofs.sub _ Ptrofs.zero] => rewrite Ptrofs.sub_zero_l; auto



          | |- Val.inject _ _ _ => eauto using Ptrofs.add_zero with solve_inject
          end).


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

  Hypothesis no_bottom1: forall b f,
      Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
      comp_of f <> bottom.
  Hypothesis no_top1: forall b f,
      Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
      comp_of f <> top.
  Hypothesis no_bottom2: forall b f,
      Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
      comp_of f <> bottom.
  Hypothesis no_top2: forall b f,
      Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
      comp_of f <> top.
  Hypothesis no_bottom3: forall b f,
      Genv.find_def ge3 b = Some (Gfun (Internal f)) ->
      comp_of f <> bottom.
  Hypothesis no_top3: forall b f,
      Genv.find_def ge3 b = Some (Gfun (Internal f)) ->
      comp_of f <> top.


  Hypothesis no_bottom1': forall b v,
      Genv.find_def ge1 b = Some (Gvar v) ->
      comp_of v <> bottom.
  Hypothesis no_top1': forall b v,
      Genv.find_def ge1 b = Some (Gvar v) ->
      comp_of v <> top.
  Hypothesis no_bottom2': forall b v,
      Genv.find_def ge2 b = Some (Gvar v) ->
      comp_of v <> bottom.
  Hypothesis no_top2': forall b v,
      Genv.find_def ge2 b = Some (Gvar v) ->
      comp_of v <> top.
  Hypothesis no_bottom3': forall b v,
      Genv.find_def ge3 b = Some (Gvar v) ->
      comp_of v <> bottom.
  Hypothesis no_top3': forall b v,
      Genv.find_def ge3 b = Some (Gvar v) ->
      comp_of v <> top.

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
        rewrite (match_prog_pol _ _ _ _ match_W1_W3), <- same_comp. auto.
  Qed.

  Lemma call_arguments_preserved:
    forall j__δ m1 m3 rs1 rs3 sp1 sp3,
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Val.inject j__δ sp1 sp3 ->
      forall sig args, call_arguments rs1 sp1 m1 sig args ->
                  exists args', Val.inject_list j__δ args args'
                           /\ call_arguments rs3 sp3 m3 sig args'.
  Proof.
    intros * m1_m3 rs1_rs3 sp1_sp3 sig args H.
    unfold call_arguments in H.
    unfold call_arguments.
    induction H.
    - exists nil. split; auto. constructor.
    - assert (exists b1', Val.inject j__δ b1 b1' /\ call_arg_pair rs3 sp3 m3 a1 b1').
      { inv H.
        - inv H1.
          + specialize (rs1_rs3 (preg_of r)).
            exists (rs3 (preg_of r)). split; eauto. constructor; constructor.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto.
            intros [b1' [? ?]].
            exists b1'; split. eauto. constructor. econstructor; eauto.
        - inv H1; inv H2.
          + pose proof (rs1_rs3 (preg_of r)).
            pose proof (rs1_rs3 (preg_of r0)).
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; constructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto. clear H1.
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto.
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
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      Val.inject j__δ v v' ->
      Val.inject_list j__δ args args' ->
      (Genv.type_of_call cp cp' = Genv.CrossCompartmentCall -> Forall not_ptr args) ->
      call_trace ge1 cp cp' v args (sig_args sig) t ->
      call_trace ge3 cp cp' v' args' (sig_args sig) t.
  Proof.
    intros j__δ cp cp' v v' args args' sig t inj_pres delta_zero inj_v inj_args NPTR EV.
    inv EV.
    - constructor; auto.
    - specialize (NPTR H).
      inv inj_v; eauto.
      econstructor; eauto. apply Genv.find_invert_symbol.
      eapply symbols_inject1; eauto. eapply Genv.invert_find_symbol; eauto.
      remember (sig_args sig) as tys.
      clear -inj_args NPTR H2.
      revert args args' tys vl inj_args NPTR H2.
      induction args;intros args' tys vl inj_args NPTR Hmatch.
      + inv inj_args; inv Hmatch; constructor.
      + inv inj_args; inv Hmatch; inv NPTR.
        constructor; eauto.
        inv H1; inv H5; try contradiction; econstructor; eauto.
  Qed.

  (* State inversion *)
  Lemma strong_equiv_state_internal_inv:
    forall j__δ st1 rs1 m1 s3 b ofs f i cp,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      (* agrees_with j__δ (init_meminj W1 W3) -> *)
      strong_equivalence s cp_main ge1 ge3 j__δ δ (State st1 rs1 m1 cp) s3 ->
      rs1 PC = Vptr b ofs ->
      Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exists st3 rs3 m3 b' f',
        s3 = State st3 rs3 m3 cp /\
          rs3 PC = Vptr b' ofs /\
          Genv.find_def ge3 b' = Some (Gfun (Internal f')) /\
          (match_fundef (Internal f) (Internal f') /\
             (forall id : ident, Genv.find_symbol ge1 id = Some b -> kept_prog s W1 δ id = true -> f = f')) /\
          mem_rel s ge1 ge3 j__δ δ m1 m3 /\
          regset_rel j__δ rs1 rs3 /\
          s (comp_of f) = δ.
  Proof.
    intros * inj_pres equiv eq_pc find_fun find_ins (* inj_b_b' *).
    assert (exists b', j__δ b = Some (b', 0)) as [b' inj_b_b'].
    { inv equiv.
      specialize (H4 PC). inv H4; try congruence.
      exploit delta_zero; eauto; intros ->; rewrite Ptrofs.add_zero in *.
      exists b2. congruence. }
    exploit find_def_preserved; eauto.
    (* exploit (agrees_with_init_meminj_find_def_preserved s W1 W3); eauto. *)
    intros [fd' [find_fun' [match_f_f' left_implies_eq]]].
    assert (exists f', fd' = (Gfun (Internal f'))) as [f' ?] by
        now inversion match_f_f' as [? ? H | ? ? H]; inv H; eauto.
    subst fd'.
    inv match_f_f'; inv equiv.
    eexists; eexists; eexists; eexists; eexists; split; eauto.
    pose proof (H5 PC) as inj.
    rewrite eq_pc in *; simpl in *. inv inj.
    assert (b' = b2) by congruence; subst b2;
      assert (delta = 0) by congruence; subst delta.
    rewrite Ptrofs.add_zero. split; auto.
    rewrite find_fun'.
    repeat (split; auto).
    - intros; exploit left_implies_eq; eauto. congruence.
    - inv COMP1.
      { rewrite eq_pc in H9; simpl in H9.
        unfold Genv.find_comp_of_block in H9; rewrite find_fun in H9; simpl in H9.
        congruence. }
      (* { rewrite eq_pc in H9; simpl in H9. *)
      (*   unfold Genv.find_comp_of_block in H9; rewrite find_fun in H9; simpl in H9. *)
      (*   exploit no_bottom1; eauto. contradiction. } *)
  Qed.

  Lemma strong_equiv_state_external_inv:
    forall j__δ st1 rs1 m1 s3 b ofs f cp,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      strong_equivalence s cp_main ge1 ge3 j__δ δ (State st1 rs1 m1 cp) s3 ->
      rs1 PC = Vptr b ofs ->
      Genv.find_def ge1 b = Some (Gfun (External f)) ->
      exists st3 rs3 m3 b',
        s3 = State st3 rs3 m3 cp /\
          rs3 PC = Vptr b' ofs /\
          Genv.find_def ge3 b' = Some (Gfun (External f)) /\
          mem_rel s ge1 ge3 j__δ δ m1 m3 /\
          regset_rel j__δ rs1 rs3.
  Proof.
    intros * inj_pres equiv eq_pc find_fun (* inj_b_b' *).
    assert (exists b', j__δ b = Some (b', 0)) as [b' inj_b_b'].
    { inv equiv.
      specialize (H4 PC). inv H4; try congruence.
      exploit delta_zero; eauto; intros ->; rewrite Ptrofs.add_zero in *.
      exists b2. congruence. }
    exploit find_def_preserved; eauto.
    intros [fd' [find_fun' [match_f_f' left_implies_eq]]].
    inv equiv; inv match_f_f'. inv H0.
    eexists; eexists; eexists; eexists; split; eauto.
    pose proof (H4 PC) as inj.
    rewrite eq_pc in *; simpl in *. inv inj.
    assert (b' = b2) by congruence; subst b2;
      assert (delta = 0) by congruence; subst delta.
    rewrite Ptrofs.add_zero. split; auto.
  Qed.

  Lemma strong_equiv_returnstate_inv:
    forall j__δ st1 rs1 m1 s3 rec_cp,
      strong_equivalence s cp_main ge1 ge3 j__δ δ (ReturnState st1 rs1 m1 rec_cp) s3 ->
      exists st3 rs3 m3,
        s3 = ReturnState st3 rs3 m3 rec_cp /\
          mem_rel s ge1 ge3 j__δ δ m1 m3 /\
          regset_rel j__δ rs1 rs3.
  Proof.
    intros * equiv.
    inv equiv.
    eexists; eexists; eexists; split; eauto.
  Qed.

  (* Builtins and external calls arguments *)
  Lemma eval_builtin_arg_inject:
    forall cp (rs: regset) m j__δ rs' m' a v
      (eval: eval_builtin_arg ge1 cp rs (rs X2) m a v)
      (sideof: s cp = δ)
      (no_top: cp <> top)
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (m_m': mem_rel s ge1 ge3 j__δ δ m m')
      (delta_zero: mem_delta_zero j__δ),
      regset_rel j__δ rs rs' ->
      Mem.inject j__δ m m' ->
      exists v',
        eval_builtin_arg ge3 cp rs' (rs' X2) m' a v'
        /\ Val.inject j__δ v v'.
  Proof.
    induction 1; intros SIDE NOTOP MINJ MR DZ (* SP  *)RS MI.
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
    - assert (Val.inject j__δ (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge3 id ofs)).
      { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
        destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; auto.
        exploit symbols_inject2; eauto.
        { revert H. unfold kept_genv, Genv.symbol_address.
          rewrite FS; simpl.
          intros H. eapply Mem.load_valid_access in H.
          destruct H as [PERM [H _]]. simpl in H, PERM.
          specialize (PERM (Ptrofs.unsigned ofs)).
          fold (Genv.find_def ge1 b).
          exploit Genv.find_symbol_find_def_inversion; eauto. intros [g G]. rewrite G.
          destruct g; auto.
          assert (has_comp_globvar v0 = cp) as ->.
          { exploit find_var_comp1; eauto. intros ?.
            exploit perm_compartment1; eauto.
            eapply Mem.perm_max. eapply Mem.perm_implies. eapply PERM. destruct chunk; simpl; lia.
            constructor.
            intros [? R]; rewrite R in *.
            assert (cp = Comp x).
            { inv H; try now contradiction. auto. }
            subst cp. simpl in *; auto. }
          now destruct side_eq. }
        intros (b' & A & B). rewrite A.
        econstructor; eauto. rewrite Ptrofs.add_zero; auto. }
      exploit Mem.loadv_inject; eauto. intros (v' & A & B). exists v'; split; auto with barg.
    - assert (KEPT: kept_genv s ge1 δ id = true).
      { revert H. unfold kept_genv, Genv.allowed_addrof, Genv.allowed_addrof_b.
        destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; auto.
        fold (Genv.find_def ge1 b).
        destruct Genv.find_def as [[] |] eqn:FIND; try discriminate; auto.
        simpl. intros H.
        assert (has_comp_globvar v = cp) as ->.
        { clear -FIND H no_bottom1' NOTOP.
          destruct flowsto_dec as [G |]; try discriminate.
          clear H. inv G; auto.
          exploit no_bottom1'; eauto; contradiction.
          congruence. }
        now destruct side_eq.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence.
      }
      econstructor; split; eauto with barg.
      econstructor; eauto.
      { revert H.
        unfold Genv.allowed_addrof, Genv.allowed_addrof_b. clear match_W2_W3.
        destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; try discriminate.
        exploit symbols_inject2; eauto.
        intros (b' & TFS & INJ). rewrite TFS.
        destruct (Genv.find_def ge1 b) eqn:FIND; try discriminate.
        exploit defs_inject; eauto. intros [g' [-> [_ [MATCH _]]]].
        inv MATCH; auto. inv H; auto. clear TFS.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence.
      }
      unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
      destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; auto.
      exploit symbols_inject2; eauto.
      intros (b' & A & B). rewrite A.
      econstructor; eauto. now rewrite Ptrofs.add_zero.
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
    forall cp (rs: regset) m j__δ rs' m' al vl
      (eval: eval_builtin_args ge1 cp rs (rs X2) m al vl)
      (sideof: s cp = δ)
      (no_top: cp <> top)
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (m_m': mem_rel s ge1 ge3 j__δ δ m m')
      (delta_zero: mem_delta_zero j__δ),
      regset_rel j__δ rs rs' ->
      Mem.inject j__δ m m' ->
      exists vl',
        eval_builtin_args ge3 cp rs' (rs' X2) m' al vl'
        /\ Val.inject_list j__δ vl vl'.
  Proof.
    induction 1; intros.
    - exists (@nil val); split; constructor.
    - exploit eval_builtin_arg_inject; eauto using in_or_app. intros (v1' & A & B).
      destruct IHeval as (vl' & C & D); eauto using in_or_app.
      exists (v1' :: vl'); split; constructor; auto.
  Qed.

  Lemma extcall_arguments_preserved:
    forall j__δ δ m1 m3 rs1 rs3 sp1 sp3,
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Val.inject j__δ sp1 sp3 ->
      forall sig args, extcall_arguments rs1 sp1 m1 sig args ->
                  exists args', Val.inject_list j__δ args args'
                           /\ extcall_arguments rs3 sp3 m3 sig args'.
  Proof.
    intros * m1_m3 rs1_rs3 sp1_sp3 sig args H.
    unfold extcall_arguments in H.
    unfold extcall_arguments.
    induction H.
    - exists nil. split; auto. constructor.
    - assert (exists b1', Val.inject j__δ b1 b1' /\ extcall_arg_pair rs3 sp3 m3 a1 b1').
      { inv H.
        - inv H1.
          + specialize (rs1_rs3 (preg_of r)).
            exists (rs3 (preg_of r)). split; eauto. constructor; constructor.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto.
            intros [b1' [? ?]].
            exists b1'; split. eauto. constructor. econstructor; eauto.
        - inv H1; inv H2.
          + pose proof (rs1_rs3 (preg_of r)).
            pose proof (rs1_rs3 (preg_of r0)).
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; constructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto. clear H1.
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject; eauto.
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

  Lemma exec_instr_preserved:
    forall j__δ j__oppδ f i rs1 rs1' rs3 m1 m1' m2 m3 st1 st2 st3
      (not_bottom: has_comp_function f <> bottom)
      (not_top: has_comp_function f <> top),
      s |= has_comp_function f ∈ δ ->
      meminj_preserves_globals s δ W1 W3 j__δ ->
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      exec_instr ge1 f i rs1 m1 (has_comp_function f) = Next rs1' m1' ->
      exists j__δ' rs3' m3',
        exec_instr ge3 f i rs3 m3 (has_comp_function f) = Next rs3' m3' /\
          meminj_preserves_globals s δ W1 W3 j__δ' /\
          mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
          mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
          regset_rel j__δ' rs1' rs3' /\
          stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ m1' m2 m3' st1 st2 st3 /\
          inject_incr j__δ j__δ'.
  Proof.
    intros until st3.
    intros ? ? side_cp inj_pres1 inj_pres2 m1_m3 m2_m3 rs1_rs3 st1_st3 exec.

    Local Opaque Val.cmpu_bool Val.cmplu_bool.
    Local Opaque opposite.


    destruct i; inv exec; simpl in *;
      try now (simpl_before_exists; (eexists_and_split
                                       ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                                               (simpl; try reflexivity; try eassumption;
                                                solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity)))).
    - destruct (Genv.allowed_addrof_b) eqn:EQ; try discriminate.
      assert (KEPT: kept_genv s ge1 δ symb = true).
      { revert EQ. unfold kept_genv, Genv.allowed_addrof_b.
        destruct (Genv.find_symbol) eqn:FS; try discriminate.
        fold (Genv.find_def ge1 b).
        destruct Genv.find_def as [[] |] eqn:FIND; try discriminate; auto.
        simpl. intros H.
        assert (has_comp_globvar v = has_comp_function f) as ->.
        { clear -FIND H no_bottom1' not_top.
          destruct flowsto_dec as [G |]; try discriminate.
          clear H. inv G; auto.
          exploit no_bottom1'; eauto; contradiction.
          congruence. }
        now destruct side_eq.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence.
      }
      assert (Genv.allowed_addrof_b ge3 (has_comp_function f) symb = true) as ->.
      { revert EQ.
        unfold Genv.allowed_addrof_b. clear match_W2_W3 inj_pres2.
        destruct (Genv.find_symbol ge1 symb) as [b|] eqn:FS; try discriminate.
        exploit symbols_inject2; eauto.
        intros (b' & TFS & INJ). rewrite TFS.
        destruct (Genv.find_def ge1 b) eqn:FIND; try discriminate.
        exploit defs_inject; eauto. intros [g' [-> [_ [MATCH _]]]].
        inv MATCH; auto. inv H; auto.
        clear TFS.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence.
      }
      inv H0.
      (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      exploit (symbol_address_inject s (s (has_comp_function f)) W1 W3 j__δ symb Ptrofs.zero);
        eauto using delta_zero.
    - destruct (Genv.allowed_addrof_b) eqn:EQ; try discriminate.
      assert (KEPT: kept_genv s ge1 δ symb = true).
      { revert EQ. unfold kept_genv, Genv.allowed_addrof_b.
        destruct (Genv.find_symbol) eqn:FS; try discriminate.
        fold (Genv.find_def ge1 b).
        destruct Genv.find_def as [[] |] eqn:FIND; try discriminate; auto.
        simpl. intros H.
        assert (has_comp_globvar v = has_comp_function f) as ->.
        { clear -FIND H no_bottom1' not_top.
          destruct flowsto_dec as [G |]; try discriminate.
          clear H. inv G; auto.
          exploit no_bottom1'; eauto; contradiction.
          congruence. }
        now destruct side_eq.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence.
      }
      assert (Genv.allowed_addrof_b ge3 (has_comp_function f) symb = true) as ->.
      { revert EQ.
        unfold Genv.allowed_addrof_b. clear match_W2_W3 inj_pres2.
        destruct (Genv.find_symbol ge1 symb) as [b|] eqn:FS; try discriminate.
        exploit symbols_inject2; eauto.
        intros (b' & TFS & INJ). rewrite TFS.
        destruct (Genv.find_def ge1 b) eqn:FIND; try discriminate.
        exploit defs_inject; eauto. intros [g' [-> [_ [MATCH _]]]].
        inv MATCH; auto. inv H; auto.
        clear TFS.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence.
      }
      inv H0.
      (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      exploit (symbol_address_inject s (s (has_comp_function f)) W1 W3 j__δ symb Ptrofs.zero);
        eauto using delta_zero.
    - destruct (Genv.allowed_addrof_b) eqn:EQ; try discriminate.
      assert (KEPT: kept_genv s ge1 δ id = true).
      { revert EQ. unfold kept_genv, Genv.allowed_addrof_b.
        destruct (Genv.find_symbol) eqn:FS; try discriminate.
        fold (Genv.find_def ge1 b).
        destruct Genv.find_def as [[] |] eqn:FIND; try discriminate; auto.
        simpl. intros H.
        assert (has_comp_globvar v = has_comp_function f) as ->.
        { clear -FIND H no_bottom1' not_top.
          destruct flowsto_dec as [G |]; try discriminate.
          clear H. inv G; auto.
          exploit no_bottom1'; eauto; contradiction.
          congruence. }
        now destruct side_eq.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence.
      }
      assert (Genv.allowed_addrof_b ge3 (has_comp_function f) id = true) as ->.
      { revert EQ.
        unfold Genv.allowed_addrof_b. clear match_W2_W3 inj_pres2.
        destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; try discriminate.
        exploit symbols_inject2; eauto.
        intros (b' & TFS & INJ). rewrite TFS.
        destruct (Genv.find_def ge1 b) eqn:FIND; try discriminate.
        exploit defs_inject; eauto. intros [g' [-> [_ [MATCH _]]]].
        inv MATCH; auto. inv H; auto.
        clear TFS.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence. }
      inv H0.
      (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      exploit (symbol_address_inject s (s (has_comp_function f)) W1 W3 j__δ id ofs);
        eauto using delta_zero.
    - replace (high_half ge1 id ofs) with (Genv.symbol_address ge1 id ofs) by reflexivity.
      replace (high_half ge3 id ofs) with (Genv.symbol_address ge3 id ofs) by reflexivity.
      destruct (Genv.allowed_addrof_b) eqn:EQ; try discriminate.
      assert (KEPT: kept_genv s ge1 δ id = true).
      { revert EQ. unfold kept_genv, Genv.allowed_addrof_b.
        destruct (Genv.find_symbol) eqn:FS; try discriminate.
        fold (Genv.find_def ge1 b).
        destruct Genv.find_def as [[] |] eqn:FIND; try discriminate; auto.
        simpl. intros H.
        assert (has_comp_globvar v = has_comp_function f) as ->.
        { clear -FIND H no_bottom1' not_top.
          destruct flowsto_dec as [G |]; try discriminate.
          clear H. inv G; auto.
          exploit no_bottom1'; eauto; contradiction.
          congruence. }
        now destruct side_eq.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence.
      }
      assert (Genv.allowed_addrof_b ge3 (has_comp_function f) id = true) as ->.
      { revert EQ.
        unfold Genv.allowed_addrof_b. clear match_W2_W3 inj_pres2.
        destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; try discriminate.
        exploit symbols_inject2; eauto.
        intros (b' & TFS & INJ). rewrite TFS.
        destruct (Genv.find_def ge1 b) eqn:FIND; try discriminate.
        exploit defs_inject; eauto. intros [g' [-> [_ [MATCH _]]]].
        inv MATCH; auto. inv H; auto.
        clear TFS.
        exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?]. congruence.
      }
      inv H0.
      (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      exploit (symbol_address_inject s (s (has_comp_function f)) W1 W3 j__δ id ofs);
        eauto using delta_zero.
      Unshelve.
      all: try assumption.
      all: eapply match_prog_unique; eauto.
  Qed.

  Lemma exec_instr_preserves_weak:
    forall j__δ j__oppδ f i rs2 rs2' m1 m2 m2' m3 st1 st2 st3
      (not_bottom: has_comp_function f <> bottom)
      (not_top: has_comp_function f <> top),
      s (has_comp_function f) = δ ->
      exec_instr ge2 f i rs2 m2 (has_comp_function f) = Next rs2' m2' ->
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->
      exists j__oppδ',
        meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ' /\
          mem_rel s ge2 ge3 j__oppδ' (opposite δ) m2' m3 /\
          stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ' m1 m2' m3 st1 st2 st3.
  Proof.
    intros j__δ j__oppδ f i rs2 rs2' m1 m2 m2' m3 st1 st2 st3
      ? ? side_f exec (* agr addr *) inj_pres m2_m3 st_rel.

    destruct i; inv exec; simpl in *;
      try (now simpl_before_exists; eauto);
      try (now exploit exec_store_preserves_weak; eauto; intros []).
    - eapply exec_store_preserves_weak in H0 as [A B]; eauto.
      eapply stack_rel_comm in B; eauto. eexists; split; eauto.
      split; eauto. destruct s; eauto.
      eapply stack_rel_comm; eauto.
    - eapply exec_store_preserves_weak in H0 as [A B]; eauto.
      eapply stack_rel_comm in B; eauto. eexists; split; eauto.
      split; eauto. destruct s; eauto.
      eapply stack_rel_comm; eauto.
    - eapply exec_store_preserves_weak in H0 as [A B]; eauto.
      eapply stack_rel_comm in B; eauto. eexists; split; eauto.
      split; eauto. destruct s; eauto.
      eapply stack_rel_comm; eauto.
    - eapply exec_store_preserves_weak in H0 as [A B]; eauto.
      eapply stack_rel_comm in B; eauto. eexists; split; eauto.
      split; eauto. destruct s; eauto.
      eapply stack_rel_comm; eauto.
    - eapply exec_store_preserves_weak in H0 as [A B]; eauto.
      eapply stack_rel_comm in B; eauto. eexists; split; eauto.
      split; eauto. destruct s; eauto.
      eapply stack_rel_comm; eauto.
    - eapply exec_store_preserves_weak in H0 as [A B]; eauto.
      eapply stack_rel_comm in B; eauto. eexists; split; eauto.
      split; eauto. destruct s; eauto.
      eapply stack_rel_comm; eauto.
    - eapply exec_store_preserves_weak in H0 as [A B]; eauto.
      eapply stack_rel_comm in B; eauto. eexists; split; eauto.
      split; eauto. destruct s; eauto.
      eapply stack_rel_comm; eauto.
    - eapply exec_store_preserves_weak in H0 as [A B]; eauto.
      eapply stack_rel_comm in B; eauto. eexists; split; eauto.
      split; eauto. destruct s; eauto.
      eapply stack_rel_comm; eauto.
    - eapply exec_store_preserves_weak in H0 as [A B]; eauto.
      eapply stack_rel_comm in B; eauto. eexists; split; eauto.
      split; eauto. destruct s; eauto.
      eapply stack_rel_comm; eauto.
    - simpl_before_exists.
      exploit alloc_preserves_weak; eauto. eapply stack_rel_comm; eauto.
      intros [j' [? [? [A B]]]].
      exploit store_preserves_weak; eauto. intros [C D].
      exists j'; split; [| split]; eauto using inject_incr_stack_rel2.
      eapply stack_rel_comm in B, D.
      replace (opposite (opposite (s (has_comp_function f)))) with (s (has_comp_function f)) in *; eauto.
      now destruct s.
    - simpl_before_exists.
      exists j__oppδ; split; [| split]; auto.
      { constructor.
        + intros b'. apply same_dom in m2_m3.
          specialize (m2_m3 b').
          simpl in *. erewrite Mem.free_result with (m2 := m2'); eauto.  unfold Mem.unchecked_free in *.
          destruct (zle sz 0); now subst.
        + eapply Mem.free_left_inject; eauto using partial_mem_inject.
        + eapply delta_zero; eauto.
        + intros. erewrite <- Mem.free_preserves_comp; eauto.
          exploit perm_compartment1; eauto.
          eapply Mem.perm_free_3; eauto.
        + eapply perm_compartment2; eauto.
        + erewrite Mem.nextblock_free; eauto using ple_nextblock1.
        + eapply ple_nextblock2; eauto.
        + intros. eapply Mem.valid_block_free_1; eauto using find_def_valid1.
        + intros. eapply find_def_valid2; eauto.
        + intros. intros n.
          eapply find_def_perm1; eauto.
          eapply Mem.perm_free_3; eauto.
        + intros. eapply find_def_perm2; eauto.
        + intros. erewrite <- Mem.free_preserves_comp; eauto using find_var_comp1.
        + eapply meminj_injective; eauto.
      }
      { induction st_rel.
        constructor.
        constructor; eauto.
        inv H.
        - econstructor; eauto.
          + unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; destruct sp2; simpl in *; try congruence.
            { intros ?? A; inv A. intros ??.
              eapply Mem.perm_free_1; eauto.
              destruct (Pos.eqb_spec b4 b); auto; subst; right.
              destruct (zlt ofs0 0); auto; right.
              destruct (zle sz ofs0); auto. exfalso.
              (* clear free3. *)
              exploit Mem.free_range_perm; eauto. instantiate (1 := ofs0); lia. intros ?.
              eapply PERM2. eapply Mem.perm_max, Mem.perm_implies; eauto. constructor.
              eapply X; eauto. }
            intros ? G''.
            eapply Mem.load_free_2 in G'' as G'''; eauto.
          (* specialize (STACK_CONTENT2 _ G''') as [? ?]. split; auto. *)
          + unfold at_most_readable in *. destruct sp2; try auto.
            split. eapply Mem.valid_block_free_1; eauto. eapply PERM2.
            intros ? N. eapply PERM2.
            eapply Mem.perm_free_3; eauto.
          + unfold nonempty in *.
            destruct sp2; try contradiction.
            eapply Mem.free_range_perm in eq1 as ?.
            destruct (eq_block b b0). subst.
            -- destruct (zlt 0 0); auto.
               eapply Mem.perm_free_1; eauto.
               destruct (zle sz 0); auto.
               eapply Mem.perm_free_1; eauto.
               (* lia. *) exfalso.
               eapply PERM2.
               apply Mem.range_perm_max in H.
               eapply Mem.perm_implies.
               eapply H. instantiate (1 := 0). lia. constructor.
            -- eapply Mem.perm_free_1; eauto.
          + split. eapply Mem.valid_block_free_1; eauto. eapply EMPTY2.
            intros ? N. eapply EMPTY2.
            eapply Mem.perm_free_3; eauto.
        - eapply stackframe_related_opp_δ; eauto. simpl in *.
          + unfold same_content_stack in *.
            intros ? ? ? E G.
            specialize (STACK_CONTENT2 _ _ _ E G) as [X STACK_CONTENT2].
            split; destruct sp2; simpl in *; try congruence.
            { intros ?? A; inv A. intros ??.
              eapply Mem.perm_free_1; eauto.
              destruct (Pos.eqb_spec b4 b); auto; subst; right.
              destruct (zlt ofs0 0); auto; right.
              destruct (zle sz ofs0); auto. exfalso.
              (* clear free3. *)
              exploit Mem.free_range_perm; eauto. instantiate (1 := ofs0); lia. intros ?.
              eapply PERM2. eapply Mem.perm_max, Mem.perm_implies; eauto. constructor.
              eapply X; eauto. }
            intros ? G''.
            eapply Mem.load_free_2 in G'' as G'''; eauto.
          (* specialize (STACK_CONTENT2 _ G''') as [? ?]. split; auto. *)
          + unfold at_most_readable in *. destruct sp2; try auto.
            split. eapply Mem.valid_block_free_1; eauto. eapply PERM2.
            intros ? N. eapply PERM2.
            eapply Mem.perm_free_3; eauto.
          + unfold nonempty in *.
            destruct sp2; try contradiction.
            eapply Mem.free_range_perm in eq1 as ?.
            destruct (eq_block b b0). subst.
            -- destruct (zlt 0 0); auto.
               eapply Mem.perm_free_1; eauto.
               destruct (zle sz 0); auto.
               eapply Mem.perm_free_1; eauto.
               (* lia. *) exfalso.
               eapply PERM2.
               apply Mem.range_perm_max in H.
               eapply Mem.perm_implies.
               eapply H. instantiate (1 := 0). lia. constructor.
            -- eapply Mem.perm_free_1; eauto.
          + split. eapply Mem.valid_block_free_1; eauto. eapply EMPTY2.
            intros ? N. eapply EMPTY2.
            eapply Mem.perm_free_3; eauto.
      }
  Qed.

  Hypothesis senv_public: forall id,
      Senv.public_symbol ge3 id = Senv.public_symbol ge1 id.

  Hypothesis senv_wf: forall id cp b,
      Senv.find_symbol ge1 id = Some b ->
      Senv.find_comp ge1 id ⊆ cp ->
      exists fd, Genv.find_def ge1 b = Some fd.

  Hypothesis same_cp_main: comp_of_main W3 = comp_of_main W1.

  (* External calls preserved *)
  Lemma external_call_inject_left:
    forall ef cp vargs m1 t vres m2 j__δ j__oppδ m1' vargs' m3 rs1 rs3 st1 st2 st3
      (not_bottom: cp <> bottom)
      (not_top: cp <> top),
      s cp = δ ->
      meminj_preserves_globals s δ W1 W3 j__δ ->
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
      external_call ef ge1 cp vargs m1 t vres m1' ->
      Val.inject_list j__δ vargs vargs' ->

      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ m1 m2 m3 st1 st2 st3 ->

      exists j__δ', exists vres', exists m3',
        external_call ef ge3 cp vargs' m3 t vres' m3'
        /\ Val.inject j__δ' vres vres'
        /\ Mem.unchanged_on (loc_unmapped j__δ) m1 m1'
        /\ Mem.unchanged_on (loc_out_of_reach j__δ m1) m3 m3'
        /\ inject_incr j__δ j__δ'
        /\ inject_separated j__δ j__δ' m1 m3 /\
          meminj_preserves_globals s δ W1 W3 j__δ' /\
          mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
          mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
          regset_rel j__δ' rs1 rs3 /\
          stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ m1' m2 m3' st1 st2 st3.
  Proof.
    intros * s_ef inj_pres inj_pres' extcall1 inj_args m1_m3 m2_m3 rs1_rs3 st_rel.
    exploit external_call_mem_inject_gen; eauto using partial_mem_inject.
    eapply globals_symbols_inject; eauto.
    intros (j__δ' & vres' & m3' & extcall3 & inj_res & inj_mem & unchanged1 & unchanged2 & incr & inj_sep).

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
          assert (j__δ b = Some (b', delta)).
          { destruct (j__δ b) as [[] |] eqn:j_b.
            exploit incr; eauto. congruence.
            exploit inj_sep; eauto.
            intros [].
            exploit Genv.find_symbol_find_def_inversion; eauto. intros [? ?].
            exploit find_def_valid1; eauto. congruence. }

          exploit symbols_inject1; eauto.
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
      rewrite inj_pres'; eauto. intros G. exploit G; eauto. intros []; eauto.
    - exploit (extcall_preserves_mem_rel_opp_side2 s W2 W3); eauto.
      now destruct δ.
    - intros x. exploit val_inject_incr; eauto.
    - exploit extcall_preserves_mem_rel_same_side; eauto.
      rewrite inj_pres'; eauto. intros G. exploit G; eauto. intros []; eauto.
      rewrite inj_pres' in *; eauto.
  Qed.

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


  Lemma regset_rel_invalidate_call: forall j rs1' rs3' sig,
      regset_rel j rs1' rs3' ->
      regset_rel j (invalidate_call rs1' sig) (invalidate_call rs3' sig).
  Proof.
    intros ? ? ? ? H.
    intros r. specialize (H r).
    unfold invalidate_call.
    destruct orb; auto.
  Qed.

  Lemma regset_rel_invalidate_return: forall j rs1' rs3' sig,
      regset_rel j rs1' rs3' ->
      regset_rel j (invalidate_return rs1' sig) (invalidate_return rs3' sig).
  Proof.
    intros ? ? ? ? H.
    intros r. specialize (H r).
    unfold invalidate_return.
    destruct orb; auto.
  Qed.

  Lemma regset_rel_return_from_external:
    forall j rs1 rs2 ef res1 res2 pc1 pc2 sg,
      regset_rel j rs1 rs2 ->
      Val.inject j res1 res2 ->
      Val.inject j pc1 pc2 ->
      regset_rel j
        ((invalidate_return (set_pair (loc_external_result (ef_sig ef))
            res1 rs1) sg) # PC <- pc1)
        ((invalidate_return (set_pair (loc_external_result (ef_sig ef))
           res2 rs2) sg)  # PC <- pc2).
  Proof.
    intros j rs1 rs2 ef res1 res2 pc1 pc2 sg H H0.
    assert (G: regset_rel j
                 (invalidate_return (set_pair (loc_external_result (ef_sig ef)) res1
                    rs1) sg)
                 (invalidate_return (set_pair (loc_external_result (ef_sig ef)) res2
                    rs2) sg)).
    { eapply regset_rel_invalidate_return.
      destruct (loc_external_result (ef_sig ef)).
      + eapply regset_rel_inject; eauto.
        (* { unfold undef_caller_save_regs. *)
        (*   intros x. destruct orb; auto. } *)
      + eapply regset_rel_inject; eauto using Val.loword_inject.
        eapply regset_rel_inject; eauto using Val.hiword_inject. }
        (* { unfold undef_caller_save_regs. *)
        (*   intros x. destruct orb; auto. } } *)
    eapply regset_rel_inject; eauto.
  Qed.

  Definition stack_of_state (s: state) :=
    match s with
    | State st _ _ _ | ReturnState st _ _ _ => st
    end.
  Definition mem_of_state (s: state) :=
    match s with
    | State st _ m _ | ReturnState st _ m _ => m
    end.


  Lemma find_def_find_symbol: forall b gd,
      Genv.find_def ge1 b = Some gd ->
      exists id, Genv.find_symbol ge1 id = Some b.
  Proof.
    intros.
    exploit Genv.find_def_find_symbol_inversion; eauto.
  Qed.

  Lemma find_funct_ptr_find_symbol: forall b fd,
      Genv.find_funct_ptr ge1 b = Some fd ->
      exists id, Genv.find_symbol ge1 id = Some b.
  Proof.
    intros * H. unfold Genv.find_funct_ptr in H.
    destruct (Genv.find_def ge1 b) as [[fd' |]|] eqn:?; try congruence.
    assert (fd' = fd) by congruence; subst fd'; clear H.
    exploit find_def_find_symbol; eauto.
  Qed.


  Lemma nextinstr_pc_return_builtin_value:
    forall rs res vres ef
      (RES_NOT_PC : exists reg : builtin_res mreg, res = map_builtin_res preg_of reg),
      nextinstr (set_res res vres (undef_regs (map preg_of (destroyed_by_builtin ef))
                                     (rs # X1 <- Vundef) # X31 <- Vundef)) PC =
        Val.offset_ptr (rs PC) Ptrofs.one.
  Proof.
    intros rs res vres ef RES_NOT_PC.
    destruct RES_NOT_PC as [reg ?]; subst res.
    Simpl.
    rewrite Asmgenproof0.set_res_other; eauto.
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
    rewrite Asmgenproof0.undef_regs_other_2; eauto.
  Qed.

  (* Some simulation diagrams *)
  Lemma step_E0_strong: forall (s1 s1': state),
      Step (semantics W1) s1 E0 s1' ->
      forall (s2 s3: state) j__δ j__oppδ,
        meminj_preserves_globals s δ W1 W3 j__δ ->
        meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
        stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ (mem_of_state s1) (mem_of_state s2) (mem_of_state s3) (stack_of_state s1) (stack_of_state s2) (stack_of_state s3) ->
        strong_equivalence s cp_main ge1 ge3 j__δ δ s1 s3 ->
        weak_equivalence s ge2 ge3 j__oppδ (opposite δ) s2 s3 ->
        exists (s3': state) j__δ',
          Plus (semantics W3) s3 E0 s3' /\
            meminj_preserves_globals s δ W1 W3 j__δ' /\
            meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ /\
            stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ (mem_of_state s1') (mem_of_state s2) (mem_of_state s3') (stack_of_state s1') (stack_of_state s2) (stack_of_state s3') /\
            strong_equivalence s cp_main ge1 ge3 j__δ' δ s1' s3' /\
            weak_equivalence s ge2 ge3 j__oppδ (opposite δ) s2 s3'.
  Proof.
    intros s1 s1' H s2 s3 j__δ j__oppδ inj_pres1 inj_pres2 st_rel strong_s1_s3 weak_s2_s3.
    simpl in H.
    inv H.
    - assert (same_comp:
               Genv.find_comp_in_genv ge1 (rs' PC) = Genv.find_comp_in_genv ge1 (rs PC)).
      { rewrite NEXTPC, H0; simpl; rewrite <- ALLOWED; auto.
        now unfold Genv.find_comp_of_block; rewrite H1. }
      exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''.
        unfold Genv.find_def in R; rewrite R. simpl; simpl in side_f. rewrite side_f. now destruct side_eq. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      exploit exec_instr_preserved; simpl; eauto. simpl in st_rel.
      replace m2 with (mem_of_state s2). eauto. destruct s2; simpl in *; congruence.
      intros (j__δ' & rs3' & m3' & exec_instr' & inj_pres' & m1_m3' & m2_m3' & rs1_rs3' & st_rel' & incr).

      assert (exists b', rs3' PC = Vptr b' ofs') as [b3' rs3'_PC].
      { pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc.
        assert (delta = 0) by now eapply (delta_zero s ge1 ge3); eauto. subst delta. rewrite Ptrofs.add_zero in *.
        eauto. }
      assert (same_comp':
               Genv.find_comp_of_block ge3 b3' = Genv.find_comp_of_block ge1 b').
      { specialize (rs1_rs3' PC) as inj_pc. rewrite NEXTPC, rs3'_PC in inj_pc.
        erewrite <- (find_comp_of_block_preserved _ W1 W3); eauto using delta_zero.
        inv inj_pc; try congruence.
        exploit (delta_zero s ge1 ge3); eauto; intros ->.
        now rewrite Ptrofs.add_zero in *; eauto.
      }

      exists (State st3 rs3' m3' (has_comp_function f)), j__δ'; split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        econstructor; eauto.
        rewrite same_comp'. auto.
      + eauto.
      + eauto.
      + simpl.
        replace (mem_of_state s2) with m2. eauto. destruct s2; simpl in *; congruence.
      + inv strong_s1_s3; econstructor; eauto.
        * inv COMP1. econstructor; try rewrite same_comp; eauto.
        * inv COMP1; try congruence.
          econstructor; eauto. rewrite rs3'_PC; simpl; rewrite same_comp'.
          rewrite <- same_comp in H11; simpl in H11; rewrite NEXTPC in H11; eauto.
      + (* assert (cp = comp_of f); subst. *)
        inv weak_s2_s3; inv A; econstructor; eauto.
        * inv COMP2; try congruence.
          econstructor; try rewrite same_comp; eauto.
          rewrite eq_pc', rs3'_PC. simpl; auto.
          rewrite same_comp', <- ALLOWED. unfold Genv.find_comp_of_block; rewrite find_funct.
          auto.
        * inv COMP2; try congruence.
          { econstructor; try rewrite same_comp; eauto.
            rewrite eq_pc', rs3'_PC. simpl; auto.
            rewrite same_comp', <- ALLOWED. unfold Genv.find_comp_of_block; rewrite find_funct.
            auto. }

    - exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''.
        unfold Genv.find_def in R; rewrite R. simpl; simpl in side_f. rewrite side_f. now destruct side_eq. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      assert (exists dsp3 dosp3,
                 asm_parent_dummy_sp st3 = Vptr dsp3 dosp3) as [dsp3 [dosp3 ?]].
      { inv strong_s1_s3. inv st_rel.
        simpl in *; subst; simpl in *;
          unfold Vnullptr in *; destruct Archi.ptr64; congruence.
        simpl in *. inv H11. simpl in *. eauto.
        simpl in *. inv COMP2; eauto. }
      { assert (rs3 ra = Vptr dsp3 o').
        { specialize (rs1_rs3 ra). rewrite H4 in rs1_rs3.
          inv st_rel.
          - simpl in *; subst; simpl in *;
              unfold Vnullptr in *; destruct Archi.ptr64; discriminate.
          - inv H11; simpl in *.
            + inv H; inv H3; simpl in *.
              inv strong_s1_s3; simpl in *.
              rewrite SIDE in *. destruct side_eq; try congruence.
              inv H20; inv rs1_rs3; try congruence.
              assert (dsp3 = b5) by congruence. subst b5.
              assert (delta = delta0) by congruence. subst delta0.
              exploit delta_zero; eauto. intros ->. rewrite Ptrofs.add_zero.
              reflexivity.
            + inv H; inv H3; simpl in *.
              inv strong_s1_s3; simpl in *. (* H11 + *)
              inv COMP1; eauto. rewrite H0 in *; simpl in *.
              unfold Genv.find_comp_of_block in *; rewrite H1 in *; simpl in *.
              destruct side_eq; try congruence.
              inv H20; inv rs1_rs3; try congruence.
              assert (dsp3 = b5) by congruence. subst b5.
              assert (delta = delta0) by congruence. subst delta0.
              exploit delta_zero; eauto. intros ->. rewrite Ptrofs.add_zero.
              reflexivity. }
        simpl in *.
        assert (exists v2, Mem.loadv (chunk_of_type ty) m3
                  (Val.offset_ptr (asm_parent_sp st3) (Ptrofs.add o' (eval_offset ge3 o))) top =
                  Some v2 /\ Val.inject j__δ v v2) as [v2 [? ?]].
        { inv st_rel;
            [simpl in *; unfold Vnullptr in *; destruct Archi.ptr64; congruence|].
          simpl_before_exists.
          { inv H12.
            - simpl in *.
              destruct sp1; simpl in *; try congruence.
              inv H17; simpl in *.
              exploit Mem.load_inject; eauto.
              now eapply partial_mem_inject; eauto.
              intros [v2 [LOAD' INJ']].
              assert (delta = 0)
                as ->
                  by (now eapply (delta_zero _ _ _ _ _ _ _ m1_m3); eauto).
              rewrite Ptrofs.add_zero; simpl in *.
              rewrite Z.add_0_r in LOAD'.
              eauto.
            - assert (exists ofs_arg, Ptrofs.unsigned (Ptrofs.add o' ofs0) =
                                   Stacklayout.fe_ofs_arg + 4 * ofs_arg) as [? R].
              { inv H6; eauto. }
              exploit STACK_CONTENT1; eauto. rewrite R; eauto.
              intros [X Y].
              exploit Y; eauto. rewrite <- R, Ptrofs.repr_unsigned.
              eauto.
              intros [NOTPTR ?].
              eexists; split; eauto.
              rewrite <- R, Ptrofs.repr_unsigned in H12. eauto.
              { destruct v; simpl in NOTPTR; try contradiction;
                  eauto. } }
          { inv H12.
            - simpl in *.
              destruct sp1; simpl in *; try congruence.
              inv H17; simpl in *.
              exploit Mem.load_inject; eauto.
              now eapply partial_mem_inject; eauto.
              intros [v2 [LOAD' INJ']].
              assert (delta = 0)
                as ->
                  by (now eapply (delta_zero _ _ _ _ _ _ _ m1_m3); eauto).
              rewrite Ptrofs.add_zero; simpl in *.
              rewrite Z.add_0_r in LOAD'.
              eauto.
            - assert (exists ofs_arg, Ptrofs.unsigned o' =
                                   Stacklayout.fe_ofs_arg + 4 * ofs_arg) as [? R].
              { inv H6; eauto. }
              exploit STACK_CONTENT1; eauto. rewrite R; eauto.
              intros [X Y].
              exploit Y; eauto. rewrite <- R, Ptrofs.repr_unsigned.
              eauto.
              intros [NOTPTR ?].
              eexists; split; eauto.
              rewrite <- R, Ptrofs.repr_unsigned in H12. eauto.
              { destruct v; simpl in NOTPTR; try contradiction;
                  eauto. } }
          }
        destruct rd; [specialize (H8 _ eq_refl); clear H9 | specialize (H9 _ eq_refl); clear H8].

        { eexists; eexists;
            split; [| split; [| split; [| split; [| split]]]].
          + econstructor; [| now eapply star_refl | now traceEq].
            eapply exec_step_load_arg_cross; eauto.
            { inv st_rel; eauto.
              - simpl in *. congruence.
              - inv H13; inv H; eauto. }
            { inv st_rel;
                [simpl in *; unfold Vnullptr in *; destruct Archi.ptr64; congruence|].
              inv H13; simpl in *; eauto. }
            intros ? G; inv G. reflexivity.
            intros ? G; inv G.
          + eauto.
          + eauto.
          + eauto.
          + inv strong_s1_s3; econstructor; eauto.
            * inv COMP1; econstructor; auto.
              -- Simpl. rewrite H0 in *; simpl; eauto.
            * inv COMP2; econstructor; eauto.
              -- Simpl. rewrite eq_pc' in *; simpl; eauto.
            * eapply regset_rel_inject. eapply regset_rel_inject. eauto.
              eauto.
              (* destruct v; try now constructor. *)
              (* contradiction. *)
              Simpl. eapply Val.offset_ptr_inject; eauto.
          + inv weak_s2_s3; inv A; econstructor; eauto.
            * inv COMP2; econstructor; eauto.
              -- Simpl. rewrite eq_pc' in *; simpl; eauto.
            * inv COMP2; econstructor; eauto.
              -- Simpl. rewrite eq_pc' in *; simpl; eauto.
        }
        { eexists; eexists; split; [| split; [| split; [| split; [| split]]]].
          + econstructor; [| now eapply star_refl | now traceEq].
            eapply exec_step_load_arg_cross; eauto.
            { inv st_rel; eauto.
              - simpl in *. congruence.
              - inv H13; inv H; eauto. }
            { inv st_rel;
                [simpl in *; unfold Vnullptr in *; destruct Archi.ptr64; congruence|].
              inv H13; simpl in *; eauto. }
            intros ? G; inv G.
            intros ? G; inv G. reflexivity.
          + eauto.
          + eauto.
          + eauto.
          + inv strong_s1_s3; econstructor; eauto.
            * inv COMP1; econstructor; auto.
              -- Simpl. rewrite H0 in *; simpl; eauto.
            * inv COMP2; econstructor; eauto.
              -- Simpl. rewrite eq_pc' in *; simpl; eauto.
            * eapply regset_rel_inject. eapply regset_rel_inject. eauto.
              eauto.
              (* destruct v; try now constructor. *)
              (* contradiction. *)
              Simpl. eapply Val.offset_ptr_inject; eauto.
          + inv weak_s2_s3; inv A; econstructor; eauto.
            * inv COMP2; econstructor; eauto.
              -- Simpl. rewrite eq_pc' in *; simpl; eauto.
            * inv COMP2; econstructor; eauto.
              -- Simpl. rewrite eq_pc' in *; simpl; eauto.
        }
      }


    - exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''.
        unfold Genv.find_def in R; rewrite R. simpl; simpl in side_f. rewrite side_f. now destruct side_eq. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      destruct rd; [specialize (EXECi _ eq_refl); clear EXECf | specialize (EXECf _ eq_refl); clear EXECi].

      simpl_before_exists.
      { eexists; eexists; split; [| split; [| split; [| split; [| split]]]].
        + econstructor; [| now eapply star_refl | now traceEq].
          eapply exec_step_load_arg_int; eauto.
          intros ? G; inv G. unfold exec_load. simpl.
          rewrite <- H4; simpl; rewrite load3.
          reflexivity.
          intros ? G; inv G.
        + eauto.
        + eauto.
        + eauto.
        + inv strong_s1_s3; econstructor; eauto.
          * inv COMP1. econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl. rewrite <- H11.
            rewrite H0. reflexivity.
          * inv COMP2; try congruence.
            econstructor; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl. rewrite <- H11.
            rewrite eq_pc'. reflexivity.
          * eapply regset_rel_inject; eauto.
            eapply regset_rel_inject; eauto.
            eapply Val.offset_ptr_inject; eauto. Simpl.
        + (* assert (cp = comp_of f); subst. *)
          inv weak_s2_s3; inv A; econstructor; eauto.
          * inv COMP2; try congruence.
            econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl.
            rewrite eq_pc'. reflexivity.
          * inv COMP2; try congruence.
            econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl.
            rewrite eq_pc'. reflexivity. }
      { eexists; eexists; split; [| split; [| split; [| split; [| split]]]].
        + econstructor; [| now eapply star_refl | now traceEq].
          eapply exec_step_load_arg_int; eauto.
          intros ? G; inv G. unfold exec_load. simpl. rewrite <- H4. simpl. unfold low_half.
          simpl.
          rewrite Ptrofs.add_zero. rewrite load3.
          reflexivity.
          intros ? G; inv G.
        + eauto.
        + eauto.
        + eauto.
        + inv strong_s1_s3; econstructor; eauto.
          * inv COMP1. econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl. rewrite <- H11.
            rewrite H0. reflexivity.
          * inv COMP2; try congruence.
            econstructor; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl. rewrite <- H11.
            rewrite eq_pc'. reflexivity.
          * eapply regset_rel_inject; eauto.
            eapply regset_rel_inject; eauto.
            eapply Val.offset_ptr_inject; eauto. Simpl.
        + (* assert (cp = comp_of f); subst. *)
          inv weak_s2_s3; inv A; econstructor; eauto.
          * inv COMP2; try congruence.
            econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl.
            rewrite eq_pc'. reflexivity.
          * inv COMP2; try congruence.
            econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl.
            rewrite eq_pc'. reflexivity. }

      simpl_before_exists.
      { eexists; eexists; split; [| split; [| split; [| split; [| split]]]].
        + econstructor; [| now eapply star_refl | now traceEq].
          eapply exec_step_load_arg_int; eauto.
          intros ? G; inv G.
          intros ? G; inv G. unfold exec_load. simpl.
          rewrite <- H4; simpl; rewrite load3.
          reflexivity.
        + eauto.
        + eauto.
        + eauto.
        + inv strong_s1_s3; econstructor; eauto.
          * inv COMP1. econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl. rewrite <- H11.
            rewrite H0. reflexivity.
          * inv COMP2; try congruence.
            econstructor; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl. rewrite <- H11.
            rewrite eq_pc'. reflexivity.
          * eapply regset_rel_inject; eauto.
            eapply regset_rel_inject; eauto.
            eapply Val.offset_ptr_inject; eauto. Simpl.
        + (* assert (cp = comp_of f); subst. *)
          inv weak_s2_s3; inv A; econstructor; eauto.
          * inv COMP2; try congruence.
            econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl.
            rewrite eq_pc'. reflexivity.
          * inv COMP2; try congruence.
            econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl.
            rewrite eq_pc'. reflexivity. }
      { eexists; eexists; split; [| split; [| split; [| split; [| split]]]].
        + econstructor; [| now eapply star_refl | now traceEq].
          eapply exec_step_load_arg_int; eauto.
          intros ? G; inv G.
          intros ? G; inv G. unfold exec_load. simpl. rewrite <- H4. simpl. unfold low_half.
          simpl.
          rewrite Ptrofs.add_zero. rewrite load3.
          reflexivity.
        + eauto.
        + eauto.
        + eauto.
        + inv strong_s1_s3; econstructor; eauto.
          * inv COMP1. econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl. rewrite <- H11.
            rewrite H0. reflexivity.
          * inv COMP2; try congruence.
            econstructor; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl. rewrite <- H11.
            rewrite eq_pc'. reflexivity.
          * eapply regset_rel_inject; eauto.
            eapply regset_rel_inject; eauto.
            eapply Val.offset_ptr_inject; eauto. Simpl.
        + (* assert (cp = comp_of f); subst. *)
          inv weak_s2_s3; inv A; econstructor; eauto.
          * inv COMP2; try congruence.
            econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl.
            rewrite eq_pc'. reflexivity.
          * inv COMP2; try congruence.
            econstructor; try rewrite same_comp; eauto.
            rewrite Asmgenproof0.nextinstr_pc. Simpl.
            rewrite eq_pc'. reflexivity. }

    - exploit strong_equiv_state_internal_inv; eauto.
      rename f' into nextf.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit (find_def_find_symbol b); eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''.
        unfold Genv.find_def in R; rewrite R.
        simpl in *; rewrite side_f; now destruct side_eq. }
      intros <-.
      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      exploit (exec_instr_preserved j__δ j__oppδ f); simpl; eauto.
      replace m2 with (mem_of_state s2); eauto.
      destruct s2; simpl in *; now congruence.
      intros (j__δ' & rs3' & m3' & exec_instr' & inj_pres' & m1_m3' & m2_m3' & rs1_rs3' & st_rel' & incr).

      assert (exists b', rs3' PC = Vptr b' Ptrofs.zero) as [b3' rs3'_PC].
      { pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc.
        assert (delta = 0) by now eapply (delta_zero s ge1 ge3); eauto. subst delta. rewrite Ptrofs.add_zero in *.
        eauto. }
      assert (H: Genv.find_comp_in_genv ge1 (rs' PC) ⊆ comp_of f).
      { rewrite NEXTPC. simpl.
        unfold Genv.allowed_call in ALLOWED.
        destruct ALLOWED; auto.
        inv EV; auto.
        unfold Genv.type_of_call in H5. destruct flowsto_dec; try auto. contradiction. }

      (* destruct (cp_eq_dec (Genv.find_comp_in_genv ge1 (rs' PC)) (comp_of f)) as [int | ext]. *)

      { eapply update_stack_call_preserved_internal with (st3 := st3) in STUPD
            as [? [? [? STUPD]]];
          eauto using delta_zero; try congruence.
        subst st' rs'' m''.
        exploit call_arguments_preserved; eauto.
        intros [args' [inj_args call_args']].

        assert (exists nextf,
                   Genv.find_def ge3 b3' = Some (Gfun (Internal nextf)))
                 as [next ?].
        { specialize (rs1_rs3' PC) as G.
        rewrite NEXTPC, rs3'_PC in G. inv G.
        exploit defs_inject; eauto.
        intros [? [? [? G]]].
        inv G. inv H7. inv H11. eauto. }
        exists (State st3 (invalidate_call rs3' sig) m3' (has_comp_function f)), j__δ';
          split; [| split; [| split; [| split; [| split]]]].
        + econstructor; [| now eapply star_refl | now traceEq].
          eapply exec_step_internal_call; eauto.
          * eapply allowed_call_preserved with (v := Vptr b' Ptrofs.zero);
              eauto using delta_zero.
            congruence.
            specialize (rs1_rs3' PC) as inj_pc. rewrite NEXTPC, rs3'_PC in inj_pc.
            inv inj_pc; try congruence. exploit (delta_zero s ge1 ge3); eauto; intros ->.
          * specialize (rs1_rs3' PC); inv rs1_rs3'; try congruence.
            assert (b1 = b') by congruence; subst.
            assert (b2 = b3') by congruence; subst.
            erewrite <- find_comp_of_block_preserved; eauto using delta_zero.
            unfold Genv.type_of_call; destruct flowsto_dec; try congruence.
            rewrite NEXTPC in *; contradiction.
          * specialize (rs1_rs3' PC); inv rs1_rs3'; try congruence.
            assert (b1 = b') by congruence; subst.
            assert (b2 = b3') by congruence; subst.
            erewrite <- find_comp_of_block_preserved; eauto using delta_zero.
            unfold Genv.type_of_call; destruct flowsto_dec; try congruence.
            rewrite NEXTPC in *; contradiction.
          * specialize (rs1_rs3' PC); inv rs1_rs3'; try congruence.
            assert (b1 = b') by congruence; subst.
            assert (b2 = b3') by congruence; subst.
            erewrite <- find_comp_of_block_preserved; eauto using delta_zero.
            constructor; eauto.
            unfold Genv.type_of_call; destruct flowsto_dec; try congruence.
            rewrite NEXTPC in *; contradiction.
        + eauto.
        + eauto.
        + simpl. replace (mem_of_state s2) with m2; eauto. destruct s2; simpl in *; congruence.
        + econstructor; eauto.
          * inv H.
            -- specialize (rs1_rs3' PC); rewrite NEXTPC, rs3'_PC in rs1_rs3'; inv rs1_rs3'; try congruence.
               exploit no_bottom1; eauto.
               rewrite NEXTPC in H7. simpl in H7.
               unfold Genv.find_comp_of_block in H7.
               rewrite NEXT_INT in H7. auto. contradiction.
            -- exploit (no_top1 b); eauto. contradiction.
            -- eapply comp_of_state_internal; eauto.
          * inv H.
            -- specialize (rs1_rs3' PC); rewrite NEXTPC, rs3'_PC in rs1_rs3'; inv rs1_rs3'; try congruence.
               exploit no_bottom1; eauto.
               rewrite NEXTPC in H7. simpl in H7.
               unfold Genv.find_comp_of_block in H7.
               rewrite NEXT_INT in H7. auto. contradiction.
            -- exploit (no_top1 b); eauto. contradiction.
            -- eapply comp_of_state_internal; eauto.
               rewrite invalidate_call_PC, rs3'_PC. simpl.
               specialize (rs1_rs3' PC); rewrite NEXTPC, rs3'_PC in rs1_rs3'; inv rs1_rs3'; try congruence.
               erewrite <- (find_comp_of_block_preserved _ W1 W3 _ j__δ'); eauto using delta_zero.
               rewrite <- H8, NEXTPC; auto.
          * inv strong_s1_s3. inv COMP1.
            now rewrite H0 in H12; simpl in H12;
              unfold Genv.find_comp_of_block in H12; rewrite H1 in H12.
          * eapply regset_rel_invalidate_call; eauto.
        + inv weak_s2_s3; inv A; econstructor; eauto.
          * assert (cp = comp_of f) as ->.
            { inv COMP2.
              now rewrite eq_pc'; simpl; unfold Genv.find_comp_of_block; rewrite find_funct. }
            inv H.
            -- specialize (rs1_rs3' PC); rewrite NEXTPC, rs3'_PC in rs1_rs3'; inv rs1_rs3'; try congruence.
               exploit no_bottom1; eauto.
               rewrite NEXTPC in H7. simpl in H7.
               unfold Genv.find_comp_of_block in H7.
               rewrite NEXT_INT in H7. auto. contradiction.
            -- exploit (no_top1 b); eauto. contradiction.
            -- eapply comp_of_state_internal; eauto.
               rewrite invalidate_call_PC, rs3'_PC. simpl.
               specialize (rs1_rs3' PC); rewrite NEXTPC, rs3'_PC in rs1_rs3'; inv rs1_rs3'; try congruence.
               erewrite <- (find_comp_of_block_preserved _ W1 W3 _ j__δ'); eauto using delta_zero.
               rewrite <- H9, NEXTPC; auto.
          *
           assert (cp = comp_of f) as ->.
            { inv COMP2.
              now rewrite eq_pc'; simpl; unfold Genv.find_comp_of_block; rewrite find_funct. } inv H.
            -- specialize (rs1_rs3' PC); rewrite NEXTPC, rs3'_PC in rs1_rs3'; inv rs1_rs3'; try congruence.
               exploit no_bottom1; eauto.
               rewrite NEXTPC in H7. simpl in H7.
               unfold Genv.find_comp_of_block in H7.
               rewrite NEXT_INT in H7. auto. contradiction.
            -- exploit (no_top1 b); eauto. contradiction.
            -- eapply comp_of_state_internal; eauto.
               rewrite invalidate_call_PC, rs3'_PC. simpl.
               specialize (rs1_rs3' PC); rewrite NEXTPC, rs3'_PC in rs1_rs3'; inv rs1_rs3'; try congruence.
               erewrite <- (find_comp_of_block_preserved _ W1 W3 _ j__δ'); eauto using delta_zero.
               rewrite <- H9, NEXTPC; auto.
      + rewrite NEXTPC in *; simpl in *; unfold Genv.find_comp_of_block in H.
        rewrite NEXT_INT in H. simpl in *.
        inv H.
        * exploit no_bottom1; eauto. contradiction.
        * exploit (no_top1 b); eauto. contradiction.
        * unfold Genv.find_comp_of_block.
          now rewrite NEXT_INT. }

    (** [State] to [ReturnState] *)
    - exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        unfold Genv.find_funct_ptr in H1. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        simpl in *; rewrite side_f; now destruct side_eq. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      exploit exec_instr_preserved; simpl; eauto. replace m2 with (mem_of_state s2); eauto.
      destruct s2; simpl in *; now congruence.
      intros (j__δ' & rs3' & m3' & exec_instr' & inj_pres' & m1_m3' & m2_m3' & rs1_rs3' & st_rel' & incr).



      exists (ReturnState st3 rs3' m3' (comp_of f)), j__δ'; split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_internal_return; eauto.
      + eauto.
      + eauto.
      + simpl; eauto.
        replace (mem_of_state s2) with m2; eauto. destruct s2; simpl in *; now congruence.
      + econstructor; eauto.
        * econstructor; eauto.
        * econstructor; eauto.
        * inv strong_s1_s3; eauto. inv COMP1.
          rewrite H0 in H10; simpl in H10; unfold Genv.find_comp_of_block in H10;
            rewrite H1 in H10. auto.
      + inv weak_s2_s3; inv A; econstructor; eauto.
        * inv COMP2.
          -- rewrite eq_pc'; simpl; unfold Genv.find_comp_of_block; rewrite find_funct.
             econstructor; eauto.
        * inv COMP2.
          -- rewrite eq_pc'; simpl; unfold Genv.find_comp_of_block; rewrite find_funct.
             econstructor; eauto.

    (** [ReturnState] to [State] *)
    - exploit strong_equiv_returnstate_inv; eauto.
      intros (st3 & rs3 & m3 & ? & m1_m3 & rs1_rs3); subst.

      simpl in st_rel.
      assert (same_sg: sig_of_call st = sig_of_call st3) by
        (inv st_rel; [reflexivity | inv H3; auto]).

      assert (res_inj: Val.inject j__δ (return_value rs (sig_of_call st)) (return_value rs3 (sig_of_call st3))).
      { simpl in st_rel.
        rewrite <- same_sg.
        unfold return_value.
        destruct (loc_result (sig_of_call st)).
        - now apply rs1_rs3.
        - apply Val.longofwords_inject; now apply rs1_rs3. }

      pose proof (rs1_rs3 PC) as inj_pc; inv inj_pc; try congruence.
      assert (b1 = b) as -> by congruence.
      assert (ofs1 = ofs) as -> by congruence.

      exploit delta_zero; eauto. intros ->.
      exploit (find_def_preserved s W1 W3); eauto.
      intros [? [? [R ?]]].
      inv R; eauto. inv H7; eauto.

      exists (State st3 (invalidate_return rs3 sig) m3
           (Genv.find_comp_in_genv ge1 (rs PC))), j__δ;
        split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_return; eauto.
        * pose proof (rs1_rs3 PC) as inj_pc; inv inj_pc; try congruence.
          unfold Vnullptr; destruct Archi.ptr64; congruence.
        * pose proof (rs1_rs3 PC) as inj_pc; inv inj_pc; try congruence.
        * simpl in *. rewrite <- H, <- H2. simpl.
          erewrite <- (find_comp_of_block_preserved _ W1 W3); eauto using delta_zero.
        * rewrite <- H. reflexivity.
      + eauto.
      + eauto.
      + simpl. eauto.
      + rewrite <- H; simpl.
        econstructor; try rewrite same_sg;
          eauto using regset_rel_invalidate_return.
        * simpl.
          inv strong_s1_s3; inv COMP2.
          -- econstructor; eauto. rewrite invalidate_return_PC.
             rewrite <- H; simpl. unfold Genv.find_comp_of_block.
             rewrite FD. eauto.
             intros ?.
             exploit no_bottom1; eauto.
        * (* destruct H2 as [? [? [? [? [? ?]]]]]. *)
          inv strong_s1_s3; inv COMP2.
          -- econstructor; eauto. rewrite invalidate_return_PC.
             rewrite <- H2; simpl. unfold Genv.find_comp_of_block.
             rewrite H4. eauto.
        * inv strong_s1_s3; auto. simpl in *.
          inv COMP1.
          -- rewrite ATPC. simpl.
             unfold Genv.find_comp_of_block; rewrite FD; simpl.
             reflexivity.
        * inv strong_s1_s3.
          (* destruct H2 as [? [? [? [G [G' ?]]]]]. *)
          inv COMP1.
          -- unfold Genv.find_comp_of_block; rewrite FD; simpl.
             intros ?. exploit no_top1; eauto.
        * inv strong_s1_s3.
          (* destruct H2 as [? [? [? [G [G' ?]]]]]. *) inv COMP1.
          -- rewrite ATPC in H7. simpl in *; congruence.
        * inv strong_s1_s3; auto. simpl in *.
          inv COMP1.
          -- rewrite ATPC. simpl.
             unfold Genv.find_comp_of_block; rewrite FD; simpl.
             reflexivity.
      + erewrite find_comp_preserved; eauto using delta_zero.
        inv weak_s2_s3.
        * econstructor; eauto.
          { econstructor; eauto.
            rewrite invalidate_return_PC.
            erewrite <- (find_comp_preserved s W1 W3); eauto using delta_zero.
            inv COMP2.
            -- reflexivity. }
          { erewrite <- (find_comp_preserved s W1 W3); eauto using delta_zero.
            rewrite ATPC. simpl. unfold Genv.find_comp_of_block; rewrite FD.
            intros ?; exploit no_top1; eauto. }
          { erewrite <- (find_comp_preserved s W1 W3); eauto using delta_zero.
            rewrite ATPC. simpl. unfold Genv.find_comp_of_block; rewrite FD.
            intros ?; exploit no_bottom1; eauto. }
        * econstructor; eauto.
          { econstructor; eauto.
            rewrite invalidate_return_PC.
            erewrite <- (find_comp_preserved s W1 W3); eauto using delta_zero.
            inv COMP2.
            -- reflexivity. }
          { erewrite <- (find_comp_preserved s W1 W3); eauto using delta_zero.
            rewrite ATPC. simpl. unfold Genv.find_comp_of_block; rewrite FD.
            intros ?; exploit no_top1; eauto. }
          { erewrite <- (find_comp_preserved s W1 W3); eauto using delta_zero.
            rewrite ATPC. simpl. unfold Genv.find_comp_of_block; rewrite FD.
            intros ?; exploit no_bottom1; eauto. }

    - (* return-cross: impossible *)
      exfalso. simpl in *.
      inv weak_s2_s3; inv strong_s1_s3; inv EV.
      + assert (rec_cp0 = rec_cp') as ->.
        { inv COMP1; inv COMP2. reflexivity. }
        assert (rec_cp' = cp) as -> by now inv COMP1.
        assert (cp = callee_comp cp_main st'0) as -> by now inv COMP0.
        inv st_rel; simpl in *; subst; try congruence.
        inv H6; simpl in *; eauto.
        * destruct (flowsto_dec); try congruence.
          inv f; congruence.
        * destruct (flowsto_dec); try congruence.
          inv f; congruence.
      +assert (rec_cp' = cp) as -> by now inv COMP2.
        assert (cp = callee_comp cp_main st'0) as -> by now inv COMP0.
        inv st_rel; simpl in *; subst; try congruence.
        inv H6; simpl in *; eauto.
        * destruct (flowsto_dec); try congruence.
          inv f; congruence.
        * destruct (flowsto_dec); try congruence.
          inv f; congruence.

    (** Builtin *)
    - exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        unfold Genv.find_funct_ptr in H1. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        simpl in *; rewrite side_f; now destruct side_eq. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).

      exploit eval_builtin_args_inject; eauto using delta_zero, partial_mem_inject.
      intros (vl' & eval_args' & inj_args').
      exploit external_call_inject_left; eauto using partial_mem_inject.
      replace m2 with (mem_of_state s2); eauto. destruct s2; simpl in *; congruence.
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      eexists; exists j__δ'; split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_builtin; eauto.
      + eauto.
      + eauto.
      + replace (mem_of_state s2) with m2; eauto. destruct s2; simpl in *; congruence.
      + econstructor; eauto.
        * econstructor.
          rewrite nextinstr_pc_return_builtin_value; eauto.
          rewrite H0; simpl. unfold Genv.find_comp_of_block; now rewrite H1.
          eapply no_bottom1; eauto.
        * econstructor.
          rewrite nextinstr_pc_return_builtin_value; eauto.
          rewrite eq_pc'; simpl. unfold Genv.find_comp_of_block; now rewrite find_funct.
          eapply no_bottom1; eauto.
        * inv strong_s1_s3.
          inv COMP1. rewrite <- H10.
          rewrite H0; simpl. unfold Genv.find_comp_of_block; now rewrite H1.
        * eapply regset_rel_return_from_builtin; eauto.
      + inv strong_s1_s3; inv weak_s2_s3; inv A; econstructor; eauto.
        * assert (cp = callee_comp cp_main st3) by (eapply comp_of_state_unique; eauto); subst cp.
          econstructor.
          { rewrite nextinstr_pc_return_builtin_value; eauto.
            inv COMP2; eauto. rewrite eq_pc' in *; eauto. }
          { inv COMP2; eauto. }
        * assert (cp = callee_comp cp_main st3) by (eapply comp_of_state_unique; eauto); subst cp.
          econstructor.
          { rewrite nextinstr_pc_return_builtin_value; eauto.
            inv COMP2; eauto. rewrite eq_pc' in *; eauto. }
          { inv COMP2; eauto. }

    (** External call *)
    - exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit (find_def_find_symbol b); eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''.
        unfold Genv.find_def in R; rewrite R.
        simpl in *; rewrite side_f; now destruct side_eq. }
      intros <-.
      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      exploit (exec_instr_preserved j__δ j__oppδ f); simpl; eauto.
      replace m2 with (mem_of_state s2); eauto.
      destruct s2; simpl in *; now congruence.
      intros (j__δ' & rs3' & m3' & exec_instr' & inj_pres' & m1_m3' & m2_m3' & rs1_rs3' & st_rel' & incr).

      assert (exists b', rs3' PC = Vptr b' Ptrofs.zero) as [b3' rs3'_PC].
      { pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc.
        assert (delta = 0) by now eapply (delta_zero s ge1 ge3); eauto. subst delta. rewrite Ptrofs.add_zero in *.
        eauto. }
      exploit extcall_arguments_preserved; eauto.
      intros (args' & inj_args & extcall_args').

      exploit external_call_inject_left; eauto using partial_mem_inject.

      intros (j__δ'' & vres' & m3'' & extcall' & inj_res & unchanged1 & unchanged2 &
                incr' & sep & inj_pres'' & m'_m3' & m2_m3'' & rs_rs3' & st_rel'').
      eexists; exists j__δ''; split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_external_call; eauto.
        { specialize (rs_rs3' PC).
          rewrite NEXTPC, rs3'_PC in rs_rs3'.
          inv rs_rs3'. exploit delta_zero; eauto. intros ->.
          exploit find_def_preserved; eauto.
          intros [gd' [? [G ?]]].
          inv G. inv H10. eauto. }

      + eauto.
      + eauto.
      + simpl; eauto.
        replace (mem_of_state s2) with m2; eauto. destruct s2; simpl in *; congruence.
      + inv strong_s1_s3; econstructor; eauto.
        * econstructor; eauto.
          Simpl. inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *; eauto.
        * econstructor; eauto.
          Simpl. inv COMP2; eauto.
          rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *; eauto.
        * eapply regset_rel_return_from_external; eauto.
          eapply Val.offset_ptr_inject; eauto.
      + inv strong_s1_s3; inv weak_s2_s3; inv A; econstructor; eauto.
        * econstructor; eauto.
          assert (cp = callee_comp cp_main st3) as ->.
          { eapply comp_of_state_unique; eauto. }
          Simpl. inv COMP2; eauto.
          rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *; eauto.
        * econstructor; eauto.
          assert (cp = callee_comp cp_main st3) as ->.
          { eapply comp_of_state_unique; eauto. }
          Simpl. inv COMP2; eauto.
          rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *; eauto.
  Qed.

  Lemma step_E0_weak: forall (s2 s2': state),
      Step (semantics W2) s2 E0 s2' ->
      forall (s1 s3: state) j__δ j__oppδ,
        meminj_preserves_globals s δ W1 W3 j__δ ->
        meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
        stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ (mem_of_state s1) (mem_of_state s2) (mem_of_state s3) (stack_of_state s1) (stack_of_state s2) (stack_of_state s3) ->
        strong_equivalence s cp_main ge1 ge3 j__δ δ s1 s3 ->
        weak_equivalence s ge2 ge3 j__oppδ (opposite δ) s2 s3 ->
        exists j__oppδ',
          meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ' /\
            stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ' (mem_of_state s1) (mem_of_state s2') (mem_of_state s3)
              (stack_of_state s1) (stack_of_state s2') (stack_of_state s3) /\
            strong_equivalence s cp_main ge1 ge3 j__δ δ s1 s3 /\
            weak_equivalence s ge2 ge3 j__oppδ' (opposite δ) s2' s3.
  Proof.
    intros s2 s2' H s1 s3 j__left j__right inj_pres1 inj_pres2 st_rel strong_s1_s3 weak_s2_s3.
    simpl in H.
    inv H.

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      assert (f_left: s (has_comp_function f) = δ).
      { inv weak_s2_s3; inv B.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ. }
      exploit exec_instr_preserves_weak; eauto.
      replace m3 with (mem_of_state s3); eauto.
      now destruct s3; simpl in *; congruence.
      intros (j__oppδ' & ? & m'_m3 & st_rel').
      eexists.
      repeat (split; eauto).
      replace (mem_of_state s3) with m3; eauto.
      now destruct s3; simpl in *; congruence.
      inv weak_s2_s3; inv B; econstructor; eauto.
      + constructor; eauto. rewrite NEXTPC; simpl; rewrite <- ALLOWED.
        inv COMP1; eauto.
        * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.
      + constructor; eauto. rewrite NEXTPC; simpl; rewrite <- ALLOWED.
        inv COMP1; eauto.
        * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      assert (f_left: s (has_comp_function f) = δ).
      { inv weak_s2_s3; inv B.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ. }
      eexists.
      repeat (split; eauto).
      replace (mem_of_state s3) with m3; eauto.
      inv weak_s2_s3; inv B; econstructor; eauto.
      + constructor; eauto.
        destruct rd; [erewrite H8 | erewrite H9]; eauto.
        { Simpl. rewrite H0.
          inv COMP1; eauto.
          * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1. }
        { Simpl. rewrite H0.
          inv COMP1; eauto.
          * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1. }
      + constructor; eauto.
        destruct rd; [erewrite H8 | erewrite H9]; eauto.
        { Simpl. inv COMP1; eauto.
          * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1. }
        { Simpl. inv COMP1; eauto.
          * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1. }
      + now destruct s3; simpl in *; congruence.

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      assert (f_left: s (has_comp_function f) = δ).
      { inv weak_s2_s3; inv B.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ. }
      destruct rd; [exploit EXECi | exploit EXECf]; eauto.
      + intros; simpl_before_exists; eexists; repeat (split; eauto).
        { inv weak_s2_s3; inv B; econstructor; eauto.
          + constructor; eauto.
            Simpl. rewrite H0.
            inv COMP1; eauto.
            * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.
          + constructor; eauto.
            Simpl. rewrite H0.
            inv COMP1; eauto.
            * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.
        }
        { inv weak_s2_s3; inv B; econstructor; eauto.
          + constructor; eauto.
            Simpl. rewrite H0.
            inv COMP1; eauto.
            * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.
          + constructor; eauto.
            Simpl. rewrite H0.
            inv COMP1; eauto.
            * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.
        }
      + intros; simpl_before_exists; eexists; repeat (split; eauto).
        { inv weak_s2_s3; inv B; econstructor; eauto.
          + constructor; eauto.
            Simpl. rewrite H0.
            inv COMP1; eauto.
            * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.
          + constructor; eauto.
            Simpl. rewrite H0.
            inv COMP1; eauto.
            * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.
        }
        { inv weak_s2_s3; inv B; econstructor; eauto.
          + constructor; eauto.
            Simpl. rewrite H0.
            inv COMP1; eauto.
            * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.
          + constructor; eauto.
            Simpl. rewrite H0.
            inv COMP1; eauto.
            * now rewrite H0; simpl; unfold Genv.find_comp_of_block; rewrite H1.
        }

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      assert (f_left: s (has_comp_function f) = δ).
      { inv weak_s2_s3; inv B.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ. }
      exploit (exec_instr_preserves_weak j__left j__right f); eauto.
      replace m3 with (mem_of_state s3); eauto.
      now destruct s3; simpl in *; congruence.
      intros (j__right' & ? & m'_m3 & st_rel').
      assert (st' = st2 /\ rs'' = rs' /\ m'' = m') as [? [? ?]]; [| subst st'].
      { unfold update_stack_call in STUPD.
        inv EV; auto. unfold Genv.type_of_call in *.
        rewrite NEXTPC in STUPD.
        simpl in STUPD. destruct (flowsto_dec); try congruence.
        destruct cp_eq_dec eqn:X; try congruence.
        inv STUPD; eauto.
        inv f0.
        - exploit no_bottom2; eauto.
          unfold Genv.find_comp_of_block in *. rewrite NEXT_INT in *.
          eauto. contradiction.
        - exploit (no_top2 b); eauto. contradiction.
        - contradiction. }
      subst rs'' m''.
      eexists.
      repeat (split; eauto).
      replace (mem_of_state s3) with m3; eauto.
      now destruct s3; simpl in *; congruence.
      inv weak_s2_s3; inv B; econstructor; eauto.
      + inv EV.
        unfold Genv.type_of_call in H5.
        destruct flowsto_dec as [F|]; try congruence.
        inv F.
        * unfold Genv.find_comp_of_block in H7.
          rewrite NEXT_INT in H7.
          exploit no_bottom2; eauto. contradiction.

          (* eapply comp_of_state_external. *)
          (* { rewrite invalidate_call_PC, NEXTPC. auto. } *)
          (* { unfold invalidate_call; simpl. *)
          (*   inv COMP1; eauto. { erewrite exec_instr_call_pc; eauto. now rewrite H0. } *)
          (*   rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *. *)
          (*   exploit no_bottom2; eauto. contradiction. } *)
          (* inv COMP1; eauto. *)
          (* rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *. *)
          (* reflexivity. *)
        * exploit (no_top2 b); eauto. contradiction.
        * eapply comp_of_state_internal.
          { unfold invalidate_call; simpl.
            inv COMP1; eauto. rewrite NEXTPC; simpl; rewrite H8.
            rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
            reflexivity. }
          inv COMP1; eauto.
      + inv EV.
        unfold Genv.type_of_call in H5.
        destruct flowsto_dec as [F|]; try congruence.
        inv F.
        * unfold Genv.find_comp_of_block in H7.
          rewrite NEXT_INT in H7.
          exploit no_bottom2; eauto. contradiction.
        * exploit (no_top2 b); eauto. contradiction.
        * eapply comp_of_state_internal.
          { unfold invalidate_call; simpl.
            inv COMP1; eauto. rewrite NEXTPC; simpl; rewrite H8.
            rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
            reflexivity. }
          inv COMP1; eauto.

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      exploit exec_instr_preserves_weak; eauto.
      { inv weak_s2_s3; inv B.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ. }
      replace m3 with (mem_of_state s3); eauto.
      now destruct s3; simpl in *; congruence.
      intros (j__right' & ? & m'_m3 & st_rel').

      eexists.
      repeat (split; eauto).
      replace (mem_of_state s3) with m3; eauto.
      now destruct s3; simpl in *; congruence.
      inv weak_s2_s3; inv B; econstructor; eauto.
      + assert (cp0 = comp_of f) as ->.
        { inv COMP1; eauto.
          - now rewrite H0 in *; simpl in *;
              unfold Genv.find_comp_of_block in *; rewrite H1 in *. }
        constructor; eauto.
      + assert (cp0 = comp_of f) as ->.
        { inv COMP1; eauto.
          - now rewrite H0 in *; simpl in *;
              unfold Genv.find_comp_of_block in *; rewrite H1 in *. }
        constructor; eauto.

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      eexists.
      repeat (split; eauto).
      inv weak_s2_s3; inv B; econstructor; eauto.
      + econstructor; eauto.
        rewrite invalidate_return_PC; eauto. inv COMP1; eauto.
      + rewrite ATPC in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite FD in *.
        eapply no_top2; eauto.
      + rewrite ATPC in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite FD in *.
        eapply no_bottom2; eauto.
      + econstructor; eauto.
        rewrite invalidate_return_PC; eauto. inv COMP1; eauto.
      + rewrite ATPC in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite FD in *.
        eapply no_top2; eauto.
      + rewrite ATPC in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite FD in *.
        eapply no_bottom2; eauto.

    - (* return-cross: impossible *)
      exfalso. simpl in *.
      inv strong_s1_s3; inv weak_s2_s3; inv EV.
      + assert (rec_cp = cp) as -> by now inv COMP0.
        inv st_rel; simpl in *; subst; try congruence.
        inv H7; simpl in *; eauto.
        * destruct (flowsto_dec); try congruence.
          inv f; congruence.
        * destruct (flowsto_dec); try congruence.
          inv f; congruence.
      + assert (rec_cp = cp) as -> by now inv COMP0.
        inv st_rel; simpl in *; subst; try congruence.
        inv H7; simpl in *; eauto.
        * destruct (flowsto_dec); try congruence.
          inv f; congruence.
        * destruct (flowsto_dec); try congruence.
          inv f; congruence.

    - exploit weak_equivalence_inv; eauto.

      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A. simpl.

      exploit extcall_preserves_mem_rel_opp_side1; eauto.
      { inv weak_s2_s3; inv B.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ. }
      { simpl in *. destruct s3; inv B; eapply stack_rel_comm; eauto. }
      intros [m'_m3' st_rel'].

      eexists; repeat (split; eauto).
      replace (mem_of_state s3) with m3; eauto.
      { simpl in *. destruct s3; inv B; eapply stack_rel_comm in st_rel'.
        now destruct δ; assumption.
        now destruct δ; assumption. }
      destruct s3; simpl in *; now congruence.
      (* eexists; do 3 (split; eauto). *)
      inv weak_s2_s3; inv B; (econstructor; eauto).
      + econstructor; eauto.
        rewrite nextinstr_pc_return_builtin_value in *; eauto.
        inv COMP1; eauto. now rewrite H0.
      + econstructor; eauto.
        rewrite nextinstr_pc_return_builtin_value in *; eauto.
        inv COMP1; eauto. now rewrite H0.

    - exploit weak_equivalence_inv; eauto. intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A. simpl in *.

      assert (f_left: s (has_comp_function f) = δ).
      { inv weak_s2_s3; inv B.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ.
        - inv COMP1; eauto.
          rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *.
          clear -SIDE. simpl in SIDE; now destruct δ. }
      exploit exec_instr_preserves_weak; eauto.
      replace m3 with (mem_of_state s3); eauto.
      now destruct s3; simpl in *; congruence.
      intros (j__oppδ' & ? & m'_m3 & st_rel').

      exploit extcall_preserves_mem_rel_opp_side1; eauto.
      now destruct δ.
      clear st_rel.
      { simpl in *. destruct s3; inv B; eapply stack_rel_comm; eauto. }

      intros [m'_m3' st_rel''].

      eexists; repeat (split; eauto).
      replace (mem_of_state s3) with m3; eauto.
      (* { simpl in *. destruct s3; inv B; eauto. eapply stack_rel_comm; eauto. } *)
      { simpl in *. destruct s3; inv B; eapply stack_rel_comm in st_rel''.
        clear st_rel'.
        now destruct (s (has_comp_function f)); assumption.
        now destruct (s (has_comp_function f)); assumption. }
      now destruct s3; simpl in *; congruence.
      inv weak_s2_s3; inv B; econstructor; eauto.
      + econstructor; eauto. Simpl.
        inv COMP1.
        rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *; eauto.
      + econstructor; eauto. Simpl.
        inv COMP1.
        rewrite H0 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H1 in *; eauto.
  Qed.

  Lemma step_t: forall (s1 s1': state) (s2 s2': state) e,
      Step (semantics W1) s1 (e :: nil) s1' ->
      Step (semantics W2) s2 (e :: nil) s2' ->
      forall (s3: state) j__δ j__oppδ,
        meminj_preserves_globals s δ W1 W3 j__δ ->
        meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
        stack_rel s cp_main ge1 ge2 ge3 δ j__δ j__oppδ (mem_of_state s1) (mem_of_state s2) (mem_of_state s3) (stack_of_state s1) (stack_of_state s2) (stack_of_state s3) ->
        strong_equivalence s cp_main ge1 ge3 j__δ δ s1 s3 ->
        weak_equivalence s ge2 ge3 j__oppδ (opposite δ) s2 s3 ->
        exists s3' j__δ' j__oppδ',
          Plus (semantics W3) s3 (e :: nil) s3' /\
            meminj_preserves_globals s δ W1 W3 j__δ' /\
            meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ' /\
            stack_rel s cp_main ge1 ge2 ge3 δ j__δ' j__oppδ' (mem_of_state s1') (mem_of_state s2') (mem_of_state s3') (stack_of_state s1') (stack_of_state s2') (stack_of_state s3') /\
            ((strong_equivalence s cp_main ge1 ge3 j__δ' δ s1' s3' /\
                weak_equivalence s ge2 ge3 j__oppδ' (opposite δ) s2' s3') \/
               (weak_equivalence s ge1 ge3 j__δ' δ s1' s3' /\
                  strong_equivalence s cp_main ge2 ge3 j__oppδ' (opposite δ) s2' s3')).
  Proof.
    intros s1 s1' s2 s2' e step1 step2 s3 j__δ j__oppδ inj_pres_δ inj_pres_opp_δ
      st_rel strong_s1_s3 weak_s2_s3.
    simpl in step1, step2.

    inv step1; inv step2;
      try now (do 2 match goal with
                 | H: call_trace _ _ _ _ _ _ (?e :: nil) |- _ => inv H
                 | H: return_trace _ _ _ _ _ (?e :: nil) |- _ => inv H
                 | H: external_call _ _ _ _ _ (?e :: nil) _ _ |- _ => eapply ec_no_crossing in H;
                                                                   eauto using external_call_spec
                 end); try contradiction.
    (* Should get 6 cases *)

    - (* Call *)
      exploit strong_equiv_state_internal_inv; eauto.
      rename f' into nextf.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        unfold Genv.find_funct_ptr in H0. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''.
        unfold Genv.find_def in R; rewrite R.
        simpl in *; rewrite side_f; now destruct side_eq. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A). injection A; intros -> -> ->; clear A.
      exploit exec_instr_preserved; simpl; eauto.
      intros (j__δ' & rs3' & m3' & exec_instr' & inj_pres' & m1_m3' & m2_m3' & rs1_rs3' & st_rel' & incr).
      assert (side_f0: s (has_comp_function f0) = δ).
      { clear -side_f EV EV0.
        inv EV; inv EV0. simpl; congruence. }
      exploit exec_instr_preserves_weak; simpl; [| |exact side_f0 | | | | | ]; eauto.
      intros (j__oppδ' & ? & m'0_m3' & st_rel'').

      assert (exists b', rs3' PC = Vptr b' Ptrofs.zero) as [b3' rs3'_PC].
      { pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc.
        assert (delta = 0) by now eapply (delta_zero s ge1 ge3); eauto. subst delta. rewrite Ptrofs.add_zero in *.
        eauto. }

      exploit call_arguments_preserved; eauto.
      intros [args' [inj_args call_args']].
      remember (Genv.find_comp_of_block ge1 b') as cp'.
      remember (Genv.find_comp_of_block ge2 b'0) as cp'0.


      assert (diff_comp: not (flowsto cp' (comp_of f))).
      { clear -EV.
        inv EV; eauto.
        unfold Genv.type_of_call in H0.
        destruct flowsto_dec; try congruence. }

      assert (CP'_bottom: cp' <> bottom).
      { clear -diff_comp. intros ->. apply diff_comp; auto with comps. }
      assert (CP'_top: cp' <> top).
      { subst cp'. unfold Genv.find_comp_of_block.
        clear -no_top1 no_top1'.
        destruct (Genv.find_def ge1 b') as [[[] |] |] eqn:EQ; try discriminate.
        eapply no_top1; eauto.
        eapply no_top1'; eauto. }


      exploit (exec_instr_call_pc ge1 f i); eauto.
      exploit (exec_instr_call_pc ge2 f0 i0); eauto.
      exploit (exec_instr_call_pc ge3 f i); eauto.
      rewrite eq_pc', H4, H; simpl.
      intros rs3'_X1 rs'0_X1 rs'_X1.

      assert (Genv.find_comp_in_genv ge3 (rs3' PC) = cp') as NEXTCOMP'.
      { erewrite <- (find_comp_preserved s W1 W3); eauto using delta_zero.
        rewrite NEXTPC; eauto.
        congruence. }
      simpl in NEXTCOMP'.

      assert (cp'0 = cp') as ->.
      { clear -EV EV0.
        inv EV; inv EV0. congruence. }


      assert (diff_comp': not (flowsto cp' (comp_of f0))).
      { clear -EV0.
        inv EV0; eauto.
        unfold Genv.type_of_call in H0.
        destruct flowsto_dec; try congruence. }

      assert (same_sig: sig = sig0).
      { exploit CALLSIG; eauto.
        { clear -EV. inv EV; auto. }
        intros [fd [Hfd ->]].
        exploit CALLSIG0; eauto.
        { clear -EV0. inv EV0; auto. }
        intros [fd0 [Hfd0 ->]].
        (* clear -STUPD STUPD0. *)
        clear -match_W1_W3 match_W2_W3 EV EV0 Hfd Hfd0 inj_pres' inj_pres_opp_δ.
        inv EV; inv EV0. inv H1; inv H12.
        apply Genv.invert_find_symbol in H2.
        apply Genv.invert_find_symbol in H13.
        apply (symbols_inject2 _ _ _ _ _ inj_pres') in H2 as [b3 [X Y]].
        apply (symbols_inject2 _ _ _ _ _ inj_pres_opp_δ) in H13 as [b3' [X' Y']].
        assert (b3' = b3) by congruence; subst b3'.
        (* rewrite Genv.find_funct_ptr_iff in Hfd, Hfd0. *)
        eapply (defs_inject _ _ _ _ _ inj_pres') in Hfd as [gd [find_gd [_ [match_gd ?]]]]; eauto.
        eapply (defs_inject _ _ _ _ _ inj_pres_opp_δ) in Hfd0 as [gd0 [find_gd0 [_ [match_gd0 ?]]]]; eauto.
        rewrite find_gd in find_gd0.
        assert (gd0 = gd) by congruence; subst gd0.
        inv match_gd; inv match_gd0. inv H4; inv H7; auto.
        unfold kept_genv. rewrite H13. unfold Genv.find_def in Hfd0; rewrite Hfd0. auto.
        unfold kept_genv. rewrite H2. unfold Genv.find_def in Hfd; rewrite Hfd. auto.
      }
      subst sig0.
      assert (G: exists dra1 dsp1 dra2 dsp2 st3' j__δ'' j__oppδ'' rs3'' m3'',
                 st' = Stackframe b sig cp' (rs' X2) (Ptrofs.add ofs Ptrofs.one) dra1 dsp1 :: st /\
                   st'0 = Stackframe b0 sig cp' (rs'0 X2) (Ptrofs.add ofs0 Ptrofs.one) dra2 dsp2 :: st2 /\
                   update_stack_call ge3 st3 sig (comp_of f) rs3' m3' = Some (st3', rs3'', m3'') /\
                   meminj_preserves_globals s δ W1 W3 j__δ'' /\
                   meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ'' /\
                   mem_rel s (Genv.globalenv W1) (Genv.globalenv W3) j__δ'' δ m'' m3'' /\
                   mem_rel s (Genv.globalenv W2) (Genv.globalenv W3) j__oppδ'' (opposite δ) m''0 m3'' /\
                   inject_incr j__δ' j__δ'' /\ inject_incr j__oppδ' j__oppδ'' /\
                   stack_rel s cp_main ge1 ge2 ge3 δ j__δ'' j__oppδ'' m'' m''0 m3'' st' st'0 st3' /\
                   rs3'' PC = rs3' PC /\
                   (s cp' = δ -> regset_rel j__δ'' rs'' rs3'') /\
                   (s cp' = opposite δ -> regset_rel j__oppδ'' (invalidate_call rs''0 sig) (invalidate_call rs3'' sig))).
      { unfold update_stack_call in STUPD, STUPD0.
        rewrite NEXTPC in STUPD; simpl in STUPD. rewrite <- Heqcp' in STUPD.
        destruct (flowsto_dec cp' (has_comp_function f)); try contradiction.
        rewrite NEXTPC0 in STUPD0; simpl in STUPD0. rewrite <- Heqcp'0 in STUPD0.
        destruct (flowsto_dec cp' (has_comp_function f0)); try contradiction.
        rewrite rs'_X1 in STUPD. rewrite rs'0_X1 in STUPD0.
        destruct (Mem.alloc m' cp' 0 0) eqn:alloc1,
            (Mem.alloc m0 cp' 0 0) eqn:alloc1'.
        inv STUPD.
        remember (Genv.find_comp_of_block ge1 b') as cp'.
        remember (Genv.find_comp_of_block ge2 b'0) as cp'0.
        destruct (Mem.alloc m'0 cp' 0 0) eqn:alloc2,
            (Mem.alloc m4 cp' 0 0) eqn:alloc2'; inv STUPD0.
        remember (Genv.find_comp_of_block ge1 b') as cp'.
        remember (Genv.find_comp_of_block ge2 b'0) as cp'0.
        destruct (side_eq (s cp') (s (comp_of f))) as [e1 | n1].
        - eapply (alloc_preserves_rel s W1 W2 W3) in alloc1 as alloc1''; eauto using match_prog_unique.
          destruct alloc1'' as (j0 & temp_m3 & dra3 & alloc3 & ? & ? & R1 & ? & ? & ? & S).
          eapply (alloc_preserves_rel s W1 W2 W3) in alloc1' as alloc1''; eauto using match_prog_unique.
          destruct alloc1'' as (j & m3'' & dsp3 & alloc3' & ? & ? & R2 & ? & ? & ? & S').
          rewrite <- e1 in *.
          exploit (alloc_preserves_weak s (opposite (s cp')) W2 norepet2 ge1 W3 cp_main j__oppδ' j cp' 0 0 m'0); eauto.
          eapply stack_rel_comm; eauto.
          intros (j0' & ? & R1' & ? & SS).
          exploit (alloc_preserves_weak s (opposite (s cp')) W2 norepet2 ge1 W3 cp_main j0' j cp' 0 0 m4); eauto.
          intros (j' & ? & R2' & ? & SS').
          eapply stack_rel_comm in SS'.
          replace (opposite (opposite (s cp'))) with (s cp') in * by now destruct s.
          assert (rs' X2 = rs X2) as X2_1.
          { clear -H2 H3. destruct i; try discriminate; simpl in *.
            destruct (Genv.allowed_addrof_b); inv H2; Simpl.
            inv H2; Simpl. }
          assert (rs'0 X2 = rs2 X2) as X2_2.
          { clear -H7 H8. destruct i0; try discriminate; simpl in *.
            destruct (Genv.allowed_addrof_b); inv H7; Simpl.
            inv H7; Simpl. }
          assert (rs3' X2 = rs3 X2) as X2_3.
          { clear -exec_instr' H3. destruct i; try discriminate; simpl in *.
            destruct (Genv.allowed_addrof_b); inv exec_instr'; Simpl.
            inv exec_instr'; Simpl. }
          specialize (rs1_rs3 X2) as X2_inj; rewrite <- X2_1, <- X2_3 in X2_inj.
          destruct (rs' X2) eqn:rs'_X2; try discriminate.
          destruct (rs'0 X2) eqn:rs'0_X2; try discriminate.

          destruct (Mem.set_perm m1 b6 Readable) eqn:set_perm1; try discriminate.
          destruct (Mem.set_perm m5 b7 Readable) eqn:set_perm2; try discriminate.
          inv H11. inv H12.

          (* inv rs1_rs3. *)
          (* inv rs1_rs3; try rewrite H27, H28 in *; try congruence. *)
          (* specialize (rs) *)
          (* destruct (rs'0 X2); try discriminate. *)
          (* eapply (set_perm_ok s W1 W2 W3) with (v0 := rs'0 X2) in SS' as [? [? ?]]; eauto using match_prog_unique; try now destruct s. *)
          unfold update_stack_call.
          rewrite NEXTCOMP'. simpl. destruct flowsto_dec; try contradiction.
          rewrite alloc3; simpl; rewrite alloc3'; simpl.
          inv X2_inj.
          eapply (set_perm_preserves_rel s W1 W2 W3) in SS'; eauto using match_prog_unique.
          destruct SS' as [m3''' [set_perm3 [mrel1 [mrel2 strel]]]].
          rewrite set_perm3, rs3'_X1.

          (* eapply stack_rel_comm in SS'; eauto. *)
          (* now destruct s. *)
          (* eapply (set_perm_preserves_rel s W1 W2 W3) in SS'; eauto using match_prog_unique. *)
          (* destruct SS' as [? [? ?]]. *)

          do 5 eexists; exists j; exists j'; do 2 eexists.
          do 3 (split; eauto).
          (* + unfold update_stack_call. *)
          (*   rewrite NEXTCOMP'. simpl. destruct flowsto_dec; try contradiction. *)
          (*   rewrite alloc3; simpl; rewrite alloc3'; simpl. *)
          (*   rewrite rs3'_X1. reflexivity. *)
          + Simpl. do 7 (split; eauto using inject_incr_trans); [| split; [| split]; eauto].
            * econstructor; eauto using inject_incr_stack_rel1, inject_incr_stack_rel2.
              eapply stackframe_related_δ with (cp := comp_of f); eauto.
              -- eapply Genv.find_funct_ptr_iff in find_funct.
                 erewrite Genv.find_funct_ptr_find_comp_of_block; eauto. reflexivity.
              -- specialize (H19 X1). rewrite rs'_X1, rs3'_X1 in H19. eauto.
              -- rewrite e1. destruct side_eq; try now congruence.
                 eapply val_inject_incr; eauto. econstructor; eauto.
                 eapply H15; eauto. reflexivity. rewrite Ptrofs.add_zero. reflexivity.
              -- rewrite e1. destruct side_eq; try now congruence.
                 econstructor.
                 eapply H20; eauto. reflexivity. rewrite Ptrofs.add_zero. reflexivity.
              -- { assert (m = m').
                   { clear -H2 H3.
                     destruct i; try discriminate; simpl in *.
                     destruct Genv.allowed_addrof_b; inv H2; auto.
                     inv H2; auto. } subst m'.
                   apply incr, H16, H21 in H27.
                   clear -ARGS NO_CROSS_PTR n H18 H19 alloc1 alloc1' m1_m3' H2 rs'_X2 H26 H27 set_perm1 mrel1 H3.
                   rename H18 into m1_m3. rename H19 into rs1_rs3.
                   rename H2 into exec_instr1.
                   rename H3 into sigcall.
                   intros ? ? G ? G'.
                   split.
                   { intros ? ? A; inv A.
                     (* assert (R: rs' X2 = rs X2). *)
                     (* { clear -exec_instr1 sigcall. destruct i; try discriminate; simpl in *. *)
                     (*   destruct Genv.allowed_addrof_b; auto. inv exec_instr1. *)
                     (*   Simpl. inv exec_instr1. *)
                     (*   inv exec_instr1. Simpl. } *)
                     clear - G ARGS rs'_X2 set_perm1 alloc1' alloc1.
                     destruct G as [G | [[l G] | [l G]]].
                     - unfold call_arguments in ARGS.
                       pose proof (list_forall2_in_left _ ARGS G) as [arg [IN P]].
                       inv P. inv H0.
                       rewrite rs'_X2 in H4. simpl in H4.
                       eapply Mem.load_alloc_other in H4; eauto.
                       eapply Mem.load_alloc_other in H4; eauto.
                       eapply Mem.load_set in H4; eauto.
                       eapply Mem.load_valid_access in H4 as [? [? ?]]. eauto.
                       constructor.
                     - unfold call_arguments in ARGS.
                       pose proof (list_forall2_in_left _ ARGS G) as [arg [IN P]].
                       inv P. inv H1.
                       rewrite rs'_X2 in H5. simpl in H5.
                       eapply Mem.load_alloc_other in H5; eauto.
                       eapply Mem.load_alloc_other in H5; eauto.
                       eapply Mem.load_set in H5; eauto.
                       eapply Mem.load_valid_access in H5 as [? [? ?]]. eauto.
                       constructor.
                     - unfold call_arguments in ARGS.
                       pose proof (list_forall2_in_left _ ARGS G) as [arg [IN P]].
                       inv P. inv H3.
                       rewrite rs'_X2 in H5. simpl in H5.
                       eapply Mem.load_alloc_other in H5; eauto.
                       eapply Mem.load_alloc_other in H5; eauto.
                       eapply Mem.load_set in H5; eauto.
                       eapply Mem.load_valid_access in H5 as [? [? ?]]. eauto.
                       constructor.
                   }
                   intros ? G''.

                   exploit delta_zero; eauto. intros ->.
                   eapply Mem.load_inject in G'' as G'''; eauto using partial_mem_inject.
                   destruct G''' as [v2 [load' v_v2]].
                   rewrite !Ptrofs.add_zero, Z.add_0_r in *.
                   assert (not_ptr v).
                   { destruct G as [G | [[l G] | [l G]]].
                     - unfold call_arguments in ARGS.
                       exploit list_forall2_in_left; eauto.
                       intros [arg [IN P]].
                       inv P. inv H0.
                       assert (arg = v).
                       { rewrite rs'_X2 in *; simpl in *.
                         eapply Mem.load_Some_None in H4.

                         eapply Mem.load_set' in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         congruence.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor.
                         eapply Mem.valid_block_alloc; eauto.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor. constructor.
                         intros ? ?.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.load_valid_access; eauto.
                       }
                       subst arg.
                       exploit NO_CROSS_PTR; eauto. simpl. destruct flowsto_dec; try now auto.
                       intros R. eapply Forall_forall in R; eauto.
                     - unfold call_arguments in ARGS.
                       exploit list_forall2_in_left; eauto.
                       intros [arg [IN P]].
                       inv P. inv H1.
                       assert (vhi = v).
                       { rewrite rs'_X2 in *; simpl in *.
                         eapply Mem.load_Some_None in H5.
                         eapply Mem.load_set' in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         congruence.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor.
                         eapply Mem.valid_block_alloc; eauto.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor. constructor.
                         intros ? ?.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.load_valid_access; eauto. }
                       subst vhi.
                       exploit NO_CROSS_PTR; eauto. simpl. destruct flowsto_dec; try now auto.

                       intros R. rewrite Forall_forall in R.
                       apply R in IN.
                       destruct v; simpl in *; try now auto.
                     - unfold call_arguments in ARGS.
                       exploit list_forall2_in_left; eauto.
                       intros [arg [IN P]].
                       inv P. inv H3.
                       assert (vlo = v).
                       { rewrite rs'_X2 in *; simpl in *.
                         eapply Mem.load_Some_None in H5.
                         eapply Mem.load_set' in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         congruence.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor.
                         eapply Mem.valid_block_alloc; eauto.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor. constructor.
                         intros ? ?.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.load_valid_access; eauto. }
                       subst vlo.
                       exploit NO_CROSS_PTR; eauto. simpl. destruct flowsto_dec; try now auto.

                       intros R. rewrite Forall_forall in R.
                       apply R in IN.
                       destruct v, vhi; simpl in *; try now auto. }
                   inv v_v2; simpl in *; split; eauto; contradiction.
                 }
              -- { assert (m = m').
                   { clear -H2 H3.
                     destruct i; try discriminate; simpl in *.
                     destruct Genv.allowed_addrof_b; inv H2; auto.
                     inv H2; auto. } subst m'.
                   assert (m'0 = m2).
                   { clear -H7 H8.
                     destruct i0; try discriminate; simpl in *.
                     destruct Genv.allowed_addrof_b; inv H7; auto.
                     inv H7; auto. } subst m'0.
                   assert (CROSS: Genv.type_of_call (comp_of f) (Genv.find_comp_of_block ge1 b') = Genv.CrossCompartmentCall).
                   { simpl. destruct flowsto_dec; try congruence. }
                   specialize (NO_CROSS_PTR CROSS).
                   assert (args0 = args).
                   { clear -EV EV0 NO_CROSS_PTR. inv EV; inv EV0; auto.
                     clear -H8 H14 NO_CROSS_PTR. revert H8 H14.
                     generalize (sig_args sig).
                     generalize dependent args0. generalize dependent args. induction vl.
                     - intros; inv H8; inv H14; eauto.
                     - intros; inv H8; inv H14; eauto.
                       assert (v0 = v1).
                       { inv H1; inv H6; eauto. inv NO_CROSS_PTR; eauto. now simpl in *. }
                       subst v1.
                       inv NO_CROSS_PTR.
                       exploit IHvl; eauto. intros ->; eauto. }
                   subst args0.
                   intros ? ? G ? G'.
                   split.
                   { intros ? ? A; inv A.
                     assert (R: rs'0 X2 = rs2 X2).
                     { clear -H7 H8. destruct i0; try discriminate; simpl in *.
                       destruct Genv.allowed_addrof_b; auto. inv H7.
                       Simpl. inv H7.
                       inv H7. Simpl. }
                     clear -CROSS G ARGS0 R X2_2 set_perm2 alloc2' alloc2.
                     destruct G as [G | [[l G] | [l G]]].
                     - unfold call_arguments in ARGS0.
                       pose proof (list_forall2_in_left _ ARGS0 G) as [arg [IN P]].
                       inv P. inv H0.
                       rewrite R, <- X2_2 in H4. simpl in H4.
                       eapply Mem.load_alloc_other in H4; eauto.
                       eapply Mem.load_alloc_other in H4; eauto.
                       eapply Mem.load_set in H4; eauto.
                       eapply Mem.load_valid_access in H4 as [? [? ?]]. eauto.
                       constructor.
                     - unfold call_arguments in ARGS0.
                       pose proof (list_forall2_in_left _ ARGS0 G) as [arg [IN P]].
                       inv P. inv H1.
                       rewrite R, <- X2_2 in H5. simpl in H5.
                       eapply Mem.load_alloc_other in H5; eauto.
                       eapply Mem.load_alloc_other in H5; eauto.
                       eapply Mem.load_set in H5; eauto.
                       eapply Mem.load_valid_access in H5 as [? [? ?]]. eauto.
                       constructor.
                     - unfold call_arguments in ARGS0.
                       pose proof (list_forall2_in_left _ ARGS0 G) as [arg [IN P]].
                       inv P. inv H3.
                       rewrite R, <- X2_2 in H5. simpl in H5.
                       eapply Mem.load_alloc_other in H5; eauto.
                       eapply Mem.load_alloc_other in H5; eauto.
                       eapply Mem.load_set in H5; eauto.
                       eapply Mem.load_valid_access in H5 as [? [? ?]]. eauto.
                       constructor.
                   }
                   intros ? G''.
                   assert (G''': Mem.loadv (chunk_of_type ty) m''
                                   (Val.offset_ptr (Vptr b6 i1) (Ptrofs.repr bofs)) top
                                 = Some v).
                   { destruct G as [G | [[l G] | [l G]]].
                     - unfold call_arguments in ARGS, ARGS0.
                       clear call_args'.
                       pose proof (parallel_list_forall2_in_left _ ARGS ARGS0 G)
                         as [arg [IN [P1 P2]]].
                       inv P1; inv P2.
                       inv H12; inv H28.
                       assert (arg = v).
                       { rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                         eapply Mem.load_Some_None in H31.

                         eapply Mem.load_set' in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         congruence.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor.
                         eapply Mem.valid_block_alloc; eauto.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor. constructor.
                         intros ? ?.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.load_valid_access; eauto. }
                       subst arg.
                       rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H32.
                       eapply Mem.load_set; eauto. constructor.
                       erewrite Mem.load_alloc_unchanged with (m1 := m0); eauto.
                       erewrite Mem.load_alloc_unchanged with (m1 := m); eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                     - unfold call_arguments in ARGS, ARGS0.
                       clear call_args'.
                       pose proof (parallel_list_forall2_in_left _ ARGS ARGS0 G)
                         as [arg [IN [P1 P2]]].
                       inv P1; inv P2.
                       assert (vhi = vhi0).
                       {  exploit eq_distributes_longofwords; eauto.
                          rewrite H29.
                          eapply Forall_forall; eauto.
                          eapply Forall_forall; eauto.
                          now intros [].
                       }
                       subst vhi0.
                       inv H28; inv H31.
                       assert (vhi = v).
                       { rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                         eapply Mem.load_Some_None in H34.

                         eapply Mem.load_set' in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         congruence.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor.
                         eapply Mem.valid_block_alloc; eauto.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor. constructor.
                         intros ? ?.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.load_valid_access; eauto. }
                       subst vhi.
                       rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H35.
                       eapply Mem.load_set; eauto. constructor.
                       erewrite Mem.load_alloc_unchanged with (m1 := m0); eauto.
                       erewrite Mem.load_alloc_unchanged with (m1 := m); eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                     - unfold call_arguments in ARGS, ARGS0.
                       clear call_args'.
                       pose proof (parallel_list_forall2_in_left _ ARGS ARGS0 G)
                         as [arg [IN [P1 P2]]].
                       inv P1; inv P2.
                       assert (vlo = vlo0).
                       {  exploit eq_distributes_longofwords; eauto.
                          rewrite H29.
                          eapply Forall_forall; eauto.
                          eapply Forall_forall; eauto.
                          now intros [].
                       }
                       subst vlo0.
                       inv H30; inv H32.
                       assert (vlo = v).
                       { rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                         eapply Mem.load_Some_None in H34.

                         eapply Mem.load_set' in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         congruence.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor.
                         eapply Mem.valid_block_alloc; eauto.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor. constructor.
                         intros ? ?.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.load_valid_access; eauto. }
                       subst vlo.
                       rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H35.
                       eapply Mem.load_set; eauto. constructor.
                       erewrite Mem.load_alloc_unchanged with (m1 := m0); eauto.
                       erewrite Mem.load_alloc_unchanged with (m1 := m); eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. }

                   clear G''; rename G''' into G''.
                   apply incr, H16, H21 in H27.
                   clear -ARGS NO_CROSS_PTR n H18 H19 alloc1 alloc1' m1_m3' H2 rs'_X2 H26 H27 set_perm1 mrel1 G G' G''.
                   rename H18 into m1_m3. rename H19 into rs1_rs3.
                   rename H2 into exec_instr1.

                   exploit delta_zero; eauto. intros ->.
                   eapply Mem.load_inject in G'' as G'''; eauto using partial_mem_inject.
                   destruct G''' as [v2 [load' v_v2]].
                   rewrite !Ptrofs.add_zero, Z.add_0_r in *.
                   assert (not_ptr v).
                   { destruct G as [G | [[l G] | [l G]]].
                     - unfold call_arguments in ARGS.
                       exploit list_forall2_in_left; eauto.
                       intros [arg [IN P]].
                       inv P. inv H0.
                       assert (arg = v).
                       { rewrite rs'_X2 in *; simpl in *.
                         eapply Mem.load_Some_None in H4.

                         eapply Mem.load_set' in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         congruence.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor.
                         eapply Mem.valid_block_alloc; eauto.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor. constructor.
                         intros ? ?.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.load_valid_access; eauto.
                       }
                       subst arg.
                       eapply Forall_forall in NO_CROSS_PTR; eauto.
                     - unfold call_arguments in ARGS.
                       exploit list_forall2_in_left; eauto.
                       intros [arg [IN P]].
                       inv P. inv H1.
                       assert (vhi = v).
                       { rewrite rs'_X2 in *; simpl in *.
                         eapply Mem.load_Some_None in H5.
                         eapply Mem.load_set' in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         congruence.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor.
                         eapply Mem.valid_block_alloc; eauto.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor. constructor.
                         intros ? ?.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.load_valid_access; eauto. }
                       subst vhi.
                       rewrite Forall_forall in NO_CROSS_PTR.
                       apply NO_CROSS_PTR in IN.
                       destruct v; simpl in *; try now auto.
                     - unfold call_arguments in ARGS.
                       exploit list_forall2_in_left; eauto.
                       intros [arg [IN P]].
                       inv P. inv H3.
                       assert (vlo = v).
                       { rewrite rs'_X2 in *; simpl in *.
                         eapply Mem.load_Some_None in H5.
                         eapply Mem.load_set' in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         erewrite Mem.load_alloc_unchanged in G''; eauto.
                         congruence.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor.
                         eapply Mem.valid_block_alloc; eauto.
                         eapply Mem.valid_access_valid_block; eauto.
                         eapply Mem.valid_access_implies; eauto.
                         eapply Mem.load_valid_access; eauto.
                         constructor. constructor.
                         intros ? ?.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.perm_alloc_1; eauto.
                         eapply Mem.load_valid_access; eauto. }
                       subst vlo.
                       rewrite Forall_forall in NO_CROSS_PTR.
                       apply NO_CROSS_PTR in IN.
                       destruct v, vhi; simpl in *; try now auto. }
                   inv v_v2; simpl in *; split; eauto; contradiction.
                 }
              -- rewrite <- X2_1 in *.
                 destruct (SP_HAS_PTR) as [? [? ?]].
                 simpl. now destruct flowsto_dec.
                 simpl. split; auto. unfold Mem.set_perm in set_perm1.
                 unfold Mem.valid_block. clear -set_perm1. destruct plt; try discriminate.
                 inv set_perm1. auto.
                 clear -set_perm1. revert set_perm1.
                 unfold Mem.set_perm. unfold Mem.perm. intros ?. destruct plt; try discriminate. inv set_perm1.
                 simpl.
                 rewrite PMap.gss; auto. intros ? ?.
                 destruct ((Mem.mem_access m1) !! b6 ofs Max); auto. inv H.
              -- rewrite <- X2_2 in *.
                 destruct (SP_HAS_PTR0) as [? [? ?]].
                 simpl. now destruct flowsto_dec.
                 simpl. split; auto.
                 unfold Mem.set_perm in set_perm2.
                 unfold Mem.valid_block. clear -set_perm2. destruct plt; try discriminate.
                 inv set_perm2. auto.
                 clear -set_perm2. revert set_perm2.
                 unfold Mem.set_perm. unfold Mem.perm. intros ?. destruct plt; try discriminate. inv set_perm2.
                 simpl.
                 rewrite PMap.gss; auto. intros ? ?.
                 destruct ((Mem.mem_access m5) !! b7 ofs Max); auto. inv H.
              -- destruct (SP_HAS_PTR) as [? [? ?]].
                 simpl. now destruct flowsto_dec.
                 simpl. split; auto.
                 unfold Mem.set_perm in set_perm3.
                 unfold Mem.valid_block. clear -set_perm3. destruct plt; try discriminate.
                 inv set_perm3. auto.
                 clear -set_perm3. revert set_perm3.
                 unfold Mem.set_perm. unfold Mem.perm. intros ?. destruct plt; try discriminate. inv set_perm3.
                 simpl.
                 rewrite PMap.gss; auto. intros ? ?.
                 destruct ((Mem.mem_access m3'') !! b9 ofs Max); auto. inv H.
              (* -- simpl in *. *)
              (*    exploit SP_HAS_PTR; eauto. now destruct flowsto_dec. *)
              (*    intros [x [? [? [? A]]]]. *)
              (*    assert (b6 = x) by congruence. subst x. *)
              (*    assert (m = m'). *)
              (*    { clear -H2 H3. destruct i; try discriminate; simpl in *. *)
              (*      destruct Genv.allowed_addrof_b; inv H2; auto. *)
              (*      inv H2; auto. } subst m'. *)
              (*    rewrite <- A. *)
              (*    eapply Mem.set_preserves_comp in set_perm1. rewrite <- set_perm1. *)
              (*    clear set_perm1. *)
              (*    erewrite Mem.alloc_block_compartment; eauto. *)
              (*    erewrite Mem.alloc_block_compartment; eauto. *)
              (*    destruct (eq_block b6 b2). *)
              (*    { subst. eapply Mem.fresh_block_alloc in alloc1'. *)
              (*      exfalso. eapply alloc1'. *)
              (*      eapply Mem.valid_block_alloc; eauto. *)
              (*      eapply Mem.valid_block_inject_1; eauto. *)
              (*      eapply partial_mem_inject; eauto. } *)
              (*    destruct (eq_block b6 b1). *)
              (*    { subst. eapply Mem.fresh_block_alloc in alloc1. *)
              (*      exfalso. eapply alloc1. eapply Mem.valid_block_inject_1; eauto. *)
              (*      eapply partial_mem_inject; eauto. } *)
              (*    reflexivity. *)
              (* -- simpl in *. assert (R: has_comp_function f = has_comp_function f0). *)
              (*    { inv EV; inv EV0; eauto. } *)
              (*    exploit SP_HAS_PTR0; eauto. rewrite <- R. now destruct flowsto_dec. *)
              (*    intros [x [? [? [? A]]]]. *)
              (*    assert (b7 = x) by congruence. subst x. *)
              (*    assert (m2 = m'0). *)
              (*    { clear -H7 H8. destruct i0; try discriminate; simpl in *. *)
              (*      destruct Genv.allowed_addrof_b; inv H7; auto. *)
              (*      inv H7; auto. } subst m'0. *)
              (*    rewrite R, <- A. *)
              (*    eapply Mem.set_preserves_comp in set_perm2. rewrite <- set_perm2. *)
              (*    clear set_perm2. *)
              (*    erewrite Mem.alloc_block_compartment; eauto. *)
              (*    erewrite Mem.alloc_block_compartment; eauto. *)
              (*    destruct (eq_block b7 b5). *)
              (*    { subst. eapply Mem.fresh_block_alloc in alloc2'. *)
              (*      exfalso. eapply alloc2'. *)
              (*      eapply Mem.valid_block_alloc; eauto. *)
              (*      eapply Mem.valid_block_inject_1; eauto. *)
              (*      eapply partial_mem_inject; eauto. } *)
              (*    destruct (eq_block b6 b1). *)
              (*    { subst. eapply Mem.fresh_block_alloc in alloc1. *)
              (*      exfalso. eapply alloc1. eapply Mem.valid_block_inject_1; eauto. *)
              (*      eapply partial_mem_inject; eauto. } *)
              (*    reflexivity. *)
              -- unfold nonempty in *.
                 eapply Mem.perm_implies.
                 eapply Mem.perm_set_1; eauto.
                 eapply Mem.perm_alloc_1; eauto.
                 eapply Mem.perm_alloc_1; eauto.
                 assert (m' = m).
                 { clear -H2 H3. destruct i; simpl in *; try discriminate; try now inv H2.
                   destruct (Genv.allowed_addrof_b); try discriminate. inv H2. auto. }
                 subst m'.
                 destruct (SP_HAS_PTR) as [? [? [X [Y Z]]]].
                 simpl. now destruct flowsto_dec.
                 assert (x = b6) by congruence. subst. eauto.
                 constructor.
              -- unfold nonempty in *.
                 eapply Mem.perm_implies.
                 eapply Mem.perm_set_1; eauto.
                 eapply Mem.perm_alloc_1; eauto.
                 eapply Mem.perm_alloc_1; eauto.
                 assert (m'0 = m2) .
                 { clear -H7 H8. destruct i0; simpl in *; try discriminate; try now inv H7.
                   destruct (Genv.allowed_addrof_b); try discriminate. inv H7. auto. }
                 subst m'0.
                 destruct (SP_HAS_PTR0) as [? [? [X [Y Z]]]].
                 simpl. now destruct flowsto_dec.
                 assert (x = b7) by congruence. subst. eauto.
                 constructor.
              -- unfold nonempty in *.
                 eapply Mem.perm_implies.
                 eapply Mem.perm_set_1; eauto.
                 eapply Mem.perm_alloc_1; eauto.
                 eapply Mem.perm_alloc_1; eauto.
                 assert (m3' = m3).
                 { clear -exec_instr' H3.
                   destruct i; simpl in *; try discriminate; try now inv exec_instr'.
                   destruct (Genv.allowed_addrof_b); try discriminate. inv exec_instr'. auto. }
                 subst m3'.
                 destruct (SP_HAS_PTR) as [? [? [X [Y Z]]]].
                 simpl. now destruct flowsto_dec.
                 replace 0 with (0 + 0) by lia.
                 eapply Mem.mi_perm. eapply Mem.mi_inj. eapply partial_mem_inject.
                 eapply m1_m3. specialize (rs1_rs3 X2).
                 rewrite X in *. rewrite <- H26 in *; rewrite <- X2_3 in *.
                 inv rs1_rs3; eauto. assert (delta0 = 0).
                 { eapply delta_zero. eapply m1_m3; eauto. eauto. }
                 subst delta0. eauto. eauto. constructor.

              -- destruct (SP_HAS_PTR) as [? [? [X [Y _]]]].
                 simpl. now destruct flowsto_dec.
                 simpl. intros ? Z.
                 assert (x = b6) by congruence. subst. congruence.
              -- destruct (SP_HAS_PTR0) as [? [? [X [Y _]]]].
                 simpl. now destruct flowsto_dec.
                 simpl. intros ? Z.
                 assert (x = b7) by congruence. subst. congruence.
              -- destruct (SP_HAS_PTR) as [? [? [X [Y _]]]].
                 simpl. now destruct flowsto_dec.
                 simpl. intros ? Z.
                 eapply (defs_rev_inject s (s (Genv.find_comp_of_block ge1 b')) W1 W3) in Z; eauto.
                 destruct Z as [? [Z [? Z']]]. inv Z'.
                 assert (x = b6) by congruence. subst. congruence.
              -- split.
                 rewrite <- X2_1 in *.
                 eapply Mem.set_perm_valid_block_1; eauto. eapply Mem.valid_new_block; eauto.
                 intros ? G.
                 eapply Mem.perm_set_4 in G; eauto.
                 eapply Mem.perm_alloc_3 in G; eauto. lia.
                 destruct (peq b2 b6). right. subst.
                 intros R.
                 eapply Mem.perm_alloc_3 in R; eauto. lia. now left.
              -- split.
                 rewrite <- X2_2 in *.
                 eapply Mem.set_perm_valid_block_1; eauto. eapply Mem.valid_new_block; eauto.
                 intros ? G.
                 eapply Mem.perm_set_4 in G; eauto.
                 eapply Mem.perm_alloc_3 in G; eauto. lia.
                 destruct (peq b5 b7). right. subst.
                 intros R.
                 eapply Mem.perm_alloc_3 in R; eauto. lia. now left.
              -- split.
                 rewrite <- X2_1 in *.
                 eapply Mem.set_perm_valid_block_1; eauto. eapply Mem.valid_new_block; eauto.
                 intros ? G.
                 eapply Mem.perm_set_4 in G; eauto.
                 eapply Mem.perm_alloc_3 in G; eauto. lia.
                 destruct (peq dsp3 b9). right. subst.
                 intros R.
                 eapply Mem.perm_alloc_3 in R; eauto. lia. now left.
              -- simpl. inv strong_s1_s3.
                 inv COMP2; eauto. rewrite eq_pc' in *; auto.
                 unfold Genv.find_comp_of_block; rewrite find_funct; auto.
              -- unfold diff_sp. exploit DIFF_SP; eauto.
                 simpl. now destruct flowsto_dec. unfold diff_sp_X2.
                 rewrite <- X2_1. eauto.
              -- unfold diff_sp. exploit DIFF_SP0; eauto.
                 simpl. now destruct flowsto_dec. unfold diff_sp_X2.
                 rewrite <- X2_2. eauto.
              -- unfold diff_sp. simpl. clear st_rel' S st_rel'' strel S' SS.
                 specialize (rs1_rs3 X2). rewrite <- X2_3, <- H26 in rs1_rs3.
                 rewrite <- X2_1 in rs1_rs3.
                 assert (delta = 0).
                 { eapply delta_zero. eapply m1_m3. eauto. }
                 subst delta.
                 revert rs1_rs3.
                 rewrite Ptrofs.add_zero. unfold diff_sp in *.
                 simpl in st_rel.
                 inv st_rel.
                 ++ simpl in *; subst; simpl.
                    unfold Vnullptr; destruct Archi.ptr64; eauto.
                 ++ simpl in *. subst.
                    inv H12; eauto.
                    { revert H32.
                      exploit DIFF_SP; eauto.
                      now destruct flowsto_dec. unfold diff_sp_X2. simpl.
                      rewrite <- X2_1.
                      intros A B.
                      destruct sp1 ; try now inv B.
                      intros C.
                      inv B; inv C.
                      eapply (meminj_injective s ge1 ge3 j__δ); eauto. }
                    { revert H32.
                      exploit DIFF_SP; eauto.
                      now destruct flowsto_dec. unfold diff_sp_X2. simpl.
                      rewrite <- X2_1.
                      exploit DIFF_SP0; eauto.
                      replace (has_comp_function f0) with (has_comp_function f).
                      now destruct flowsto_dec. { now inv EV; inv EV0. }
                      unfold diff_sp_X2. simpl.
                      rewrite <- X2_2.
                      destruct sp3; try auto.
                      destruct sp2; try contradiction.
                      destruct sp1; try contradiction.
                      intros diff1 diff2 inj1 inj2. clear inj2. rename H27 into inj2.
                      intros ?; subst b12.
                      inv inj1.
                      assert (delta = 0).
                      { eapply delta_zero. eapply m2_m3. eauto. } subst delta.
                      revert H32. intros inj1.
                      revert inj2. intros inj2.
                      revert m1_m3; revert m2_m3.
                      intros m2_m3 m1_m3.
                      assert (C1: j__δ b6 <> None) by congruence.
                      assert (C2: j__oppδ b13 <> None) by congruence.
                      eapply same_dom in m1_m3 as D1.
                      eapply same_dom in m2_m3 as D2.
                      apply D1 in C1; apply D2 in C2.
                      destruct C1 as [[C11 C12] | [? C1]]; try congruence;
                        destruct C2 as [[C21 C22] | [? C2]]; try congruence.
                      - clear D1 D2.
                        simpl in C11, C21.
                        assert (m1_m3'' := m1_m3).
                        exploit perm_compartment1. eapply m1_m3. eauto.
                        intros [? R].
                        exploit perm_compartment1. eapply m2_m3. eauto.
                        intros [? R'].
                        exploit perm_compartment2. eapply m2_m3. eapply NONEMPTY3.
                        intros [? R''] .
                        exploit perm_compartment2. eapply m2_m3. eapply Mem.mi_perm.
                        eapply Mem.mi_inj. eapply partial_mem_inject. eapply m2_m3.
                        eauto. eauto. intros [? eq_cp1].

                        eapply partial_mem_inject in m1_m3.
                        eapply Mem.mi_inj in m1_m3.
                        pose proof (Mem.mi_own _ _ _ m1_m3) as Y1.
                        (* specialize (X1 _ _ _ _ _ _ _ inj2) *)
                        eapply partial_mem_inject in m2_m3.
                        eapply Mem.mi_inj in m2_m3.
                        pose proof (Mem.mi_own _ _ _ m2_m3) as Y2.
                        specialize (Y2 _ _ _ _ _ _ _ inj1 NONEMPTY2 (flowsto_refl _)).
                        simpl in Y2.
                        rewrite eq_cp1 in *. rewrite R' in *.
                        assert (x2 = x0) by now inv Y2.
                        subst. rewrite e1 in *.
                        exploit SP_HAS_PTR; eauto.
                        now destruct flowsto_dec.
                        intros [? [? [? [? ?]]]].
                        assert (x2 = b6) by congruence. subst.
                        specialize (Y1 _ _ _ _ 0 Nonempty Max inj2 H29 (flowsto_refl _)).
                        simpl in Y1. inv R''. subst.
                        rewrite eq_cp1 in *.
                        assert (exists xa, Mem.block_compartment m b6 = Comp xa).
                        eapply perm_compartment1; eauto. destruct H32. rewrite H32 in *.
                        inv Y1. clear -C11 C21.
                        Local Transparent opposite.
                        destruct (s (has_comp_function f)); simpl in *. congruence.
                        congruence.
                      - eapply defs_inject in C1 as [? [? [? [X ?]]]]; eauto.
                        inv X. congruence. }

              -- simpl. inv strong_s1_s3.
                 inv COMP2; eauto. rewrite eq_pc' in *; auto.
                 ++ rewrite <- H32. simpl.
                    unfold Genv.find_comp_of_block at 1; rewrite find_funct; auto.
                    clear -diff_comp. intros ?. apply diff_comp. rewrite <- H.
                    auto with comps.
                 ++ rewrite <- H35. simpl.
                    clear -diff_comp. intros ?. apply diff_comp. rewrite <- H.
                    auto with comps.
            * intros _.
              eapply regset_rel_inject. eapply regset_rel_inject. eapply H19.
              -- econstructor.
                 eapply H20; eauto. reflexivity. now rewrite Ptrofs.add_zero.
              -- eapply val_inject_incr; eauto. econstructor.
                 eapply H15; eauto. reflexivity. now rewrite Ptrofs.add_zero.
            * Local Transparent opposite. now destruct s.
          + exploit SP_HAS_PTR; eauto. simpl; now destruct flowsto_dec.
            intros [? [? [? [? ?]]]]. assert (b6 = x) by congruence. subst.
            eauto.
          + exploit SP_HAS_PTR0; eauto. simpl; now destruct flowsto_dec.
            intros [? [? [? [? ?]]]]. assert (b7 = x) by congruence. subst.
            eauto.
          + exploit SP_HAS_PTR; eauto. simpl; now destruct flowsto_dec.
            intros [? [? [? [? ?]]]]. assert (b6 = x) by congruence. subst.
            intros. intros X.
            eapply (defs_rev_inject _ _ _ _ j__δ) in X; eauto.
            destruct X as [? [? [? X]]].
            inv X; eauto.
            eapply H12; eauto.
        - replace (s (comp_of f)) with (opposite (opposite (s (comp_of f)))) in m1_m3' by now destruct s.
          eapply stack_rel_comm in st_rel''.
          eapply (alloc_preserves_rel_no_regset s W2 W1 W3) with (m2 := m') in alloc2 as alloc2'';
            eauto using match_prog_unique.
          destruct alloc2'' as (j0 & temp_m3 & dra3 & alloc3 & ? & ? & R1 & ? & ? & ?).
          eapply (alloc_preserves_rel_no_regset s W2 W1 W3) in alloc2' as alloc2'';
            eauto using match_prog_unique.
          destruct alloc2'' as (j & m3'' & dsp3 & alloc3' & ? & ? & R2 & ? & ? & ?).
          (* rewrite <- e1 in *. *)
          assert (e1: s cp' = opposite (s (comp_of f))).
          { clear -n1. now destruct (s cp'), (s (comp_of f)). }
          rewrite e1 in *.
          exploit (alloc_preserves_weak s (s (comp_of f)) W1 norepet1 ge2 W3 cp_main j__δ' j cp' 0 0 m'); eauto.
          rewrite e1; eauto.
          rewrite e1; eauto. eapply stack_rel_comm; eauto.
          intros (j0' & ? & R1' & ? & ?).
          exploit (alloc_preserves_weak s (s (comp_of f)) W1 norepet1 ge2 W3 cp_main j0' j cp' 0 0 m0); eauto.
          intros (j' & ? & R2' & ? & S).
          (* eapply stack_rel_comm in SS'. *)
          (* replace (opposite (opposite (s cp'))) with (s cp') in * by now destruct s. *)
          assert (rs' X2 = rs X2) as X2_1.
          { clear -H2 H3. destruct i; try discriminate; simpl in *.
            destruct (Genv.allowed_addrof_b); inv H2; Simpl.
            inv H2; Simpl. }
          assert (rs'0 X2 = rs2 X2) as X2_2.
          { clear -H7 H8. destruct i0; try discriminate; simpl in *.
            destruct (Genv.allowed_addrof_b); inv H7; Simpl.
            inv H7; Simpl. }
          assert (rs3' X2 = rs3 X2) as X2_3.
          { clear -exec_instr' H3. destruct i; try discriminate; simpl in *.
            destruct (Genv.allowed_addrof_b); inv exec_instr'; Simpl.
            inv exec_instr'; Simpl. }
          specialize (rs1_rs3 X2) as X2_inj; rewrite <- X2_1, <- X2_3 in X2_inj.
          destruct (rs' X2) eqn:rs'_X2; try discriminate.
          destruct (rs'0 X2) eqn:rs'0_X2; try discriminate.

          destruct (Mem.set_perm m1 b6 Readable) eqn:set_perm1; try discriminate.
          destruct (Mem.set_perm m5 b7 Readable) eqn:set_perm2; try discriminate.
          inv H11. inv H12.

          unfold update_stack_call.
          rewrite NEXTCOMP'. simpl. destruct flowsto_dec; try contradiction.
          rewrite alloc3; simpl; rewrite alloc3'; simpl.
          inv X2_inj.

          assert (mem_rel s ge2 ge3 j (opposite (opposite (s (Genv.find_comp_of_block ge1 b')))) m5 m3'').
          { replace (opposite (opposite (s (Genv.find_comp_of_block ge1 b')))) with (s (Genv.find_comp_of_block ge1 b')).
            rewrite e1; eauto.
            clear. now destruct s.
          }
          eapply (set_perm_preserves_rel s W1 W2 W3) in S; eauto using match_prog_unique.


          destruct S as [m3''' [set_perm3 [mrel1 [mrel2 strel]]]].
          rewrite set_perm3.
          rewrite rs3'_X1.
          do 9 eexists.
          split; eauto.
          split; eauto.
          split; eauto.
          split; eauto.
          split; eauto.
          split; eauto.
          rewrite e1 in mrel1. clear -mrel1. now destruct s; auto.
          split; eauto.
          rewrite e1 in mrel2. clear -mrel2. now destruct s; auto.
          split; eauto.
          eapply inject_incr_trans; eauto.
          split; eauto.
          eapply inject_incr_trans; eauto.
          split; eauto.
          { rewrite e1 in strel.
            replace (opposite (opposite (s (comp_of f)))) with (s (has_comp_function f)) in strel by now destruct s.
            econstructor; eauto using inject_incr_stack_rel1, inject_incr_stack_rel2.
            eapply stackframe_related_δ with (cp := comp_of f); eauto.
            -- eapply Genv.find_funct_ptr_iff in find_funct.
               erewrite Genv.find_funct_ptr_find_comp_of_block; eauto. reflexivity.
            -- specialize (rs1_rs3' X1). rewrite rs'_X1, rs3'_X1 in *. eauto.
            -- rewrite e1. destruct side_eq; try now destruct s.
               eapply val_inject_incr; eauto.
            -- rewrite e1. destruct side_eq; try now destruct s.
               eauto.
            -- { assert (m = m').
                 { clear -H2 H3.
                   destruct i; try discriminate; simpl in *.
                   destruct Genv.allowed_addrof_b; inv H2; auto.
                   inv H2; auto. } subst m'.
                 apply incr, H23, H26 in H28.
                 clear -ARGS NO_CROSS_PTR n H18 rs1_rs3 alloc1 alloc1' m1_m3' H2 rs'_X2 H26 H28 set_perm1 mrel1.
                 rename H18 into m1_m3.
                 rename H2 into exec_instr1.
                 intros ? ? G ? G'.
                 split.
                 { intros ? ? A; inv A.
                   (* assert (R: rs' X2 = rs X2). *)
                   (* { clear -exec_instr1 sigcall. destruct i; try discriminate; simpl in *. *)
                   (*   destruct Genv.allowed_addrof_b; auto. inv exec_instr1. *)
                   (*   Simpl. inv exec_instr1. *)
                   (*   inv exec_instr1. Simpl. } *)
                   clear - G ARGS rs'_X2 set_perm1 alloc1' alloc1.
                   destruct G as [G | [[l G] | [l G]]].
                   - unfold call_arguments in ARGS.
                     pose proof (list_forall2_in_left _ ARGS G) as [arg [IN P]].
                     inv P. inv H0.
                     rewrite rs'_X2 in H4. simpl in H4.
                     eapply Mem.load_alloc_other in H4; eauto.
                     eapply Mem.load_alloc_other in H4; eauto.
                     eapply Mem.load_set in H4; eauto.
                     eapply Mem.load_valid_access in H4 as [? [? ?]]. eauto.
                     constructor.
                   - unfold call_arguments in ARGS.
                     pose proof (list_forall2_in_left _ ARGS G) as [arg [IN P]].
                     inv P. inv H1.
                     rewrite rs'_X2 in H5. simpl in H5.
                     eapply Mem.load_alloc_other in H5; eauto.
                     eapply Mem.load_alloc_other in H5; eauto.
                     eapply Mem.load_set in H5; eauto.
                     eapply Mem.load_valid_access in H5 as [? [? ?]]. eauto.
                     constructor.
                   - unfold call_arguments in ARGS.
                     pose proof (list_forall2_in_left _ ARGS G) as [arg [IN P]].
                     inv P. inv H3.
                     rewrite rs'_X2 in H5. simpl in H5.
                     eapply Mem.load_alloc_other in H5; eauto.
                     eapply Mem.load_alloc_other in H5; eauto.
                     eapply Mem.load_set in H5; eauto.
                     eapply Mem.load_valid_access in H5 as [? [? ?]]. eauto.
                     constructor.
                 }
                 intros ? G''.

                 exploit delta_zero; eauto. intros ->.
                 eapply Mem.load_inject in G'' as G'''; eauto using partial_mem_inject.
                 destruct G''' as [v2 [load' v_v2]].
                 rewrite !Ptrofs.add_zero, Z.add_0_r in *.
                 assert (not_ptr v).
                 { destruct G as [G | [[l G] | [l G]]].
                   - unfold call_arguments in ARGS.
                     exploit list_forall2_in_left; eauto.
                     intros [arg [IN P]].
                     inv P. inv H0.
                     assert (arg = v).
                     { rewrite rs'_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H4.

                       eapply Mem.load_set' in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       congruence.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. constructor.
                       intros ? ?.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.load_valid_access; eauto.
                     }
                     subst arg.
                     exploit NO_CROSS_PTR; eauto. simpl. destruct flowsto_dec; try now auto.
                     intros R. eapply Forall_forall in R; eauto.
                   - unfold call_arguments in ARGS.
                     exploit list_forall2_in_left; eauto.
                     intros [arg [IN P]].
                     inv P. inv H1.
                     assert (vhi = v).
                     { rewrite rs'_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H5.
                       eapply Mem.load_set' in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       congruence.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. constructor.
                       intros ? ?.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.load_valid_access; eauto. }
                     subst vhi.
                     exploit NO_CROSS_PTR; eauto. simpl. destruct flowsto_dec; try now auto.

                     intros R. rewrite Forall_forall in R.
                     apply R in IN.
                     destruct v; simpl in *; try now auto.
                   - unfold call_arguments in ARGS.
                     exploit list_forall2_in_left; eauto.
                     intros [arg [IN P]].
                     inv P. inv H3.
                     assert (vlo = v).
                     { rewrite rs'_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H5.
                       eapply Mem.load_set' in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       congruence.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. constructor.
                       intros ? ?.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.load_valid_access; eauto. }
                     subst vlo.
                     exploit NO_CROSS_PTR; eauto. simpl. destruct flowsto_dec; try now auto.

                     intros R. rewrite Forall_forall in R.
                     apply R in IN.
                     destruct v, vhi; simpl in *; try now auto. }
                 inv v_v2; simpl in *; split; eauto; contradiction.
               }
            -- { assert (m = m').
                 { clear -H2 H3.
                   destruct i; try discriminate; simpl in *.
                   destruct Genv.allowed_addrof_b; inv H2; auto.
                   inv H2; auto. } subst m'.
                 assert (m'0 = m2).
                 { clear -H7 H8.
                   destruct i0; try discriminate; simpl in *.
                   destruct Genv.allowed_addrof_b; inv H7; auto.
                   inv H7; auto. } subst m'0.
                 assert (CROSS: Genv.type_of_call (comp_of f) (Genv.find_comp_of_block ge1 b') = Genv.CrossCompartmentCall).
                 { simpl. destruct flowsto_dec; try congruence. }
                 specialize (NO_CROSS_PTR CROSS).
                 assert (args0 = args).
                 { clear -EV EV0 NO_CROSS_PTR. inv EV; inv EV0; auto.
                   clear -H8 H14 NO_CROSS_PTR. revert H8 H14.
                   generalize (sig_args sig).
                   generalize dependent args0. generalize dependent args. induction vl.
                   - intros; inv H8; inv H14; eauto.
                   - intros; inv H8; inv H14; eauto.
                     assert (v0 = v1).
                     { inv H1; inv H6; eauto. inv NO_CROSS_PTR; eauto. now simpl in *. }
                     subst v1.
                     inv NO_CROSS_PTR.
                     exploit IHvl; eauto. intros ->; eauto. }
                 subst args0.
                 intros ? ? G ? G'.
                 split.
                 { intros ? ? A; inv A.
                   assert (R: rs'0 X2 = rs2 X2).
                   { clear -H7 H8. destruct i0; try discriminate; simpl in *.
                     destruct Genv.allowed_addrof_b; auto. inv H7.
                     Simpl. inv H7.
                     inv H7. Simpl. }
                   clear -CROSS G ARGS0 R X2_2 set_perm2 alloc2' alloc2.
                   destruct G as [G | [[l G] | [l G]]].
                   - unfold call_arguments in ARGS0.
                     pose proof (list_forall2_in_left _ ARGS0 G) as [arg [IN P]].
                     inv P. inv H0.
                     rewrite R, <- X2_2 in H4. simpl in H4.
                     eapply Mem.load_alloc_other in H4; eauto.
                     eapply Mem.load_alloc_other in H4; eauto.
                     eapply Mem.load_set in H4; eauto.
                     eapply Mem.load_valid_access in H4 as [? [? ?]]. eauto.
                     constructor.
                   - unfold call_arguments in ARGS0.
                     pose proof (list_forall2_in_left _ ARGS0 G) as [arg [IN P]].
                     inv P. inv H1.
                     rewrite R, <- X2_2 in H5. simpl in H5.
                     eapply Mem.load_alloc_other in H5; eauto.
                     eapply Mem.load_alloc_other in H5; eauto.
                     eapply Mem.load_set in H5; eauto.
                     eapply Mem.load_valid_access in H5 as [? [? ?]]. eauto.
                     constructor.
                   - unfold call_arguments in ARGS0.
                     pose proof (list_forall2_in_left _ ARGS0 G) as [arg [IN P]].
                     inv P. inv H3.
                     rewrite R, <- X2_2 in H5. simpl in H5.
                     eapply Mem.load_alloc_other in H5; eauto.
                     eapply Mem.load_alloc_other in H5; eauto.
                     eapply Mem.load_set in H5; eauto.
                     eapply Mem.load_valid_access in H5 as [? [? ?]]. eauto.
                     constructor.
                 }
                 intros ? G''.
                 assert (G''': Mem.loadv (chunk_of_type ty) m''
                                 (Val.offset_ptr (Vptr b6 i1) (Ptrofs.repr bofs)) top
                               = Some v).
                 { destruct G as [G | [[l G] | [l G]]].
                   - unfold call_arguments in ARGS, ARGS0.
                     clear call_args'.
                     pose proof (parallel_list_forall2_in_left _ ARGS ARGS0 G)
                       as [arg [IN [P1 P2]]].
                     inv P1; inv P2.
                     inv H29; inv H30.
                     assert (arg = v).
                     { rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H33.

                       eapply Mem.load_set' in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       congruence.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. constructor.
                       intros ? ?.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.load_valid_access; eauto. }
                     subst arg.
                     rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                     eapply Mem.load_Some_None in H34.
                     eapply Mem.load_set; eauto. constructor.
                     erewrite Mem.load_alloc_unchanged with (m1 := m0); eauto.
                     erewrite Mem.load_alloc_unchanged with (m1 := m); eauto.
                     eapply Mem.valid_access_valid_block; eauto.
                     eapply Mem.valid_access_implies; eauto.
                     eapply Mem.load_valid_access; eauto.
                     constructor.
                     eapply Mem.valid_block_alloc; eauto.
                     eapply Mem.valid_access_valid_block; eauto.
                     eapply Mem.valid_access_implies; eauto.
                     eapply Mem.load_valid_access; eauto.
                     constructor.
                   - unfold call_arguments in ARGS, ARGS0.
                     clear call_args'.
                     pose proof (parallel_list_forall2_in_left _ ARGS ARGS0 G)
                       as [arg [IN [P1 P2]]].
                     inv P1; inv P2.
                     assert (vhi = vhi0).
                     {  exploit eq_distributes_longofwords; eauto.
                        rewrite H31.
                        eapply Forall_forall; eauto.
                        eapply Forall_forall; eauto.
                        now intros [].
                     }
                     subst vhi0.
                     inv H30; inv H33.
                     assert (vhi = v).
                     { rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H36.

                       eapply Mem.load_set' in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       congruence.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. constructor.
                       intros ? ?.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.load_valid_access; eauto. }
                     subst vhi.
                     rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                     eapply Mem.load_Some_None in H37.
                     eapply Mem.load_set; eauto. constructor.
                     erewrite Mem.load_alloc_unchanged with (m1 := m0); eauto.
                     erewrite Mem.load_alloc_unchanged with (m1 := m); eauto.
                     eapply Mem.valid_access_valid_block; eauto.
                     eapply Mem.valid_access_implies; eauto.
                     eapply Mem.load_valid_access; eauto.
                     constructor.
                     eapply Mem.valid_block_alloc; eauto.
                     eapply Mem.valid_access_valid_block; eauto.
                     eapply Mem.valid_access_implies; eauto.
                     eapply Mem.load_valid_access; eauto.
                     constructor.
                   - unfold call_arguments in ARGS, ARGS0.
                     clear call_args'.
                     pose proof (parallel_list_forall2_in_left _ ARGS ARGS0 G)
                       as [arg [IN [P1 P2]]].
                     inv P1; inv P2.
                     assert (vlo = vlo0).
                     {  exploit eq_distributes_longofwords; eauto.
                        rewrite H31.
                        eapply Forall_forall; eauto.
                        eapply Forall_forall; eauto.
                        now intros [].
                     }
                     subst vlo0.
                     inv H32; inv H34.
                     assert (vlo = v).
                     { rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H36.

                       eapply Mem.load_set' in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       congruence.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. constructor.
                       intros ? ?.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.load_valid_access; eauto. }
                     subst vlo.
                     rewrite rs'_X2, rs'0_X2 in *; simpl in *.
                     eapply Mem.load_Some_None in H37.
                     eapply Mem.load_set; eauto. constructor.
                     erewrite Mem.load_alloc_unchanged with (m1 := m0); eauto.
                     erewrite Mem.load_alloc_unchanged with (m1 := m); eauto.
                     eapply Mem.valid_access_valid_block; eauto.
                     eapply Mem.valid_access_implies; eauto.
                     eapply Mem.load_valid_access; eauto.
                     constructor.
                     eapply Mem.valid_block_alloc; eauto.
                     eapply Mem.valid_access_valid_block; eauto.
                     eapply Mem.valid_access_implies; eauto.
                     eapply Mem.load_valid_access; eauto.
                     constructor. }

                 clear G''; rename G''' into G''.
                 apply incr, H23, H26 in H28.
                 clear -ARGS NO_CROSS_PTR n H18 rs1_rs3 alloc1 alloc1' m1_m3' H2 rs'_X2 H26 H28 set_perm1 mrel1 G G' G''.
                 rename H18 into m1_m3.
                 rename H2 into exec_instr1.

                 exploit delta_zero; eauto. intros ->.
                 eapply Mem.load_inject in G'' as G'''; eauto using partial_mem_inject.
                 destruct G''' as [v2 [load' v_v2]].
                 rewrite !Ptrofs.add_zero, Z.add_0_r in *.
                 assert (not_ptr v).
                 { destruct G as [G | [[l G] | [l G]]].
                   - unfold call_arguments in ARGS.
                     exploit list_forall2_in_left; eauto.
                     intros [arg [IN P]].
                     inv P. inv H0.
                     assert (arg = v).
                     { rewrite rs'_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H4.

                       eapply Mem.load_set' in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       congruence.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. constructor.
                       intros ? ?.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.load_valid_access; eauto.
                     }
                     subst arg.
                     eapply Forall_forall in NO_CROSS_PTR; eauto.
                   - unfold call_arguments in ARGS.
                     exploit list_forall2_in_left; eauto.
                     intros [arg [IN P]].
                     inv P. inv H1.
                     assert (vhi = v).
                     { rewrite rs'_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H5.
                       eapply Mem.load_set' in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       congruence.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. constructor.
                       intros ? ?.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.load_valid_access; eauto. }
                     subst vhi.
                     rewrite Forall_forall in NO_CROSS_PTR.
                     apply NO_CROSS_PTR in IN.
                     destruct v; simpl in *; try now auto.
                   - unfold call_arguments in ARGS.
                     exploit list_forall2_in_left; eauto.
                     intros [arg [IN P]].
                     inv P. inv H3.
                     assert (vlo = v).
                     { rewrite rs'_X2 in *; simpl in *.
                       eapply Mem.load_Some_None in H5.
                       eapply Mem.load_set' in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       erewrite Mem.load_alloc_unchanged in G''; eauto.
                       congruence.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor.
                       eapply Mem.valid_block_alloc; eauto.
                       eapply Mem.valid_access_valid_block; eauto.
                       eapply Mem.valid_access_implies; eauto.
                       eapply Mem.load_valid_access; eauto.
                       constructor. constructor.
                       intros ? ?.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.perm_alloc_1; eauto.
                       eapply Mem.load_valid_access; eauto. }
                     subst vlo.
                     rewrite Forall_forall in NO_CROSS_PTR.
                     apply NO_CROSS_PTR in IN.
                     destruct v, vhi; simpl in *; try now auto. }
                 inv v_v2; simpl in *; split; eauto; contradiction.
               }
            -- rewrite <- X2_1 in *.
               destruct (SP_HAS_PTR) as [? [? ?]].
               simpl. now destruct flowsto_dec.
               simpl. split; auto. unfold Mem.set_perm in set_perm1.
               unfold Mem.valid_block. clear -set_perm1. destruct plt; try discriminate.
               inv set_perm1. auto.
               clear -set_perm1. revert set_perm1.
               unfold Mem.set_perm. unfold Mem.perm. intros ?. destruct plt; try discriminate. inv set_perm1.
               simpl.
               rewrite PMap.gss; auto. intros ? ?.
               destruct ((Mem.mem_access m1) !! b6 ofs Max); auto. inv H.
            -- rewrite <- X2_2 in *.
               destruct (SP_HAS_PTR0) as [? [? ?]].
               simpl. now destruct flowsto_dec.
               simpl. split; auto.
               unfold Mem.set_perm in set_perm2.
               unfold Mem.valid_block. clear -set_perm2. destruct plt; try discriminate.
               inv set_perm2. auto.
               clear -set_perm2. revert set_perm2.
               unfold Mem.set_perm. unfold Mem.perm. intros ?. destruct plt; try discriminate. inv set_perm2.
               simpl.
               rewrite PMap.gss; auto. intros ? ?.
               destruct ((Mem.mem_access m5) !! b7 ofs Max); auto. inv H.
            -- destruct (SP_HAS_PTR) as [? [? ?]].
               simpl. now destruct flowsto_dec.
               simpl. split; auto.
               unfold Mem.set_perm in set_perm3.
               unfold Mem.valid_block. clear -set_perm3. destruct plt; try discriminate.
               inv set_perm3. auto.
               clear -set_perm3. revert set_perm3.
               unfold Mem.set_perm. unfold Mem.perm. intros ?. destruct plt; try discriminate. inv set_perm3.
               simpl.
               rewrite PMap.gss; auto. intros ? ?.
               destruct ((Mem.mem_access m3'') !! b9 ofs Max); auto. inv H.
            -- unfold nonempty in *.
               eapply Mem.perm_implies.
               eapply Mem.perm_set_1; eauto.
               eapply Mem.perm_alloc_1; eauto.
               eapply Mem.perm_alloc_1; eauto.
               assert (m' = m).
               { clear -H2 H3. destruct i; simpl in *; try discriminate; try now inv H2.
                 destruct (Genv.allowed_addrof_b); try discriminate. inv H2. auto. }
               subst m'.
               destruct (SP_HAS_PTR) as [? [? [X [Y Z]]]].
               simpl. now destruct flowsto_dec.
               assert (x = b6) by congruence. subst. eauto.
               constructor.
            -- unfold nonempty in *.
               eapply Mem.perm_implies.
               eapply Mem.perm_set_1; eauto.
               eapply Mem.perm_alloc_1; eauto.
               eapply Mem.perm_alloc_1; eauto.
               assert (m'0 = m2) .
               { clear -H7 H8. destruct i0; simpl in *; try discriminate; try now inv H7.
                 destruct (Genv.allowed_addrof_b); try discriminate. inv H7. auto. }
               subst m'0.
               destruct (SP_HAS_PTR0) as [? [? [X [Y Z]]]].
               simpl. now destruct flowsto_dec.
               assert (x = b7) by congruence. subst. eauto.
               constructor.
            -- unfold nonempty in *.
               eapply Mem.perm_implies.
               eapply Mem.perm_set_1; eauto.
               eapply Mem.perm_alloc_1; eauto.
               eapply Mem.perm_alloc_1; eauto.
               assert (m3' = m3).
               { clear -exec_instr' H3.
                 destruct i; simpl in *; try discriminate; try now inv exec_instr'.
                 destruct (Genv.allowed_addrof_b); try discriminate. inv exec_instr'. auto. }
               subst m3'.
               destruct (SP_HAS_PTR) as [? [? [X [Y Z]]]].
               simpl. now destruct flowsto_dec.
               replace 0 with (0 + 0) by lia.
               eapply Mem.mi_perm. eapply Mem.mi_inj. eapply partial_mem_inject.
               eapply m1_m3. specialize (rs1_rs3 X2).
               rewrite X in *. rewrite <- H27 in *; rewrite <- X2_3 in *.
               inv rs1_rs3; eauto. assert (delta0 = 0).
               { eapply delta_zero. eapply m1_m3; eauto. eauto. }
               subst delta0. eauto. eauto. constructor.
            -- destruct (SP_HAS_PTR) as [? [? [X [Y _]]]].
               simpl. now destruct flowsto_dec.
               simpl. intros ? Z.
               assert (x = b6) by congruence. subst. congruence.
            -- destruct (SP_HAS_PTR0) as [? [? [X [Y _]]]].
               simpl. now destruct flowsto_dec.
               simpl. intros ? Z.
               assert (x = b7) by congruence. subst. congruence.
            -- destruct (SP_HAS_PTR) as [? [? [X [Y _]]]].
               simpl. now destruct flowsto_dec.
               simpl. intros ? Z.
               eapply (defs_rev_inject) in Z; eauto.
               destruct Z as [? [Z [? Z']]]. inv Z'.
               assert (x = b6) by congruence. subst. congruence.
            -- split.
               rewrite <- X2_1 in *.
               eapply Mem.set_perm_valid_block_1; eauto. eapply Mem.valid_new_block; eauto.
               intros ? G.
               eapply Mem.perm_set_4 in G; eauto.
               eapply Mem.perm_alloc_3 in G; eauto. lia.
               destruct (peq b2 b6). right. subst.
               intros R.
               eapply Mem.perm_alloc_3 in R; eauto. lia. now left.
            -- split.
               rewrite <- X2_2 in *.
               eapply Mem.set_perm_valid_block_1; eauto. eapply Mem.valid_new_block; eauto.
               intros ? G.
               eapply Mem.perm_set_4 in G; eauto.
               eapply Mem.perm_alloc_3 in G; eauto. lia.
               destruct (peq b5 b7). right. subst.
               intros R.
               eapply Mem.perm_alloc_3 in R; eauto. lia. now left.
            -- split.
               rewrite <- X2_1 in *.
               eapply Mem.set_perm_valid_block_1; eauto. eapply Mem.valid_new_block; eauto.
               intros ? G.
               eapply Mem.perm_set_4 in G; eauto.
               eapply Mem.perm_alloc_3 in G; eauto. lia.
               destruct (peq dsp3 b9). right. subst.
               intros R.
               eapply Mem.perm_alloc_3 in R; eauto. lia. now left.
            -- simpl. inv strong_s1_s3.
               inv COMP2; eauto. rewrite eq_pc' in *; auto.
               unfold Genv.find_comp_of_block; rewrite find_funct; auto.
            -- unfold diff_sp. exploit DIFF_SP; eauto.
               simpl. now destruct flowsto_dec. unfold diff_sp_X2.
               rewrite <- X2_1. eauto.
            -- unfold diff_sp. exploit DIFF_SP0; eauto.
               simpl. now destruct flowsto_dec. unfold diff_sp_X2.
               rewrite <- X2_2. eauto.
            (* -- unfold diff_sp. exploit DIFF_SP; eauto. *)
            (*    simpl. now destruct flowsto_dec. unfold diff_sp_X2. *)
            (*    rewrite <- X2_1. *)
            -- unfold diff_sp. simpl. clear st_rel' st_rel'' strel.
               specialize (rs1_rs3 X2). rewrite <- X2_3, <- H27 in rs1_rs3.
               rewrite <- X2_1 in rs1_rs3.
               assert (delta = 0).
               { eapply delta_zero. eapply m1_m3. eauto. }
               subst delta.
               revert rs1_rs3.
               rewrite Ptrofs.add_zero. unfold diff_sp in *.
               simpl in st_rel.
               inv st_rel.
               ++ simpl in *; subst; simpl.
                  unfold Vnullptr; destruct Archi.ptr64; eauto.
               ++ simpl in *. subst.
                  inv H29; eauto.
                  { revert H34.
                    exploit DIFF_SP; eauto.
                    now destruct flowsto_dec. unfold diff_sp_X2. simpl.
                    rewrite <- X2_1.
                    intros A B.
                    destruct sp1 ; try now inv B.
                    intros C.
                    inv B; inv C.
                    eapply (meminj_injective s ge1 ge3 j__δ); eauto. }
                  { revert H34.
                    exploit DIFF_SP; eauto.
                    now destruct flowsto_dec. unfold diff_sp_X2. simpl.
                    rewrite <- X2_1.
                    exploit DIFF_SP0; eauto.
                    replace (has_comp_function f0) with (has_comp_function f).
                    now destruct flowsto_dec. { now inv EV; inv EV0. }
                    unfold diff_sp_X2. simpl.
                    rewrite <- X2_2.
                    destruct sp3; try auto.
                    destruct sp2; try contradiction.
                    destruct sp1; try contradiction.
                    intros diff1 diff2 inj1 inj2.
                    inv inj1. rename H37 into inj1. revert inj1.
                    inv inj2. rename H37 into inj2. revert inj2.
                    intros inj1 inj2.
                    (* clear inj1. rename H33 into inj1. *)
                    intros ?; subst b12.
                    assert (delta = 0).
                    { eapply delta_zero. eapply m2_m3. eauto. } subst delta.
                    assert (delta0 = 0).
                    { eapply delta_zero. eapply m1_m3. eauto. } subst delta0.
                    revert m1_m3; revert m2_m3.
                    intros m2_m3 m1_m3.
                    assert (C1: j__δ b6 <> None) by congruence.
                    assert (C2: j__oppδ b13 <> None) by congruence.
                    eapply same_dom in m1_m3 as D1.
                    eapply same_dom in m2_m3 as D2.
                    apply D1 in C1; apply D2 in C2.
                    destruct C1 as [[C11 C12] | [? C1]]; try congruence;
                      destruct C2 as [[C21 C22] | [? C2]]; try congruence.
                    - clear D1 D2.
                      simpl in C11, C21.
                      assert (m1_m3'' := m1_m3).
                      exploit perm_compartment1. eapply m1_m3. eauto.
                      intros [? R].
                      exploit perm_compartment1. eapply m2_m3. eauto.
                      intros [? R'].
                      exploit perm_compartment2. eapply m2_m3. eapply NONEMPTY3.
                      intros [? R''] .
                      (* exploit perm_compartment2. eapply m1_m3. eapply Mem.mi_perm. *)
                      (* eapply Mem.mi_inj. eapply partial_mem_inject. eapply m1_m3. *)
                      (* eauto. eauto. intros [? eq_cp1]. *)

                      eapply partial_mem_inject in m1_m3.
                      eapply Mem.mi_inj in m1_m3.
                      pose proof (Mem.mi_own _ _ _ m1_m3) as Y1.
                      (* specialize (Y1 _ _ _ _ _ _ _ inj1). *)
                      eapply partial_mem_inject in m2_m3.
                      eapply Mem.mi_inj in m2_m3.
                      exploit SP_HAS_PTR; eauto.
                      now destruct flowsto_dec.
                      intros [? [? [? [? ?]]]].
                      assert (x2 = b6) by congruence. subst.
                      specialize (Y1 _ _ _ _ _ _ _ inj1 H34 (flowsto_refl _)).
                      simpl in Y1.
                      rewrite R'' in Y1.
                      exploit perm_compartment1. eapply m1_m3''. eapply H34.
                      intros [? R''']. rewrite R''' in *.
                      inv Y1.
                      pose proof (Mem.mi_own _ _ _ m2_m3) as Y2.
                      specialize (Y2 _ _ _ _ _ _ _ inj2 NONEMPTY2 (flowsto_refl _)).
                      simpl in Y2. rewrite R'' in *; rewrite R' in *.
                      inv Y2. clear -C11 C21.

                      destruct (s (has_comp_function f)). congruence. congruence.
                    - eapply defs_inject in C1 as [? [? [? [X ?]]]]; eauto.
                      inv X; eauto. congruence. }
            -- simpl. inv strong_s1_s3.
               inv COMP2; eauto. rewrite eq_pc' in *; auto.
               ++ rewrite <- H34. simpl.
                  unfold Genv.find_comp_of_block at 1; rewrite find_funct; auto.
                  clear -diff_comp. intros ?. apply diff_comp. rewrite <- H.
                  auto with comps.
               ++ rewrite <- H37. simpl.
                  clear -diff_comp. intros ?. apply diff_comp. rewrite <- H.
                  auto with comps.
          }
          split; eauto.
          split; eauto. now destruct s.
          intros _.
          { intros r. unfold invalidate_call.
            destruct preg_eq; [subst; simpl; Simpl|].
            rewrite NEXTPC0, rs3'_PC.
            {
              specialize (rs1_rs3' PC); rewrite rs3'_PC, NEXTPC in rs1_rs3'.
              exploit CALLSIG0; eauto. simpl. destruct flowsto_dec; try congruence.
              exploit CALLSIG; eauto. simpl. destruct flowsto_dec; try congruence.
              revert rs1_rs3'.
              clear -H17 inj_pres' EV EV0. rename H17 into inj_pres.
              intros ? [fd1 [b'_fd ?]] [fd2 [b'0_fd ?]].
              inv EV; inv EV0.
              inv H3; inv H13.
              eapply Genv.invert_find_symbol in H4, H14.
              exploit (symbols_inject2 s (s (comp_of f)) W1 W3); eauto.
              now unfold kept_genv; rewrite H4; fold (Genv.find_def ge1 b); rewrite b'_fd.
              exploit (symbols_inject2 s (opposite (s (comp_of f))) W2 W3); eauto.
              now unfold kept_genv; rewrite H14; fold (Genv.find_def ge2 b0); rewrite b'0_fd.
              intros [b1 [? ?]] [b2 [? ?]]. assert (b1 = b2) by congruence; subst.
              inv rs1_rs3'. assert (b3' = b2) by congruence; subst.
              econstructor; eauto. }
            destruct preg_eq; [subst; simpl; Simpl|]. eapply val_inject_incr; eauto.
            destruct preg_eq; [subst; simpl; Simpl|]. eauto.
            destruct in_dec; simpl; Simpl; eauto.

            assert (args0 = args).
            { exploit NO_CROSS_PTR; eauto. simpl; now destruct flowsto_dec; congruence.
              clear -EV EV0. inv EV; inv EV0; auto. intros NO_CROSS_PTR.
              clear -H8 H14 NO_CROSS_PTR. revert H8 H14.
              generalize (sig_args sig).
              generalize dependent args0. generalize dependent args. induction vl.
              - intros; inv H8; inv H14; eauto.
              - intros; inv H8; inv H14; eauto.
                assert (v0 = v1).
                { inv H1; inv H6; eauto. inv NO_CROSS_PTR; eauto. now simpl in *. }
                subst v1.
                inv NO_CROSS_PTR.
                exploit IHvl; eauto. intros ->; eauto. }
            subst args0.
            exploit NO_CROSS_PTR; eauto. simpl. destruct flowsto_dec; try congruence.
            clear -ARGS0 inj_args call_args' i3.
            eapply list_in_map_inv in i3 as [R [? G]]. subst r.
            eapply filter_In in G as [_ G].
            unfold LTL.parameters_mregs in *.


            inv ARGS0; inv call_args'; try congruence.
            now rewrite <- H0 in *.
            assert (a1 = a0) by congruence; subst.
            assert (al0 = al) by congruence; subst. rename a0 into a.  rewrite <- H in *.
            clear H; clear H2.
            assert (HYP1: list_forall2 (call_arg_pair rs'0 m'0) (a :: al) (b1 :: bl)) by now constructor; eauto.
            assert (HYP2: list_forall2 (call_arg_pair rs3' m3') (a :: al) (b0 :: bl0)) by now constructor; eauto.
            clear H3 H4 H1 H0.
            remember (a :: al) as l; clear Heql.
            remember (b1 :: bl) as l'; clear Heql'. remember (b0 :: bl0) as l''; clear Heql''.
            generalize dependent l''. generalize dependent l'.
            generalize dependent l. clear.
            induction l.
            - now simpl.
            - destruct a as [[|]|]; simpl.
              + destruct (mreg_eq R r); try subst R; simpl.
                * intros _ ? ? ? ? ? PTR.
                  inv HYP1; inv HYP2; inv inj_args.
                  inv H1; inv H2.
                  inv H0; inv H1.
                  inv PTR. inv H6; eauto. now rewrite <- H in H1.
                * intros ? ? ? ? ? ? PTR. inv HYP1; inv HYP2; inv inj_args; inv PTR.
                  exploit IHl; eauto.
              + intros. inv HYP1; inv HYP2; inv inj_args; inv H.
                exploit IHl; eauto.
              + destruct rhi; destruct rlo; eauto.
                * simpl.
                  destruct (mreg_eq R r); [subst R | destruct (mreg_eq R r0); [subst R| ]]; simpl.
                  -- intros _ ? ? ? ? ? PTR.
                     inv HYP1; inv HYP2; inv inj_args.
                     inv H1; inv H2.
                     inv H4; inv H9; inv H1; inv H10. inv PTR.
                     assert (not_ptr (Val.longofwords (rs3' (preg_of r)) (rs3' (preg_of r0)))).
                     { inv H6; simpl; auto. rewrite <- H in *; contradiction.
                       rewrite <- H0 in *; contradiction. }
                     exploit (inject_distributes_longofwords j__δ' (rs'0 (preg_of r)) (rs'0 (preg_of r0)) (rs3' (preg_of r)));
                       eauto.
                     intros [? ?].
                     assert (not_ptr (rs'0 (preg_of r))).
                     { destruct (rs'0 (preg_of r)); simpl; auto. }
                     inv H0; eauto. rewrite <- H9 in *; contradiction.
                  -- intros _ ? ? ? ? ? PTR.
                     inv HYP1; inv HYP2; inv inj_args.
                     inv H1; inv H2.
                     inv H4; inv H9; inv H1; inv H10. inv PTR.
                     assert (not_ptr (Val.longofwords (rs3' (preg_of r)) (rs3' (preg_of r0)))).
                     { inv H6; simpl; auto. rewrite <- H in *; contradiction.
                       rewrite <- H0 in *; contradiction. }
                     exploit (inject_distributes_longofwords j__δ' (rs'0 (preg_of r)) (rs'0 (preg_of r0)) (rs3' (preg_of r)));
                       eauto.
                     intros [? ?].
                     assert (not_ptr (rs'0 (preg_of r0))).
                     { destruct (rs'0 (preg_of r0)); simpl; auto.
                       destruct (rs'0 (preg_of r)); auto.
                       destruct (rs'0 (preg_of r)); auto. }
                     inv H4; eauto. rewrite <- H9 in *; contradiction.
                  -- intros. inv HYP1; inv HYP2; inv inj_args; inv H.
                     exploit IHl; eauto.
                * simpl.
                  destruct (mreg_eq R r); try subst R; simpl.
                  -- intros _ ? ? ? ? ? PTR.
                     inv HYP1; inv HYP2; inv inj_args.
                     inv H1; inv H2.
                     inv H4; inv H1. inv PTR.
                     assert (not_ptr (Val.longofwords (rs3' (preg_of r)) vlo0)).
                     { inv H6; simpl; auto. rewrite <- H in *; contradiction.
                       rewrite <- H0 in *; contradiction. }
                     exploit (inject_distributes_longofwords j__δ' (rs'0 (preg_of r)) vlo (rs3' (preg_of r)));
                       eauto.
                     intros [? ?].
                     assert (not_ptr (rs'0 (preg_of r))).
                     { destruct (rs'0 (preg_of r)); simpl; auto. }
                     inv H0; eauto. rewrite <- H11 in *; contradiction.
                  -- intros ? ? ? ? ? ? PTR. inv HYP1; inv HYP2; inv inj_args; inv PTR.
                     exploit IHl; eauto.
                * simpl.
                  destruct (mreg_eq R r); try subst R; simpl.
                  -- intros _ ? ? ? ? ? PTR.
                     inv HYP1; inv HYP2; inv inj_args.
                     inv H1; inv H2.
                     inv H9; inv H10. inv PTR.
                     assert (not_ptr (Val.longofwords vhi0 (rs3' (preg_of r)))).
                     { inv H6; simpl; auto. rewrite <- H in *; contradiction.
                       rewrite <- H0 in *; contradiction. }
                     exploit (inject_distributes_longofwords j__δ' vhi (rs'0 (preg_of r)) vhi0);
                       eauto.
                     intros [? ?].
                     assert (not_ptr (rs'0 (preg_of r))).
                     { destruct (rs'0 (preg_of r)); simpl; auto.
                       destruct vhi; auto.
                       destruct vhi; auto. }
                     inv H9; eauto. rewrite <- H11 in *; contradiction.
                  -- intros ? ? ? ? ? ? PTR. inv HYP1; inv HYP2; inv inj_args; inv PTR.
                     exploit IHl; eauto.
                * intros ? ? ? ? ? ? PTR. inv HYP1; inv HYP2; inv inj_args; inv PTR.
                  exploit IHl; eauto.
          }
          + exploit SP_HAS_PTR; eauto. simpl; now destruct flowsto_dec.
            intros [? [? [? [? ?]]]]. assert (b6 = x) by congruence. subst.
            eauto.
          + exploit SP_HAS_PTR0; eauto. simpl; now destruct flowsto_dec.
            intros [? [? [? [? ?]]]]. assert (b7 = x) by congruence. subst.
            eauto.
          + exploit SP_HAS_PTR; eauto. simpl; now destruct flowsto_dec.
            intros [? [? [? [? ?]]]]. assert (b6 = x) by congruence. subst.
            intros. intros X.
            eapply (defs_rev_inject _ _ _ _ j__δ) in X; eauto.
            destruct X as [? [? [? X]]].
            inv X; eauto.
            eapply H29; eauto.
      }
      destruct G as (dra1 & dsp1 & dra2 & dsp2 & st3' & j__δ'' & j__oppδ'' & rs3'' & m3'' & ? & ? & STUPD3 & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
      subst st' st'0.



      eexists (State st3' (invalidate_call rs3'' sig) m3'' _),
        j__δ'', j__oppδ''; split; [| split; [| split; [| split]]]; try assumption.
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_internal_call; eauto.
        * eapply allowed_call_preserved with (v := Vptr b' Ptrofs.zero); eauto using delta_zero.
          congruence.
          specialize (rs1_rs3' PC) as inj_pc. rewrite NEXTPC, rs3'_PC in inj_pc.
          inv inj_pc; try congruence. exploit (delta_zero s ge1 ge3); eauto; intros ->.
        * intros.
          specialize (rs1_rs3 X2). revert rs1_rs3.
          exploit SP_HAS_PTR; eauto.
          simpl. destruct flowsto_dec; simpl in *; try congruence.
          intros [? [? [-> [? ?]]]].
          intros G; inv G; eauto.
          (* exploit SP_HAS_PTR; eauto. simpl; now destruct flowsto_dec. *)
          (* intros [? [? [? ?]]]. *)
          eexists; eexists; split; eauto.
          split; eauto.
          intros. intros X.
          eapply (defs_rev_inject _ _ _ _ j__δ) in X; eauto.
          destruct X as [? [? [? X]]].
          inv X; eauto.
          eapply H11; eauto.
          exploit delta_zero; eauto. intros ->.
          replace 0 with (0 + 0) by lia.
          eapply Mem.mi_perm. eapply Mem.mi_inj. eapply partial_mem_inject.
          eapply m1_m3. eauto. eauto.
        * intros.
          specialize (rs1_rs3 X2). revert rs1_rs3.
          exploit DIFF_SP; eauto.
          simpl. destruct flowsto_dec; simpl in *; try congruence.
          intros A. unfold diff_sp_X2 in *.
          inv st_rel.
          { simpl in *. subst. simpl. unfold Vnullptr; destruct Archi.ptr64; simpl; auto. }
          simpl in *. subst. simpl in *.
          inv H22.
          -- inv H27; auto.
             exploit SP_HAS_PTR; eauto.
             simpl. destruct flowsto_dec; simpl in *; try congruence.
             intros [? [? [B ?]]]. rewrite B in *.
             intros G; inv G; eauto.
             eapply meminj_injective; eauto.
             now simpl in *.
          -- inv H27; auto.
             exploit SP_HAS_PTR; eauto.
             simpl. destruct flowsto_dec; simpl in *; try congruence.
             intros [? [? [B [? P]]]]. rewrite B in *.
             intros G; inv G; eauto.
             { eapply same_dom in m2_m3 as dom2. eapply same_dom in m1_m3 as dom1.
               assert (C: j__δ x <> None) by congruence.
               apply dom1 in C.
               assert (D: j__oppδ b5 <> None) by congruence.
               apply dom2 in D.
               destruct C.
               - destruct D.
                 + destruct H27; destruct H30. intros ?. subst b8.
                   simpl in *.
                   exploit perm_compartment1. eapply m1_m3. eauto.
                   intros [? R].
                   exploit perm_compartment2. eapply m1_m3. eapply Mem.mi_perm.
                   eapply Mem.mi_inj. eapply partial_mem_inject. eapply m1_m3.
                   eauto. eauto.
                   intros [? R'].
                   eapply partial_mem_inject in m1_m3. eapply Mem.mi_inj in m1_m3.
                   pose proof (Mem.mi_own _ _ _ m1_m3) as G.
                   specialize (G _ _ _ (Mem.block_compartment m x) _ _ _ H32 P).
                   simpl in G. exploit G; auto with comps.
                   rewrite R, R' in *.
                   intros X. inv X. rewrite <- H27 in *.
                   exploit (SP_HAS_PTR0); eauto.
                   replace (has_comp_function f0) with (has_comp_function f).
                   simpl. destruct flowsto_dec; simpl in *; try congruence.
                   { now inv EV; inv EV0. }
                   intros [? [? [E [? P']]]]. rewrite E in *.
                   exploit perm_compartment1. eapply m2_m3. eapply NONEMPTY2.
                   intros [? R''].
                   eapply partial_mem_inject in m2_m3. eapply Mem.mi_inj in m2_m3.
                   pose proof (Mem.mi_own _ _ _ m2_m3) as G'.
                   specialize (G' _ _ _ (Mem.block_compartment m2 b5) 0 Nonempty Max H22 NONEMPTY2).
                   simpl in G'. exploit G'; auto with comps.
                   rewrite R'', R' in *.
                   intros X. inv X. now destruct (s (Comp x4)).
                 + destruct H30. congruence.
               - destruct H27; congruence. }

             now simpl in *.
        * intros.
          specialize (rs1_rs3' PC). rewrite rs3'_PC, NEXTPC in rs1_rs3'.
          exploit CALLSIG; eauto.
          rewrite rs3'_PC in NEXTCOMP'. simpl in NEXTCOMP'. rewrite NEXTCOMP' in H10.
          auto.
          (* { clear -EV. inv EV; auto. } *)
          intros [fd [Hfd ->]].
          (* apply Genv.find_funct_ptr_iff in Hfd. *)
          inv rs1_rs3'.
          eapply (defs_inject _ _ _ _ _ inj_pres') in Hfd as [gd [find_gd [_ [match_gd ?]]]]; eauto.
          inv match_gd.
          inv H23; eexists; split; eauto.
        * intros ?.
          exploit Val.inject_list_not_ptr; eauto.
          eapply NO_CROSS_PTR.
          rewrite rs3'_PC in NEXTCOMP'. simpl in NEXTCOMP'. rewrite NEXTCOMP' in H10.
          auto.
        * specialize (rs1_rs3' PC); rewrite rs3'_PC, NEXTPC in rs1_rs3'.
          (* TODO: factorize *)
          eapply call_trace_preserved with (v := Vptr b' Ptrofs.zero); eauto using delta_zero.
          intros. eapply NO_CROSS_PTR.
          rewrite rs3'_PC in NEXTCOMP'. simpl in NEXTCOMP'. rewrite NEXTCOMP' in H10.
          auto.
          rewrite rs3'_PC in NEXTCOMP'. simpl in NEXTCOMP'. rewrite NEXTCOMP'. eauto.
      + destruct (side_eq (s cp') δ) as [e1 | n1].
        * left; split.
          -- econstructor; eauto.
             ++ econstructor.
                erewrite invalidate_call_PC, update_stack_call_PC, NEXTPC; simpl; eauto.
                intros ->. apply diff_comp. auto with comps.
             ++ econstructor.
                erewrite invalidate_call_PC, update_stack_call_PC; simpl; eauto.
                intros ->. apply diff_comp. auto with comps.
             ++ inv H18. inv H26; reflexivity.
             ++ eapply regset_rel_invalidate_call. eapply H20. eauto.
          -- econstructor; eauto.
             Local Opaque opposite.
             ++ econstructor.
                erewrite invalidate_call_PC, update_stack_call_PC, NEXTPC0; simpl; eauto.
                intros ->. apply diff_comp. auto with comps.
             ++ econstructor.
                erewrite invalidate_call_PC, update_stack_call_PC; simpl; eauto.
                intros ->. apply diff_comp. auto with comps.
             ++ now destruct δ.
        * right; split.
          -- econstructor; eauto.
             Local Opaque opposite.
             ++ econstructor.
                erewrite invalidate_call_PC, update_stack_call_PC, NEXTPC; simpl; eauto.
                intros ->. apply diff_comp. auto with comps.
             ++ econstructor.
                erewrite invalidate_call_PC, update_stack_call_PC; simpl; eauto.
                intros ->. apply diff_comp. auto with comps.
             ++ clear -n1.
                now destruct δ, (s cp').
          -- replace (has_comp_function f0) with (comp_of f).
             econstructor; eauto.
             ++ econstructor.
                erewrite invalidate_call_PC, update_stack_call_PC, NEXTPC0; simpl; eauto.
                intros ->. apply diff_comp. auto with comps.
             ++ econstructor.
                erewrite invalidate_call_PC, update_stack_call_PC; simpl; eauto.
                intros ->. apply diff_comp. auto with comps.
             ++ clear -n1.
                now destruct δ, (s cp').
             ++ inv H18. inv H26; reflexivity.
             ++ eapply H21.
                clear -n1.
                now destruct δ, (s cp').
             ++ clear -EV EV0.
                inv EV; inv EV0. simpl in *. congruence.


    - (* Builtin *)
      exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        unfold Genv.find_funct_ptr in H0. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        simpl in *; rewrite side_f; now destruct side_eq. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      injection A; intros -> -> ->.

      exploit eval_builtin_args_inject; eauto using delta_zero, partial_mem_inject.
      intros (vl' & eval_args' & inj_args').
      exploit external_call_inject_left; eauto using partial_mem_inject.
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      exploit extcall_preserves_mem_rel_opp_side1; [| | | eassumption | | eassumption |];
        try now inv weak_s2_s3; eauto.
      { inv weak_s2_s3; eauto.
        inv COMP1; eauto. rewrite <- SIDE.
        now rewrite H4; simpl; unfold Genv.find_comp_of_block; rewrite H5.
        rewrite H4 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H5 in *.
        exploit no_bottom2; eauto. contradiction. }
      { eapply stack_rel_comm; eauto. }
      intros [m'0_m3' st_rel''].

      eexists; exists j__δ', j__oppδ; split; [| split; [| split; [| split]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_builtin; eauto.
      + eauto.
      + eauto.
      + simpl.
        eapply stack_rel_comm in st_rel''; eauto. destruct δ; simpl in *; eauto.
      + assert (R: nextinstr (set_res res vres
                                (undef_regs (map preg_of (destroyed_by_builtin ef))
                                   (rs # X1 <- Vundef) # X31 <- Vundef)) PC =
                     Val.offset_ptr (rs PC) Ptrofs.one).
        { clear -RES_NOT_PC.
          destruct RES_NOT_PC as [reg ?]; subst res.
          Simpl.
          rewrite Asmgenproof0.set_res_other; eauto.
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
          rewrite Asmgenproof0.undef_regs_other_2; eauto. }
        assert (R': nextinstr (set_res res vres'
                                 (undef_regs (map preg_of (destroyed_by_builtin ef))
                                    (rs3 # X1 <- Vundef) # X31 <- Vundef)) PC =
                      Val.offset_ptr (rs3 PC) Ptrofs.one).
        { clear -RES_NOT_PC.
          destruct RES_NOT_PC as [reg ?]; subst res.
          Simpl.
          rewrite Asmgenproof0.set_res_other; eauto.
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
          rewrite Asmgenproof0.undef_regs_other_2; eauto. }
        assert (R0: nextinstr (set_res res0 vres0
                                 (undef_regs (map preg_of (destroyed_by_builtin ef0))
                                    (rs2 # X1 <- Vundef) # X31 <- Vundef)) PC =
                      Val.offset_ptr (rs2 PC) Ptrofs.one).
        { clear -RES_NOT_PC0.
          destruct RES_NOT_PC0 as [reg ?]; subst res0.
          Simpl.
          rewrite Asmgenproof0.set_res_other; eauto.
          assert (H': Asmgenproof0.preg_notin PC (destroyed_by_builtin ef0)).
          { Local Transparent destroyed_by_builtin.
            unfold destroyed_by_builtin.
            destruct ef0; simpl; auto.
            - destruct orb; simpl; intuition.
              destruct orb; simpl; intuition.
            - intuition.
            - induction clobbers.
              + simpl; auto.
              + simpl. destruct register_by_name; auto.
                simpl; intuition.
                destruct (destroyed_by_clobber clobbers); [| split]; now destruct m.
                Local Opaque destroyed_by_builtin. }
          rewrite Asmgenproof0.undef_regs_other_2; eauto. }
        left; split.
        * inv strong_s1_s3; econstructor; eauto.
          -- econstructor; eauto. rewrite R. inv COMP1; eauto.
             now rewrite H in *.
             rewrite H in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H0 in *.
             exploit no_bottom1; eauto.
          -- econstructor; eauto. rewrite R'. inv COMP2; eauto.
             now rewrite eq_pc' in *.
             rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *.
             exploit no_bottom1; eauto.
          -- eapply regset_rel_return_from_builtin; eauto.
        * inv weak_s2_s3; inv A; econstructor; eauto.
          -- econstructor; eauto. rewrite R0. inv COMP1; eauto.
             now rewrite H4 in *.
             rewrite H4 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H5 in *.
             exploit no_bottom2; eauto.
          -- econstructor; eauto. rewrite R'. inv COMP2; eauto.
             now rewrite eq_pc' in *.
             rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *.
             exploit no_bottom1; eauto.

    - (* builtin / external call *)
      exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_prog. rewrite find_id.
        unfold Genv.find_funct_ptr in H0. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        simpl in *; rewrite side_f; now destruct side_eq. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      injection A; intros -> -> ->.

      exploit eval_builtin_args_inject; eauto using delta_zero, partial_mem_inject.
      intros (vl' & eval_args' & inj_args').
      exploit external_call_inject_left; eauto using partial_mem_inject.
      (* rewrite ALLOWED; auto. *)
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      exploit extcall_preserves_mem_rel_opp_side1; [| | | eassumption | | eassumption |];
        try now inv weak_s2_s3; eauto.
      { inv weak_s2_s3; eauto.
        inv COMP1; eauto. rewrite <- SIDE.
        rewrite H4 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H5 in *.
        simpl in *; congruence. }
      { eapply stack_rel_comm; eauto. }
      intros [m'0_m3' st_rel''].

      eexists; exists j__δ', j__oppδ; split; [| split; [| split; [| split]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_builtin; eauto.
      + eauto.
      + eauto.
      + simpl. eapply stack_rel_comm in st_rel''; destruct δ; eauto.
      + assert (R: nextinstr (set_res res vres
                                (undef_regs (map preg_of (destroyed_by_builtin ef))
                                   (rs # X1 <- Vundef) # X31 <- Vundef)) PC =
                     Val.offset_ptr (rs PC) Ptrofs.one).
        { clear -RES_NOT_PC.
          destruct RES_NOT_PC as [reg ?]; subst res.
          Simpl.
          rewrite Asmgenproof0.set_res_other; eauto.
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
          rewrite Asmgenproof0.undef_regs_other_2; eauto. }
        assert (R': nextinstr (set_res res vres'
                                 (undef_regs (map preg_of (destroyed_by_builtin ef))
                                    (rs3 # X1 <- Vundef) # X31 <- Vundef)) PC =
                      Val.offset_ptr (rs3 PC) Ptrofs.one).
        { clear -RES_NOT_PC.
          destruct RES_NOT_PC as [reg ?]; subst res.
          Simpl.
          rewrite Asmgenproof0.set_res_other; eauto.
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
          rewrite Asmgenproof0.undef_regs_other_2; eauto. }
        left; split.
        * inv strong_s1_s3; econstructor; eauto.
          -- econstructor; eauto. rewrite R. inv COMP1; eauto.
             now rewrite H in *.
             rewrite H in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H0 in *.
             exploit no_bottom1; eauto.
          -- econstructor; eauto. rewrite R'. inv COMP2; eauto.
             now rewrite eq_pc' in *.
             rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *.
             exploit no_bottom1; eauto.
          -- eapply regset_rel_return_from_builtin; eauto.
        * inv weak_s2_s3; inv A; econstructor; eauto.
          -- econstructor; eauto. Simpl.
             inv COMP1; eauto.
             rewrite H4 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H5 in *.
             contradiction.
          -- econstructor; eauto. rewrite R'. inv COMP2; eauto.
             now rewrite eq_pc' in *.
             rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *.
             exploit no_bottom1; eauto.

    - (* external_call / builtin *)
      exploit strong_equiv_state_external_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & ? & eq_pc' & find_funct & m1_m3 & rs1_rs3);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      injection A; intros <- <- <-.

      exploit extcall_arguments_preserved; eauto.
      intros (args' & inj_args & extcall_args').


      exploit (extcall_preserves_mem_rel_opp_side1 s (comp_of f) cp_main ge2 ge1 ge3 j__oppδ j__δ (opposite δ)
                 m0 m'0 m m3); eauto.
      { inv weak_s2_s3; eauto.
        inv COMP1; eauto. rewrite <- SIDE.
        rewrite H3 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H4 in *.
        simpl in *; congruence.
        rewrite H3 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H4 in *.
        simpl in *; congruence. }
      { eapply stack_rel_comm; eauto. }
      intros [m'0_m3 st_rel''].

      exploit external_call_inject_left; try eassumption.
      inv strong_s1_s3; eauto.
      inv strong_s1_s3; eauto.
      { inv strong_s1_s3; inv weak_s2_s3; eauto.
        inv COMP1; eauto.
        rewrite H in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H0 in *.
        simpl in *; congruence. }
      { eapply stack_rel_comm in st_rel''; destruct δ; eauto. }
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      eexists; exists j__δ', j__oppδ; split; [| split; [| split; [| split]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_external; eauto.
      + eauto.
      + eauto.
      + simpl. eauto.
      + left; split.
        * inv strong_s1_s3; econstructor; eauto.
          -- econstructor; eauto. Simpl.
             inv COMP1; eauto.
             rewrite H in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H0 in *.
             simpl in *; congruence.
          -- econstructor; eauto. Simpl.
             inv COMP2; eauto.
             rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *.
             simpl in *; congruence.
          -- eapply regset_rel_return_from_external; eauto.
        * assert (R: nextinstr (set_res res0 vres
                                  (undef_regs (map preg_of (destroyed_by_builtin ef0))
                                     (rs0 # X1 <- Vundef) # X31 <- Vundef)) PC =
                       Val.offset_ptr (rs0 PC) Ptrofs.one).
          { clear -RES_NOT_PC.
            destruct RES_NOT_PC as [reg ?]; subst res0.
            Simpl.
            rewrite Asmgenproof0.set_res_other; eauto.
            assert (H': Asmgenproof0.preg_notin PC (destroyed_by_builtin ef0)).
            { Local Transparent destroyed_by_builtin.
              unfold destroyed_by_builtin.
              destruct ef0; simpl; auto.
              - destruct orb; simpl; intuition.
                destruct orb; simpl; intuition.
              - intuition.
              - induction clobbers.
                + simpl; auto.
                + simpl. destruct register_by_name; auto.
                  simpl; intuition.
                  destruct (destroyed_by_clobber clobbers); [| split]; now destruct m.
                  Local Opaque destroyed_by_builtin. }
            rewrite Asmgenproof0.undef_regs_other_2; eauto. }
          inv weak_s2_s3; inv A; econstructor; eauto.
          -- econstructor; eauto. rewrite R.
             inv COMP1; eauto.
             rewrite H3 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H4 in *.
             simpl in *; congruence.
             rewrite H3 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H4 in *.
             simpl in *; congruence.
          -- econstructor; eauto. Simpl.
             inv COMP2; eauto.
             rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *.
             simpl in *; congruence.

    - (* External call *)
      exploit strong_equiv_state_external_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & ? & eq_pc' & find_funct & m1_m3 & rs1_rs3);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      injection A; intros <- <- <-.

      exploit extcall_arguments_preserved; eauto.
      intros (args' & inj_args & extcall_args').

      assert (cp0 = cp) as ->.
      { inv strong_s1_s3; inv weak_s2_s3; eauto.
        inv COMP1; eauto.
        rewrite H in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H0 in *.
        simpl in *; congruence.
        inv COMP0; eauto.
        rewrite H3 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H4 in *.
        simpl in *; congruence.
        inv COMP3; eauto.
        rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *.
        simpl in *; congruence. }


      exploit (extcall_preserves_mem_rel_opp_side1 s cp cp_main ge2 ge1 ge3 j__oppδ j__δ (opposite δ)
                 m0 m'0 m m3); eauto;
        try now inv weak_s2_s3; eauto.
      { inv strong_s1_s3; inv weak_s2_s3; eauto.
        inv COMP1; eauto.
        rewrite H in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H0 in *.
        simpl in *; congruence.
        now destruct s. }
      { eapply stack_rel_comm; eauto. }
      intros [m'0_m3 st_rel''].

      exploit external_call_inject_left; try eassumption.
      inv weak_s2_s3; eauto.
      inv weak_s2_s3; eauto.
      { inv strong_s1_s3; inv weak_s2_s3; eauto.
        inv COMP1; eauto.
        rewrite H in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H0 in *.
        simpl in *; congruence. }
      eapply stack_rel_comm in st_rel''; destruct δ; eauto.
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      remember ((set_pair (loc_external_result (ef_sig ef)) vres' (undef_caller_save_regs rs3)) # PC <- (rs3 X1)) as rs3'.
      exists (ReturnState st3 rs3' m3' bottom).
      exists j__δ', j__oppδ; split; [| split; [| split; [| split]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_external; eauto.
      + eauto.
      + eauto.
      + simpl. eauto.
      + left; split.
        * inv strong_s1_s3; econstructor; eauto.
          -- econstructor; eauto. Simpl.
             inv COMP1; eauto.
             rewrite H in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H0 in *.
             simpl in *; congruence.
          -- econstructor; eauto. Simpl.
             inv COMP2; eauto.
             rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *.
             simpl in *; congruence.
          -- eapply regset_rel_return_from_external; eauto.
        * inv weak_s2_s3; inv A; econstructor; eauto.
          -- econstructor; eauto. Simpl.
             inv COMP1; eauto.
             rewrite H3 in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite H4 in *.
             simpl in *; congruence.
          -- econstructor; eauto. Simpl.
             inv COMP2; eauto.
             rewrite eq_pc' in *; simpl in *; unfold Genv.find_comp_of_block in *; rewrite find_funct in *.
             simpl in *; congruence.
  Qed.

End Theorems.

Section Simulation.
  Context (c1 c2 p1 p2: Asm.program).
  Variable s: split.

  Context (W1 W2 W3: Asm.program).
  Hypothesis c1_p1: link p1 c1 = Some W1.
  Hypothesis c2_p2: link p2 c2 = Some W2.
  Hypothesis c2_p1: link p1 c2 = Some W3.

  Hypothesis match_W1_W3: match_prog s Left W1 W3.
  Hypothesis match_W2_W3: match_prog s Right W2 W3.

  Notation cp_main := (comp_of_main W1).

  (* Hypothesis cp_main_not_none: *)
  (*   cp_main <> None. *)

  Hypothesis norepet1: list_norepet (prog_defs_names W1).
  Hypothesis norepet2: list_norepet (prog_defs_names W2).

  Notation ge1 := (Genv.globalenv W1).
  Notation ge2 := (Genv.globalenv W2).
  Notation ge3 := (Genv.globalenv W3).

  Hypothesis no_bottom1: forall b f,
      Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
      comp_of f <> bottom.
  Hypothesis no_top1: forall b f,
      Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
      comp_of f <> top.
  Hypothesis no_bottom2: forall b f,
      Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
      comp_of f <> bottom.
  Hypothesis no_top2: forall b f,
      Genv.find_def ge2 b = Some (Gfun (Internal f)) ->
      comp_of f <> top.
  Hypothesis no_bottom3: forall b f,
      Genv.find_def ge3 b = Some (Gfun (Internal f)) ->
      comp_of f <> bottom.
  Hypothesis no_top3: forall b f,
      Genv.find_def ge3 b = Some (Gfun (Internal f)) ->
      comp_of f <> top.

  Hypothesis no_bottom1': forall b v,
      Genv.find_def ge1 b = Some (Gvar v) ->
      comp_of v <> bottom.
  Hypothesis no_top1': forall b v,
      Genv.find_def ge1 b = Some (Gvar v) ->
      comp_of v <> top.
  Hypothesis no_bottom2': forall b v,
      Genv.find_def ge2 b = Some (Gvar v) ->
      comp_of v <> bottom.
  Hypothesis no_top2': forall b v,
      Genv.find_def ge2 b = Some (Gvar v) ->
      comp_of v <> top.
  Hypothesis no_bottom3': forall b v,
      Genv.find_def ge3 b = Some (Gvar v) ->
      comp_of v <> bottom.
  Hypothesis no_top3': forall b v,
      Genv.find_def ge3 b = Some (Gvar v) ->
      comp_of v <> top.

  Hypothesis same_cp_main1:
    Genv.find_comp_in_genv ge2 (Genv.symbol_address ge2 (prog_main W2) Ptrofs.zero) =
      Genv.find_comp_in_genv ge1 (Genv.symbol_address ge1 (prog_main W1) Ptrofs.zero).
  Hypothesis same_cp_main2:
    Genv.find_comp_in_genv ge3 (Genv.symbol_address ge3 (prog_main W3) Ptrofs.zero) =
      Genv.find_comp_in_genv ge1 (Genv.symbol_address ge1 (prog_main W1) Ptrofs.zero).

  Hypothesis same_low_half1: low_half ge1 = low_half ge3.
  Hypothesis same_low_half2: low_half ge2 = low_half ge3.

  Hypothesis found_in_W3_kept1: forall id v,
      (s (comp_of v) = Left -> In (id, Gvar v) (prog_defs W3) ->
       kept_prog s W1 Left id = true).
  Hypothesis found_in_W3_kept2: forall id v,
      (s (comp_of v) = Right -> In (id, Gvar v) (prog_defs W3) ->
       kept_prog s W2 Right id = true).

  Lemma kept_prog_kept_genv: forall s W δ id,
      kept_prog s W δ id = true -> kept_genv s (Genv.globalenv W) δ id = true.
  Proof.
    unfold kept_prog, kept_genv. intros ? ? ? ?.
    destruct Genv.find_symbol; try discriminate.
    fold (Genv.find_def (Genv.globalenv W) b). destruct Genv.find_def; auto.
    destruct g; auto.
  Qed.

  Hypothesis main_not_top: Genv.find_comp_in_genv ge1 (Genv.symbol_address ge1 (prog_main W1) Ptrofs.zero) <> top.
  Hypothesis main_not_bottom: Genv.find_comp_in_genv ge1 (Genv.symbol_address ge1 (prog_main W1) Ptrofs.zero) <> bottom.

  Lemma bytes_of_init_inject:
    forall m tm,
      Genv.init_mem W1 = Some m ->
      Genv.init_mem W3 = Some tm ->
      forall il,
        (forall id ofs, In (Init_addrof id ofs) il -> False) ->
        (* (forall id, ref_init il id -> kept id) -> *)
        list_forall2 (memval_inject (init_meminj s Left W1 W3)) (Genv.bytes_of_init_data_list ge1 il)
          (Genv.bytes_of_init_data_list ge3 il).
  Proof.
    induction il as [ | i1 il]; simpl; intros.
    - constructor.
    - apply list_forall2_app.
      + destruct i1; simpl; try (apply inj_bytes_inject).
        induction (Z.to_nat z); simpl; constructor. constructor. auto.
        exploit H1; eauto. contradiction.
      + apply IHil. eauto.
  Qed.

  Lemma bytes_of_init_inject':
    forall m tm,
      Genv.init_mem W2 = Some m ->
      Genv.init_mem W3 = Some tm ->
      forall il,
        (forall id ofs, In (Init_addrof id ofs) il -> False) ->
        (* (forall id, ref_init il id -> kept id) -> *)
        list_forall2 (memval_inject (init_meminj s Right W2 W3)) (Genv.bytes_of_init_data_list ge2 il)
          (Genv.bytes_of_init_data_list ge3 il).
  Proof.
    induction il as [ | i1 il]; simpl; intros.
    - constructor.
    - apply list_forall2_app.
      + destruct i1; simpl; try (apply inj_bytes_inject).
        induction (Z.to_nat z); simpl; constructor. constructor. auto.
        exploit H1; eauto. contradiction.
      + apply IHil. eauto.
  Qed.

  Lemma Mem_getN_forall2:
    forall (P: memval -> memval -> Prop) c1 c2 i n p,
      list_forall2 P (Mem.getN n p c1) (Mem.getN n p c2) ->
      p <= i -> i < p + Z.of_nat n ->
      P (ZMap.get i c1) (ZMap.get i c2).
  Proof.
    induction n; simpl Mem.getN; intros.
    - simpl in H1. extlia.
    - inv H. rewrite Nat2Z.inj_succ in H1. destruct (zeq i p).
      + congruence.
      + apply IHn with (p + 1); auto. lia. lia.
  Qed.

  Hypothesis no_init_ptr1: forall b v, Genv.find_def ge1 b = Some (Gvar v) ->
                                  forall (id : ident) (ofs0 : ptrofs), In (Init_addrof id ofs0) (gvar_init v) -> False.
  Hypothesis no_init_ptr2: forall b v, Genv.find_def ge2 b = Some (Gvar v) ->
                                  forall (id : ident) (ofs0 : ptrofs), In (Init_addrof id ofs0) (gvar_init v) -> False.
  Hypothesis no_init_ptr3: forall b v, Genv.find_def ge3 b = Some (Gvar v) ->
                                  forall (id : ident) (ofs0 : ptrofs), In (Init_addrof id ofs0) (gvar_init v) -> False.

  Lemma init_mem_correct1: forall m1 m3, Genv.init_mem W1 = Some m1 ->
                                    Genv.init_mem W3 = Some m3 ->
                                    mem_rel s ge1 ge3 (init_meminj s Left W1 W3) Left m1 m3.
  Proof.
    intros. constructor.
    - intros ?. simpl. unfold init_meminj.
      split.
      + destruct Genv.invert_symbol eqn:IS; try congruence.
        destruct kept_genv eqn:EQ; try congruence.
        apply Genv.invert_find_symbol in IS.
        unfold kept_genv in EQ. rewrite IS in EQ.
        fold (Genv.find_def ge1 b) in EQ. destruct Genv.find_def as [[]|] eqn:FD; try now auto.
        * intros; now right; eauto.
        * intros ?. left.
          exploit (Genv.init_mem_find_def W1); eauto. intros ->.
          simpl in *. split.
          now destruct side_eq.
          eapply Genv.find_symbol_not_fresh; eauto.
      + intros [[X Y] | [fd X]].
        * exploit (Genv.find_def_init_mem W1); eauto.
          intros [g [? ?]].
          exploit Genv.find_def_find_symbol_inversion; eauto.
          intros [id FS]. eapply Genv.find_invert_symbol in FS as IS.
          rewrite IS.
          assert (R: kept_genv s ge1 Left id = true).
          { unfold kept_genv. rewrite FS. fold (Genv.find_def ge1 b).
            rewrite H1. destruct g; auto. simpl in *; rewrite H2.
            now destruct s. }
          rewrite R.
          exploit (symbols_inject2 s Left W1); eauto using init_meminj_preserves_globals.
          intros [? [-> ?]]. congruence.
        *
          exploit Genv.find_def_find_symbol_inversion; eauto.
          intros [id FS]. eapply Genv.find_invert_symbol in FS as IS.
          rewrite IS.
          assert (R: kept_genv s ge1 Left id = true).
          { unfold kept_genv. rewrite FS. fold (Genv.find_def ge1 b).
            rewrite X. auto. }
          rewrite R.
          exploit (symbols_inject2 s Left W1); eauto using init_meminj_preserves_globals.
          intros [? [-> ?]]. congruence.

    - constructor.
      + { constructor; intros.
          - exploit init_meminj_invert; eauto.
            intros [? [? [? ?]]]. subst.
            eapply Genv.find_symbol_find_def_inversion in H4 as G1.
            destruct G1 as [gd G1].
            eapply Genv.find_symbol_find_def_inversion in H5 as G2.
            destruct G2 as [gd' G2].
            exploit (Genv.init_mem_characterization_gen W1); eauto.
            exploit (Genv.init_mem_characterization_gen W3); eauto.
            assert (match_globdef gd gd') as G.
            { exploit defs_inject; eauto.
              eapply init_meminj_preserves_globals; eauto.
              intros [? [? [? [? ?]]]]. congruence. }
            inv G.
            + intros. exploit H7; eauto. contradiction.
            + intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
              apply Q1 in H2. destruct H2. subst.
              apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
              inv H3.
              apply P2. simpl in *. lia.
          - exploit init_meminj_invert; eauto. intros (A & id & B & C).
            subst delta.
            (* destruct cp as [cp|]; simpl in *; trivial. *)
            destruct (Genv.find_symbol_find_def_inversion _ _ B) as [g B'].
            assert ((prog_defmap W1) ! id = Some g) as DEF1.
            { apply Genv.find_def_symbol. eauto. }
            destruct (Genv.find_symbol_find_def_inversion _ _ C) as [g' C'].
            assert ((prog_defmap W3) ! id = Some g') as DEF2.
            { apply Genv.find_def_symbol. eauto. }

            destruct (kept_prog s W1 Left id) eqn:G; try congruence.
            + pose proof (match_prog_def _ _ _ _ match_W1_W3 id G) as DEF2'.
              rewrite DEF1, DEF2 in DEF2'.
              injection DEF2' as ->.
              simpl in *.
              rewrite (Genv.init_mem_find_def _ _ H B') in *.
              now rewrite (Genv.init_mem_find_def _ _ H0 C') in *.
            + pose proof (match_prog_notdef _ _ _ _ match_W1_W3 id G) as DEF2'.
              rewrite DEF1, DEF2 in DEF2'.
              inv DEF2'. inv H6. inv H4.
              (* injection DEF2' as ->. *)
              simpl in *.
              rewrite (Genv.init_mem_find_def _ _ H B') in *.
              now rewrite (Genv.init_mem_find_def _ _ H0 C') in *.
              simpl in *.
              rewrite (Genv.init_mem_find_def _ _ H B') in *.
              now rewrite (Genv.init_mem_find_def _ _ H0 C') in *.
              inv H4.
              simpl in *.
              rewrite (Genv.init_mem_find_def _ _ H B') in *.
              now rewrite (Genv.init_mem_find_def _ _ H0 C') in *.
          - exploit init_meminj_invert; eauto. intros (A & id & B & C).
            subst delta. apply Z.divide_0_r.
          - exploit init_meminj_invert; eauto.
            intros [? [? [? ?]]]. subst.
            eapply Genv.find_symbol_find_def_inversion in H4 as G1.
            destruct G1 as [gd G1].
            eapply Genv.find_symbol_find_def_inversion in H5 as G2.
            destruct G2 as [gd' G2].
            exploit (Genv.init_mem_characterization_gen W1); eauto.
            exploit (Genv.init_mem_characterization_gen W3); eauto.
            assert (match_globdef gd gd') as G.
            { exploit defs_inject; eauto.
              eapply init_meminj_preserves_globals; eauto.
              intros [? [? [? [? ?]]]]. congruence. }
            inv G.
            + intros. exploit H7; eauto. contradiction.
            + intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
              apply Q1 in H2. destruct H2.
              assert (NO: gvar_volatile v = false).
              { unfold Genv.perm_globvar in H6. destruct (gvar_volatile v); auto. inv H6. }
              assert (NO': gvar_volatile v' = false).
              { inv H3. simpl in *. eauto. }
              (* inv H3. simpl in *. *)
              Local Transparent Mem.loadbytes.
              generalize (S1 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; destruct Mem.can_access_block_dec; intros E1; inv E1.
              * generalize (S2 NO'). unfold Mem.loadbytes. destruct Mem.range_perm_dec; destruct Mem.can_access_block_dec; intros E2; inv E2.
                rewrite Z.add_0_r.
                apply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v'))).
                assert ((init_data_list_size (gvar_init v')) = (init_data_list_size (gvar_init v))) as EQ.
                { inv H3. simpl in *. eauto. }
                rewrite H9. rewrite EQ. rewrite H8.
                inv H3; simpl in *; subst.
                eapply bytes_of_init_inject. eauto. eauto. eauto.
                lia.
                rewrite Z2Nat.id by (apply Z.ge_le; apply init_data_list_size_pos). inv H3; simpl in *; lia.
                destruct (Z_le_dec); inv H4.
                rewrite Z.add_0_r.
                apply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v))).
                simpl in *. inv H9. inv H3; simpl in *.
                rewrite H8, H7.
                eapply bytes_of_init_inject. eauto. eauto. eauto.
                lia. lia. auto. inv H9.
              * destruct (Z_le_dec); inv H8.
                generalize (S2 NO'). unfold Mem.loadbytes. destruct Mem.range_perm_dec; destruct Mem.can_access_block_dec; intros E2; inv E2.
                rewrite Z.add_0_r.
                apply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v))).
                assert ((init_data_list_size (gvar_init v')) = (init_data_list_size (gvar_init v))) as EQ.
                { inv H3. simpl in *. eauto. }
                rewrite H9.
                inv H3; simpl in *; subst.
                rewrite H8.
                eapply bytes_of_init_inject. eauto. eauto. eauto.
                lia. lia. lia. }
      + intros.
        destruct (init_meminj s Left W1 W3 b) as [[b' delta]|] eqn:INJ; auto.
        elim H1. exploit init_meminj_invert; eauto. intros (A & id & B & C).
        eapply Genv.find_symbol_not_fresh; eauto.
      + intros. exploit init_meminj_invert; eauto. intros (A & id & B & C).
        eapply Genv.find_symbol_not_fresh; eauto.
      + red; intros.
        exploit init_meminj_invert. eexact H2. intros (A1 & id1 & B1 & C1).
        exploit init_meminj_invert. eexact H3. intros (A2 & id2 & B2 & C2).
        destruct (ident_eq id1 id2). congruence. left; eapply Genv.global_addresses_distinct; eauto.
      + intros. exploit init_meminj_invert; eauto. intros (A & id & B & C). subst delta.
        split. lia. generalize (Ptrofs.unsigned_range_2 ofs). lia.
      + intros. exploit init_meminj_invert; eauto.
        intros [? [? [? ?]]]. subst.
        eapply Genv.find_symbol_find_def_inversion in H4 as G1.
        destruct G1 as [gd G1].
        eapply Genv.find_symbol_find_def_inversion in H5 as G2.
        destruct G2 as [gd' G2].
        exploit (Genv.init_mem_characterization_gen W1); eauto.
        exploit (Genv.init_mem_characterization_gen W3); eauto.
        assert (match_globdef gd gd') as G.
        { exploit defs_inject; eauto.
          eapply init_meminj_preserves_globals; eauto.
          intros [? [? [? [? ?]]]]. congruence. }
        inv G.
        * intros. exploit H6; eauto.
        * intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
          apply Q2 in H2. destruct H2. subst.
          left. apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
          inv H3; simpl in *; subst.
          apply P1. lia.
    - intros ?. unfold init_meminj. destruct (Genv.invert_symbol); try discriminate.
      destruct kept_genv; try discriminate. destruct Genv.find_symbol; try discriminate.
      congruence.
    - intros.
      eapply Mem.perm_valid_block in H1 as ?.
      exploit (Genv.find_def_init_mem W1); eauto.
      intros [g [? ?]].
      exploit (Genv.init_mem_characterization_gen W1); eauto.
      intros X.
      destruct g; try now exploit X; eauto.
      rewrite <- H4.
      eapply no_bottom1' in H3 as ?.
      eapply no_top1' in H3 as ?. simpl.
      destruct (comp_of v); eauto; try now contradiction.
    - intros.
      eapply Mem.perm_valid_block in H1 as ?.
      exploit (Genv.find_def_init_mem W3); eauto.
      intros [g [? ?]].
      exploit (Genv.init_mem_characterization_gen W3); eauto.
      intros X.
      destruct g; try now exploit X; eauto.
      rewrite <- H4.
      eapply no_bottom3' in H3 as ?.
      eapply no_top3' in H3 as ?. simpl.
      destruct (comp_of v); eauto; try now contradiction.
    - eapply Genv.init_mem_genv_next in H. simpl. rewrite H. now apply Ple_refl.
    - eapply Genv.init_mem_genv_next in H0. simpl. rewrite H0. now apply Ple_refl.
    - intros. eapply Genv.find_def_not_fresh; eauto.
    - intros. eapply Genv.find_def_not_fresh; eauto.
    - intros. exploit (Genv.init_mem_characterization_gen W1); eauto.
    - intros. exploit (Genv.init_mem_characterization_gen W3); eauto.
    - intros. exploit (Genv.init_mem_find_def W1); eauto.
    - intros. unfold init_meminj in *.
      destruct (Genv.invert_symbol ge1 b0) eqn:find_b0; try discriminate.
      destruct (Genv.invert_symbol ge1 b4) eqn:find_b4; try discriminate.
      destruct (kept_genv s ge1 Left i ) eqn:kept_b0; try discriminate.
      destruct (kept_genv s ge1 Left i0 ) eqn:kept_b4; try discriminate.
      destruct (Genv.find_symbol ge3 i) eqn:find_i; try discriminate.
      destruct (Genv.find_symbol ge3 i0) eqn:find_i0; try discriminate. inv H3. inv H2.
      intros ?. subst.
      apply Genv.find_invert_symbol in find_i, find_i0.
      assert (i = i0) by congruence. subst i0.
      apply Genv.invert_find_symbol in find_b0, find_b4.
      assert (b0 = b4) by congruence. contradiction.
  Qed.

  Lemma init_mem_correct2: forall m2 m3, Genv.init_mem W2 = Some m2 ->
                                    Genv.init_mem W3 = Some m3 ->
                                    mem_rel s ge2 ge3 (init_meminj s Right W2 W3) Right m2 m3.
  Proof.
    intros. constructor.
    - intros ?. simpl. unfold init_meminj.
      split.
      + destruct Genv.invert_symbol eqn:IS; try congruence.
        destruct kept_genv eqn:EQ; try congruence.
        apply Genv.invert_find_symbol in IS.
        unfold kept_genv in EQ. rewrite IS in EQ.
        fold (Genv.find_def ge2 b) in EQ. destruct Genv.find_def as [[]|] eqn:FD; try now auto.
        * intros; now right; eauto.
        * intros ?. left.
          exploit (Genv.init_mem_find_def W2); eauto. intros ->.
          simpl in *. split.
          now destruct side_eq.
          eapply Genv.find_symbol_not_fresh; eauto.
      + intros [[X Y] | [fd X]].
        * exploit (Genv.find_def_init_mem W2); eauto.
          intros [g [? ?]].
          exploit Genv.find_def_find_symbol_inversion; eauto.
          intros [id FS]. eapply Genv.find_invert_symbol in FS as IS.
          rewrite IS.
          assert (R: kept_genv s ge2 Right id = true).
          { unfold kept_genv. rewrite FS. fold (Genv.find_def ge2 b).
            rewrite H1. destruct g; auto. simpl in *; rewrite H2.
            now destruct s. }
          rewrite R.
          exploit (symbols_inject2 s Right W2); eauto using init_meminj_preserves_globals.
          intros [? [-> ?]]. congruence.
        *
          exploit Genv.find_def_find_symbol_inversion; eauto.
          intros [id FS]. eapply Genv.find_invert_symbol in FS as IS.
          rewrite IS.
          assert (R: kept_genv s ge2 Right id = true).
          { unfold kept_genv. rewrite FS. fold (Genv.find_def ge2 b).
            rewrite X. auto. }
          rewrite R.
          exploit (symbols_inject2 s Right W2); eauto using init_meminj_preserves_globals.
          intros [? [-> ?]]. congruence.

    - constructor.
      + { constructor; intros.
          - exploit init_meminj_invert; eauto.
            intros [? [? [? ?]]]. subst.
            eapply Genv.find_symbol_find_def_inversion in H4 as G1.
            destruct G1 as [gd G1].
            eapply Genv.find_symbol_find_def_inversion in H5 as G2.
            destruct G2 as [gd' G2].
            exploit (Genv.init_mem_characterization_gen W2); eauto.
            exploit (Genv.init_mem_characterization_gen W3); eauto.
            assert (match_globdef gd gd') as G.
            { exploit defs_inject; eauto.
              eapply init_meminj_preserves_globals; eauto.
              intros [? [? [? [? ?]]]]. congruence. }
            inv G.
            + intros. exploit H7; eauto. contradiction.
            + intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
              apply Q1 in H2. destruct H2. subst.
              apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
              inv H3.
              apply P2. simpl in *. lia.
          - exploit init_meminj_invert; eauto. intros (A & id & B & C).
            subst delta.
            (* destruct cp as [cp|]; simpl in *; trivial. *)
            destruct (Genv.find_symbol_find_def_inversion _ _ B) as [g B'].
            assert ((prog_defmap W2) ! id = Some g) as DEF1.
            { apply Genv.find_def_symbol. eauto. }
            destruct (Genv.find_symbol_find_def_inversion _ _ C) as [g' C'].
            assert ((prog_defmap W3) ! id = Some g') as DEF2.
            { apply Genv.find_def_symbol. eauto. }

            destruct (kept_prog s W2 Right id) eqn:G; try congruence.
            + pose proof (match_prog_def _ _ _ _ match_W2_W3 id G) as DEF2'.
              rewrite DEF1, DEF2 in DEF2'.
              injection DEF2' as ->.
              simpl in *.
              rewrite (Genv.init_mem_find_def _ _ H B') in *.
              now rewrite (Genv.init_mem_find_def _ _ H0 C') in *.
            + pose proof (match_prog_notdef _ _ _ _ match_W2_W3 id G) as DEF2'.
              rewrite DEF1, DEF2 in DEF2'.
              inv DEF2'. inv H6. inv H4.
              (* injection DEF2' as ->. *)
              simpl in *.
              rewrite (Genv.init_mem_find_def _ _ H B') in *.
              now rewrite (Genv.init_mem_find_def _ _ H0 C') in *.
              simpl in *.
              rewrite (Genv.init_mem_find_def _ _ H B') in *.
              now rewrite (Genv.init_mem_find_def _ _ H0 C') in *.
              inv H4.
              simpl in *.
              rewrite (Genv.init_mem_find_def _ _ H B') in *.
              now rewrite (Genv.init_mem_find_def _ _ H0 C') in *.
          - exploit init_meminj_invert; eauto. intros (A & id & B & C).
            subst delta. apply Z.divide_0_r.
          - exploit init_meminj_invert; eauto.
            intros [? [? [? ?]]]. subst.
            eapply Genv.find_symbol_find_def_inversion in H4 as G1.
            destruct G1 as [gd G1].
            eapply Genv.find_symbol_find_def_inversion in H5 as G2.
            destruct G2 as [gd' G2].
            exploit (Genv.init_mem_characterization_gen W2); eauto.
            exploit (Genv.init_mem_characterization_gen W3); eauto.
            assert (match_globdef gd gd') as G.
            { exploit defs_inject; eauto.
              eapply init_meminj_preserves_globals; eauto.
              intros [? [? [? [? ?]]]]. congruence. }
            inv G.
            + intros. exploit H7; eauto. contradiction.
            + intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
              apply Q1 in H2. destruct H2.
              assert (NO: gvar_volatile v = false).
              { unfold Genv.perm_globvar in H6. destruct (gvar_volatile v); auto. inv H6. }
              assert (NO': gvar_volatile v' = false).
              { inv H3. simpl in *. eauto. }
              (* inv H3. simpl in *. *)
              Local Transparent Mem.loadbytes.
              generalize (S1 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; destruct Mem.can_access_block_dec; intros E1; inv E1.
              * generalize (S2 NO'). unfold Mem.loadbytes. destruct Mem.range_perm_dec; destruct Mem.can_access_block_dec; intros E2; inv E2.
                rewrite Z.add_0_r.
                apply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v'))).
                assert ((init_data_list_size (gvar_init v')) = (init_data_list_size (gvar_init v))) as EQ.
                { inv H3. simpl in *. eauto. }
                rewrite H9. rewrite EQ. rewrite H8.
                inv H3; simpl in *; subst.
                eapply bytes_of_init_inject'. eauto. eauto. eauto.
                lia.
                rewrite Z2Nat.id by (apply Z.ge_le; apply init_data_list_size_pos). inv H3; simpl in *; lia.
                destruct (Z_le_dec); inv H4.
                rewrite Z.add_0_r.
                apply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v))).
                simpl in *. inv H9. inv H3; simpl in *.
                rewrite H8, H7.
                eapply bytes_of_init_inject'. eauto. eauto. eauto.
                lia. lia. auto. inv H9.
              * destruct (Z_le_dec); inv H8.
                generalize (S2 NO'). unfold Mem.loadbytes. destruct Mem.range_perm_dec; destruct Mem.can_access_block_dec; intros E2; inv E2.
                rewrite Z.add_0_r.
                apply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v))).
                assert ((init_data_list_size (gvar_init v')) = (init_data_list_size (gvar_init v))) as EQ.
                { inv H3. simpl in *. eauto. }
                rewrite H9.
                inv H3; simpl in *; subst.
                rewrite H8.
                eapply bytes_of_init_inject'. eauto. eauto. eauto.
                lia. lia. lia. }
      + intros.
        destruct (init_meminj s Right W2 W3 b) as [[b' delta]|] eqn:INJ; auto.
        elim H1. exploit init_meminj_invert; eauto. intros (A & id & B & C).
        eapply Genv.find_symbol_not_fresh; eauto.
      + intros. exploit init_meminj_invert; eauto. intros (A & id & B & C).
        eapply Genv.find_symbol_not_fresh; eauto.
      + red; intros.
        exploit init_meminj_invert. eexact H2. intros (A1 & id1 & B1 & C1).
        exploit init_meminj_invert. eexact H3. intros (A2 & id2 & B2 & C2).
        destruct (ident_eq id1 id2). congruence. left; eapply Genv.global_addresses_distinct; eauto.
      + intros. exploit init_meminj_invert; eauto. intros (A & id & B & C). subst delta.
        split. lia. generalize (Ptrofs.unsigned_range_2 ofs). lia.
      + intros. exploit init_meminj_invert; eauto.
        intros [? [? [? ?]]]. subst.
        eapply Genv.find_symbol_find_def_inversion in H4 as G1.
        destruct G1 as [gd G1].
        eapply Genv.find_symbol_find_def_inversion in H5 as G2.
        destruct G2 as [gd' G2].
        exploit (Genv.init_mem_characterization_gen W2); eauto.
        exploit (Genv.init_mem_characterization_gen W3); eauto.
        assert (match_globdef gd gd') as G.
        { exploit defs_inject; eauto.
          eapply init_meminj_preserves_globals; eauto.
          intros [? [? [? [? ?]]]]. congruence. }
        inv G.
        * intros. exploit H6; eauto.
        * intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
          apply Q2 in H2. destruct H2. subst.
          left. apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
          inv H3; simpl in *; subst.
          apply P1. lia.
    - intros ?. unfold init_meminj. destruct (Genv.invert_symbol); try discriminate.
      destruct kept_genv; try discriminate. destruct Genv.find_symbol; try discriminate.
      congruence.
    - intros.
      eapply Mem.perm_valid_block in H1 as ?.
      exploit (Genv.find_def_init_mem W2); eauto.
      intros [g [? ?]].
      exploit (Genv.init_mem_characterization_gen W2); eauto.
      intros X.
      destruct g; try now exploit X; eauto.
      rewrite <- H4.
      eapply no_bottom2' in H3 as ?.
      eapply no_top2' in H3 as ?. simpl.
      destruct (comp_of v); eauto; try now contradiction.
    - intros.
      eapply Mem.perm_valid_block in H1 as ?.
      exploit (Genv.find_def_init_mem W3); eauto.
      intros [g [? ?]].
      exploit (Genv.init_mem_characterization_gen W3); eauto.
      intros X.
      destruct g; try now exploit X; eauto.
      rewrite <- H4.
      eapply no_bottom3' in H3 as ?.
      eapply no_top3' in H3 as ?. simpl.
      destruct (comp_of v); eauto; try now contradiction.
    - eapply Genv.init_mem_genv_next in H. simpl. rewrite H. now apply Ple_refl.
    - eapply Genv.init_mem_genv_next in H0. simpl. rewrite H0. now apply Ple_refl.
    - intros. eapply Genv.find_def_not_fresh; eauto.
    - intros. eapply Genv.find_def_not_fresh; eauto.
    - intros. exploit (Genv.init_mem_characterization_gen W2); eauto.
    - intros. exploit (Genv.init_mem_characterization_gen W3); eauto.
    - intros. exploit (Genv.init_mem_find_def W2); eauto.
    - intros. unfold init_meminj in *.
      destruct (Genv.invert_symbol ge2 b0) eqn:find_b0; try discriminate.
      destruct (Genv.invert_symbol ge2 b4) eqn:find_b4; try discriminate.
      destruct (kept_genv s ge2 Right i ) eqn:kept_b0; try discriminate.
      destruct (kept_genv s ge2 Right i0 ) eqn:kept_b4; try discriminate.
      destruct (Genv.find_symbol ge3 i) eqn:find_i; try discriminate.
      destruct (Genv.find_symbol ge3 i0) eqn:find_i0; try discriminate. inv H3. inv H2.
      intros ?. subst.
      apply Genv.find_invert_symbol in find_i, find_i0.
      assert (i = i0) by congruence. subst i0.
      apply Genv.invert_find_symbol in find_b0, find_b4.
      assert (b0 = b4) by congruence. contradiction.
  Qed.

  Let single_L1 := sd_traces (semantics_determinate W1).
  Let single_L2 := sd_traces (semantics_determinate W2).
  Let single_L3 := sd_traces (semantics_determinate W3).

  Lemma rewr_cp_main: forall (ge: Genv.t fundef unit) id, Genv.find_comp_in_genv ge (Genv.symbol_address ge id Ptrofs.zero) =
                                                       Genv.find_comp_of_ident ge id.
  Proof.
    unfold Genv.find_comp_of_ident, Genv.symbol_address.
    intros. destruct Genv.find_symbol; auto.
  Qed.

  Hypothesis comp_main: comp_of_main W3 = cp_main.

  Lemma simulation:
    @threeway_simulation (semantics W1) (semantics W2) (semantics W3)
      single_L1 single_L2 single_L3.
  Proof.
    apply threeway_simulation_diagram
      with (metadata := (meminj * meminj)%type)
           (common_equivalence := fun '(j__left, j__right) s1 s2 s3 =>
                                    stack_rel s cp_main ge1 ge2 ge3 Left j__left j__right
                                      (mem_of_state s1) (mem_of_state s2) (mem_of_state s3)
                                      (stack_of_state s1) (stack_of_state s2) (stack_of_state s3))
           (strong_equivalence1 := fun '(j__left, j__right) s1 s3 =>
                                     meminj_preserves_globals s Left W1 W3 j__left /\
                                       strong_equivalence s cp_main ge1 ge3 j__left Left s1 s3)
           (strong_equivalence2 := fun '(j__left, j__right) s2 s3 =>
                                     meminj_preserves_globals s Right W2 W3 j__right /\
                                       strong_equivalence s cp_main ge2 ge3 j__right Right s2 s3)
           (weak_equivalence1   := fun '(j__left, j__right) s1 s3 =>
                                     meminj_preserves_globals s Left W1 W3 j__left /\
                                       weak_equivalence   s ge1 ge3 j__left Left s1 s3)
           (weak_equivalence2   := fun '(j__left, j__right) s2 s3 =>
                                     meminj_preserves_globals s Right W2 W3 j__right /\
                                       weak_equivalence   s ge2 ge3 j__right Right s2 s3).
    (* (order := fun _ _ => True). *)
    - simpl. intros id. transitivity (Genv.public_symbol ge3 id).
      clear -match_W2_W3. exploit init_meminj_preserves_globals; eauto.
      intros ?.
      unfold Genv.public_symbol, ge2, ge3.
      rewrite 2!(Genv.genv_public_add_globals). fold ge2. fold ge3. simpl.
      erewrite <- match_prog_public; eauto.
      destruct (Genv.find_symbol ge2 id) eqn:?.
      exploit transform_find_symbol_1; eauto. intros [? ->]; auto.
      destruct (Genv.find_symbol ge3 id) eqn:?.
      exploit transform_find_symbol_2; eauto. intros [? ?]; auto. congruence.
      auto.
      clear -match_W1_W3. exploit init_meminj_preserves_globals; eauto.
      intros ?.
      unfold Genv.public_symbol, ge1, ge3.
      rewrite 2!(Genv.genv_public_add_globals). fold ge1. fold ge3. simpl.
      erewrite match_prog_public; eauto.
      destruct (Genv.find_symbol ge1 id) eqn:?.
      exploit transform_find_symbol_1; eauto. intros [? ->]; auto.
      destruct (Genv.find_symbol ge3 id) eqn:?.
      exploit transform_find_symbol_2; eauto. intros [? ?]; auto. congruence.
      auto.
    - simpl. intros id.
      clear -match_W2_W3. exploit init_meminj_preserves_globals; eauto.
      intros ?.
      unfold Genv.public_symbol, ge2, ge3.
      rewrite 2!(Genv.genv_public_add_globals). fold ge2. fold ge3. simpl.
      erewrite match_prog_public; eauto.
      destruct (Genv.find_symbol ge2 id) eqn:?.
      exploit transform_find_symbol_1; eauto. intros [? ->]; auto.
      destruct (Genv.find_symbol ge3 id) eqn:?.
      exploit transform_find_symbol_2; eauto. intros [? ?]; auto. congruence.
      auto.
    - intros s1 ini1 s2 ini2.
      assert (exists m, Genv.init_mem W3 = Some m) as [m3 ?].
      { apply Genv.init_mem_exists.
        intros id v H0.
        assert (P: (prog_defmap W3)!id = Some (Gvar v)).
        { eapply prog_defmap_norepet; eauto. eapply match_prog_unique; eauto. }
        destruct (s (comp_of v)) eqn:side_cp.
        - inv ini1.
          rewrite (match_prog_def _ _ _ _ match_W1_W3) in P; auto.
          exploit Genv.init_mem_inversion; eauto. apply in_prog_defmap; eauto. intros [AL FV].
          split; auto. intros. exploit FV; eauto. intros (b & FS).
          eapply (transform_find_symbol_1 _ _ _ _ match_W1_W3); eauto.
          unfold kept_prog. unfold kept_genv. eapply found_in_W3_kept1; eauto.
        - inv ini2.
          rewrite (match_prog_def _ _ _ _ match_W2_W3) in P; auto.
          exploit Genv.init_mem_inversion; eauto. apply in_prog_defmap; eauto. intros [AL FV].
          split; auto. intros. exploit FV; eauto. intros (b & FS).
          eapply (transform_find_symbol_1 _ _ _ _ match_W2_W3); eauto.
          eapply found_in_W3_kept2; eauto.
      }
      eexists; eexists (init_meminj s Left W1 W3, init_meminj s Right W2 W3). split.
      + econstructor; eauto.
      + inv ini1; inv ini2. subst ge. subst ge0.
        set (cp := Genv.find_comp_in_genv ge1 (Genv.symbol_address ge1 (prog_main W1) Ptrofs.zero)) in *.
        destruct (s cp) eqn:ini_side.
        -- eapply match_states_left; simpl; eauto.
           ++ econstructor; eauto.
           ++ split; eauto using init_meminj_preserves_globals.
              rewrite <- !rewr_cp_main, same_cp_main2.
              econstructor; eauto.
              ** constructor. subst rs0. Simpl. eauto.
              ** constructor. Simpl. eauto.
              ** simpl. unfold cp_main. rewrite <- rewr_cp_main. auto.
              ** { subst rs0. intros x.
                   setoid_rewrite Pregmap.gsspec.
                   destruct (Pregmap.elt_eq).
                   { unfold Vnullptr. destruct Archi.ptr64; now constructor. }
                   setoid_rewrite Pregmap.gsspec.
                   destruct (Pregmap.elt_eq).
                   { unfold Vnullptr. destruct Archi.ptr64; now constructor. }
                   setoid_rewrite Pregmap.gsspec.
                   destruct (Pregmap.elt_eq).
                   { unfold Genv.symbol_address.
                     destruct (Genv.find_symbol ge1 (prog_main W1)) eqn:?; try now constructor.
                     exploit (symbols_inject2 s Left W1 W3 (init_meminj s Left W1 W3)); eauto.
                     now eapply init_meminj_preserves_globals.
                     clear -Heqo ini_side main_not_bottom.
                     unfold kept_genv. rewrite Heqo.
                     fold (Genv.find_def ge1 b). unfold cp in *.
                     unfold Genv.symbol_address in *.
                     rewrite Heqo in *. simpl in *. unfold Genv.find_comp_of_block in *.
                     destruct Genv.find_def; try contradiction. destruct g; auto. simpl in *.
                     rewrite ini_side. auto.
                     erewrite (match_prog_main _ _ _ _ match_W1_W3); eauto.
                     intros [? [-> ?]]. econstructor; eauto. }
                   setoid_rewrite Pregmap.gi. now constructor. auto. }
              ** eapply init_mem_correct1; eauto.
           ++ split; eauto using init_meminj_preserves_globals.
              econstructor; eauto.
              ** constructor. subst rs1. Simpl. eauto.
              ** constructor. Simpl. eauto.
              ** rewrite <- !rewr_cp_main, same_cp_main1. auto.
              ** rewrite <- !rewr_cp_main, same_cp_main1. auto.
              ** rewrite <- !rewr_cp_main, same_cp_main2. auto.
              ** rewrite <- !rewr_cp_main, same_cp_main2. auto.
              ** eapply init_mem_correct2; eauto.
        -- eapply match_states_right; simpl; eauto.
           ++ econstructor; eauto.
           ++ split; eauto using init_meminj_preserves_globals.
              rewrite <- !rewr_cp_main, same_cp_main2.
              econstructor; eauto.
              ** constructor. subst rs1. Simpl. eauto. eauto.
              ** constructor. Simpl. eauto.
              ** eapply init_mem_correct1; eauto.
           ++ split; eauto using init_meminj_preserves_globals.
              rewrite <- !rewr_cp_main, same_cp_main1, same_cp_main2.
              econstructor; eauto.
              ** constructor. subst rs1. Simpl. eauto.
              ** constructor. Simpl. eauto.
              ** simpl. unfold cp_main. rewrite <- rewr_cp_main. auto.
              ** { subst rs1. intros x.
                   setoid_rewrite Pregmap.gsspec.
                   destruct (Pregmap.elt_eq).
                   { unfold Vnullptr. destruct Archi.ptr64; now constructor. }
                   setoid_rewrite Pregmap.gsspec.
                   destruct (Pregmap.elt_eq).
                   { unfold Vnullptr. destruct Archi.ptr64; now constructor. }
                   setoid_rewrite Pregmap.gsspec.
                   destruct (Pregmap.elt_eq).
                   { unfold Genv.symbol_address.
                     destruct (Genv.find_symbol ge2 (prog_main W2)) eqn:?; try now constructor.
                     exploit (symbols_inject2 s Right W2 W3 (init_meminj s Right W2 W3)); eauto.
                     now eapply init_meminj_preserves_globals.
                     clear -Heqo ini_side main_not_bottom same_cp_main1. subst cp.
                     unfold kept_genv. rewrite Heqo.
                     fold (Genv.find_def ge2 b).
                     unfold Genv.symbol_address in *.
                     rewrite Heqo in *. simpl in *. unfold Genv.find_comp_of_block in *.
                     destruct Genv.find_def; try contradiction. destruct g; auto. simpl in *.
                     rewrite same_cp_main1. rewrite ini_side. auto.
                     congruence.
                     erewrite (match_prog_main _ _ _ _ match_W2_W3); eauto.
                     intros [? [-> ?]]. econstructor; eauto. }
                   setoid_rewrite Pregmap.gi. now constructor. auto. }
              ** eapply init_mem_correct2; eauto.
    - intros s1 s1' H s2 s3 (j__left & j__right) (? & ?) (? & ?) ?.
      exploit (step_E0_strong s W1 W2 W3 Left); eauto.
      intros id.
      clear -match_W1_W3. exploit init_meminj_preserves_globals; eauto. simpl.
      intros ?.
      unfold Genv.public_symbol, ge1, ge3. simpl.
      rewrite 2!(Genv.genv_public_add_globals). fold ge1. fold ge3. simpl.
      erewrite match_prog_public; eauto.
      destruct (Genv.find_symbol ge1 id) eqn:?.
      exploit transform_find_symbol_1; eauto. intros [? ->]; auto.
      destruct (Genv.find_symbol ge3 id) eqn:?.
      exploit transform_find_symbol_2; eauto. intros [? ?]; auto. congruence.
      auto.
      simpl. intros. eapply Genv.find_symbol_find_def_inversion; eauto.
      unfold cp_main. clear -same_cp_main2.
      unfold Genv.find_comp_of_ident, Genv.symbol_address in *.
      destruct (Genv.find_symbol ge3 (prog_main W3)); destruct (Genv.find_symbol ge1 (prog_main W1)); try now auto.
      intros (s3' & j__left' & ? & ? & ? & ? & ? & ?).
      exists s3'; exists (j__left', j__right); split; [assumption |].
      split; [| split]; [| | assumption]; split; eauto.
      intros (s3' & j__left' & ? & ? & ? & ? & ? & ?).
      exists s3'; exists (j__left', j__right); split; [assumption |].
      split; [| split]; [| | assumption]; split; eauto.
      intros (s3' & j__left' & ? & ? & ? & ? & ? & ?).
      exists s3'; exists (j__left', j__right); split; [assumption |].
      split; [| split]; [| | assumption]; split; eauto.
      intros (s3' & j__left' & ? & ? & ? & ? & ? & ?).
      exists s3'; exists (j__left', j__right); split; [assumption |].
      split; [| split]; [| | assumption]; split; eauto.
    - intros s1 s1' H s2 s3 (j__left & j__right) (? & ?) (? & ?) ?.
      exploit (step_E0_strong s W2 W1 W3 (opposite Left)); eauto using stack_rel_comm. simpl.
      intros id.
      clear -match_W2_W3. exploit init_meminj_preserves_globals; eauto. simpl.
      intros ?.
      unfold Genv.public_symbol, ge2, ge3. simpl.
      rewrite 2!(Genv.genv_public_add_globals). fold ge2. fold ge3. simpl.
      erewrite match_prog_public; eauto.
      destruct (Genv.find_symbol ge2 id) eqn:?.
      exploit transform_find_symbol_1; eauto. intros [? ->]; auto.
      destruct (Genv.find_symbol ge3 id) eqn:?.
      exploit transform_find_symbol_2; eauto. intros [? ?]; auto. congruence.
      auto.
      simpl. intros. eapply Genv.find_symbol_find_def_inversion; eauto.
      unfold comp_of_main. eapply stack_rel_comm; eauto.
      rewrite <- rewr_cp_main, same_cp_main1, rewr_cp_main. auto.
      unfold comp_of_main. rewrite <- rewr_cp_main, same_cp_main1, rewr_cp_main. auto.

      intros (s3' & j__right' & ? & ? & ? & S & ? & ?).
      exists s3'; exists (j__left, j__right'); split; [assumption |].
      split; [| split]; [| | ].
      + split; eauto.
        unfold comp_of_main. rewrite <- rewr_cp_main, <- same_cp_main1, rewr_cp_main. auto.
      + split; eauto.
      + eapply stack_rel_comm in S; eauto.
        unfold comp_of_main. rewrite <- rewr_cp_main, <- same_cp_main1, rewr_cp_main. auto.
    - intros s1 s1' H s2 s3 (j__left & j__right) (? & ?) (? & ?) ?.
      exploit (step_E0_weak s W2 W1 W3 (opposite Left)); eauto using stack_rel_comm.
      unfold comp_of_main. eapply stack_rel_comm; eauto.
      rewrite <- rewr_cp_main, same_cp_main1, rewr_cp_main. auto.
      unfold comp_of_main. eauto.
      unfold comp_of_main. rewrite <- rewr_cp_main, same_cp_main1, rewr_cp_main. auto.
      intros (j__left' & ? & S & ? & ?).
      exists (j__left', j__right).
      split; [| split; apply stack_rel_comm in S; simpl in S]; eauto.
      unfold comp_of_main. rewrite <- rewr_cp_main, <- same_cp_main1, rewr_cp_main. auto.
    - intros s1 s1' H s2 s3 (j__left & j__right) (? & ?) (? & ?) ?.
      exploit (step_E0_weak s W1 W2 W3 Left); eauto.
      intros (j__right' & ? & S & ? & ?).
      exists (j__left, j__right').
      split; [| split]; eauto.
    - intros s1 e s1' H s2 s2' H0 s3 (j__left & j__right) H1.
      destruct H1 as [[? ?] ? ? ? ? [? ?] [? ?]
                     | [? ?] ? ? ? ? [? ?] [? ?]].
      + exploit (step_t s W1 W2 W3 Left); eauto.
        simpl.
        intros id.
        clear -match_W1_W3. exploit init_meminj_preserves_globals; eauto. simpl.
        intros ?.
        unfold Genv.public_symbol, ge1, ge3. simpl.
        rewrite 2!(Genv.genv_public_add_globals). fold ge1. fold ge3. simpl.
        erewrite match_prog_public; eauto.
        destruct (Genv.find_symbol ge1 id) eqn:?.
        exploit transform_find_symbol_1; eauto. intros [? ->]; auto.
        destruct (Genv.find_symbol ge3 id) eqn:?.
        exploit transform_find_symbol_2; eauto. intros [? ?]; auto. congruence.
        auto.
        simpl. intros. eapply Genv.find_symbol_find_def_inversion; eauto.
        intros (s3' & j__left' & j__right' & ? & ? & ? & ? & X).
        exists s3'; exists (j__left', j__right'); split; eauto.
        destruct X as [[? ?] | [? ?]]; [left; eauto | right; eauto].
      + exploit (step_t s W2 W1 W3 (opposite Left)); eauto using stack_rel_comm.
        intros id.
        clear -match_W2_W3. exploit init_meminj_preserves_globals; eauto. simpl.
        intros ?.
        unfold Genv.public_symbol, ge2, ge3. simpl.
        rewrite 2!(Genv.genv_public_add_globals). fold ge2. fold ge3. simpl.
        erewrite match_prog_public; eauto.
        destruct (Genv.find_symbol ge2 id) eqn:?.
        exploit transform_find_symbol_1; eauto. intros [? ->]; auto.
        destruct (Genv.find_symbol ge3 id) eqn:?.
        exploit transform_find_symbol_2; eauto. intros [? ?]; auto. congruence.
        auto.
        simpl. intros. eapply Genv.find_symbol_find_def_inversion; eauto.
        unfold comp_of_main. eapply stack_rel_comm; eauto.
        rewrite <- rewr_cp_main, same_cp_main1, rewr_cp_main. auto.
        unfold comp_of_main. rewrite <- rewr_cp_main, same_cp_main1, rewr_cp_main. auto.
        intros (s3' & j__right' & j__left' & ? & ? & ? & S & X).
        eapply stack_rel_comm in S; simpl in S.
        exists s3'; exists (j__left', j__right'); split; eauto.
        destruct X as [[? ?] | [? ?]]; [right; eauto | left; eauto].
        unfold comp_of_main.
        rewrite <- rewr_cp_main, <- same_cp_main1, rewr_cp_main. auto.
        split; eauto.
        unfold comp_of_main. rewrite <- rewr_cp_main, <- same_cp_main1, rewr_cp_main. auto.
        unfold comp_of_main. rewrite <- rewr_cp_main, <- same_cp_main1, rewr_cp_main. auto.
        split; eauto.
        unfold comp_of_main. rewrite <- rewr_cp_main, <- same_cp_main1, rewr_cp_main. auto.
  Qed.

End Simulation.
