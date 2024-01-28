Require Import Coqlib Maps Errors Integers.
Require Import Integers Floats AST Linking.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.
Require Import Op Locations Mach Conventions Asm.
Require Import Complements.

Require Import Split.

(* #[local] Instance has_side_stackframe: has_side stackframe := *)
(*   { in_side s := fun '(Stackframe _ cp _ _ _) δ => s cp = δ  }. *)

(* #[local] Instance has_side_stack: has_side stack := *)
(*   { in_side s := fun st δ => List.Forall (fun f => s |= f ∈ δ) st }. *)

Print Instances has_side.

(* #[local] Instance has_side_regset: has_side regset := *)
(*   { in_side '(s, ge) := fun (rs: regset) δ => s (@Genv.find_comp_ignore_offset fundef unit _ ge (rs PC)) = δ }. *)


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

  (* Variant stackframe_rel (j: meminj): stackframe -> stackframe -> Prop := *)
  (*   | stackframe_related: forall b b' cp sg sp sp' ofs ofs', *)
  (*       Val.inject j (Vptr b ofs) (Vptr b' ofs') -> *)
  (*       Val.inject j sp sp' -> *)
  (*       stackframe_rel j (Stackframe b cp sg sp ofs) (Stackframe b' cp sg sp' ofs') *)
  (* . *)


  (* Inductive stack_rel (j__left j__right: meminj): stack -> stack -> stack -> Prop := *)
  (* | stack_rel_empty: *)
  (*   stack_rel j__left j__right nil nil nil *)
  (* | stack_rel_cons_left: forall st1 st2 st2' st3 f1 f3, *)
  (*     stack_rel j__left j__right st1 st2 st3 -> *)
  (*     s |= f1 ∈ Left -> *)
  (*     s |= st2' ∈ Left -> *)
  (*     s |= f3 ∈ Left -> *)
  (*     stackframe_rel j__left f1 f3 -> *)
  (*     stack_rel j__left j__right (f1 :: st1) (st2' ++ st2) (f3 :: st3) *)
  (* | stack_rel_cons_right: forall st1 st1' st2 st3 f2 f3, *)
  (*     stack_rel j__left j__right st1 st2 st3 -> *)
  (*     s |= st1' ∈ Right -> *)
  (*     s |= f2 ∈ Right -> *)
  (*     s |= f3 ∈ Right -> *)
  (*     stackframe_rel j__right f2 f3 -> *)
  (*     stack_rel j__left j__right (st1' ++ st1) (f2 :: st2) (f3 :: st3) *)
  (* . *)

  (* Variant stackframe_rel (j__left j__right: meminj): stackframe -> stackframe -> stackframe -> Prop := *)
  (*   | stackframe_related_left: forall cp sg b1 b2 b3 sp1 sp2 sp3 ofs1 ofs2 ofs3, *)
  (*       s cp = Left -> *)
  (*       Val.inject j__left (Vptr b1 ofs1) (Vptr b3 ofs3) -> *)
  (*       stackframe_rel j__left j__right *)
  (*         (Stackframe b1 cp sg sp1 ofs1) *)
  (*         (Stackframe b2 cp sg sp2 ofs2) *)
  (*         (Stackframe b3 cp sg sp3 ofs3) *)
  (*   | stackframe_related_right: forall cp sg b1 b2 b3 sp1 sp2 sp3 ofs1 ofs2 ofs3, *)
  (*       s cp = Right -> *)
  (*       Val.inject j__right (Vptr b2 ofs2) (Vptr b3 ofs3) -> *)
  (*       stackframe_rel j__left j__right *)
  (*         (Stackframe b1 cp sg sp1 ofs1) *)
  (*         (Stackframe b2 cp sg sp2 ofs2) *)
  (*         (Stackframe b3 cp sg sp3 ofs3) *)
  (* . *)

  Variant stackframe_rel (ge3: genv) (δ: side) (j__δ j__oppδ: meminj): stackframe -> stackframe -> stackframe -> Prop :=
    | stackframe_related_δ: forall cp sg b1 b2 b3 sp1 sp2 sp3 ofs1 ofs2 ofs3,
        Genv.find_comp_of_block ge3 b3 = Some cp ->
        s cp = δ ->
        Val.inject j__δ (Vptr b1 ofs1) (Vptr b3 ofs3) ->
        (* Val.inject j__oppδ (Vptr b2 ofs2) (Vptr b3 ofs3) -> *)
        Val.inject j__δ sp1 sp3 ->
        stackframe_rel ge3 δ j__δ j__oppδ
          (Stackframe b1 sg sp1 ofs1)
          (Stackframe b2 sg sp2 ofs2)
          (Stackframe b3 sg sp3 ofs3)
    | stackframe_related_opp_δ: forall cp sg b1 b2 b3 sp1 sp2 sp3 ofs1 ofs2 ofs3,
        Genv.find_comp_of_block ge3 b3 = Some cp ->
        s cp = opposite δ ->
        (* Val.inject j__δ (Vptr b1 ofs1) (Vptr b3 ofs3) -> *)
        Val.inject j__oppδ (Vptr b2 ofs2) (Vptr b3 ofs3) ->
        Val.inject j__oppδ sp2 sp3 ->
        stackframe_rel ge3 δ j__δ j__oppδ
          (Stackframe b1 sg sp1 ofs1)
          (Stackframe b2 sg sp2 ofs2)
          (Stackframe b3 sg sp3 ofs3)
  .

  Inductive stack_rel (ge3: genv) (δ: side) (j__δ j__oppδ: meminj): stack -> stack -> stack -> Prop :=
  | stack_rel_empty:
    stack_rel ge3 δ j__δ j__oppδ nil nil nil
  | stack_rel_cons: forall st1 st2 st3 f1 f2 f3,
      stack_rel ge3 δ j__δ j__oppδ st1 st2 st3 ->
      stackframe_rel ge3 δ j__δ j__oppδ f1 f2 f3 ->
      stack_rel ge3 δ j__δ j__oppδ (f1 :: st1) (f2 :: st2) (f3 :: st3)
  .

  (* Lemma stack_rel_same_callee (ge3: genv) (δ: side) (j__δ j__oppδ: meminj): *)
  (*   forall st1 st2 st3 cp, *)
  (*     stack_rel ge3 δ j__δ j__oppδ st1 st2 st3 -> *)
  (*     callee_comp cp st1 = callee_comp cp st3 /\ callee_comp cp st2 = callee_comp cp st3. *)
  (* Proof. *)
  (*   intros * H. *)
  (*   inv H. *)
  (*   - split; reflexivity. *)
  (*   - inv H1; split; reflexivity. *)
  (* Qed. *)

  Lemma stack_rel_comm (ge3: genv) (δ: side) (j__δ j__oppδ: meminj):
    forall st1 st2 st3,
      stack_rel ge3 δ j__δ j__oppδ st1 st2 st3 ->
      stack_rel ge3 (opposite δ) j__oppδ j__δ st2 st1 st3.
  Proof.
    intros st1 st2 st3 H.
    induction H.
    - constructor.
    - constructor; eauto.
      inv H0.
      + eapply stackframe_related_opp_δ; eauto.
        now destruct s.
      + eapply stackframe_related_δ; eauto.
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

  Inductive strong_equivalence (ge ge': genv) (j: meminj) (δ: side): state -> state -> Prop :=
  | strong_equivalence_State: forall st st' rs rs' m m' cp,
      Genv.find_comp ge (rs PC) = Some cp ->
      s cp = δ ->
      regset_rel j rs rs' ->
      mem_rel ge ge' j δ m m' ->
      strong_equivalence ge ge' j δ (State st rs m) (State st' rs' m')
  | strong_equivalence_ReturnState: forall st st' rs rs' m m' rec_cp,
      (* careful, the current comp in a returnstate is given by [rec_cp] *)
      s rec_cp = δ ->
      (* s (callee_comp cp_main st) = δ -> *)
      regset_rel j rs rs' ->
      mem_rel ge ge' j δ m m' ->
      strong_equivalence ge ge' j δ (ReturnState st rs m rec_cp) (ReturnState st' rs' m' rec_cp)
  .

  Inductive weak_equivalence (ge ge': genv) (j: meminj) (δ: side): state -> state -> Prop :=
  | weak_equivalence_State: forall st st' rs rs' m m' cp,
      Genv.find_comp ge (rs PC) = Some cp ->
      Genv.find_comp ge' (rs' PC) = Some cp ->
      s cp = opposite δ ->
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (State st rs m) (State st' rs' m')
  | weak_equivalence_ReturnState: forall st st' rs rs' m m' rec_cp,
      (* careful, the current comp in a returnstate is given by [callee_comp] *)
      s rec_cp = opposite δ ->
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (ReturnState st rs m rec_cp) (ReturnState st' rs' m' rec_cp)
  | weak_equivalence_State_ReturnState: forall st st' rs rs' m m' cp,
      Genv.find_comp ge (rs PC) = Some cp ->
      s cp = opposite δ ->
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (State st rs m) (ReturnState st' rs' m' cp)
  | weak_equivalence_ReturnState_State: forall st st' rs rs' m m' rec_cp,
      (* careful, the current comp in a returnstate is given by [callee_comp] *)
      s rec_cp = opposite δ ->
      Genv.find_comp ge' (rs' PC) = Some rec_cp ->
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (ReturnState st rs m rec_cp) (State st' rs' m')
  .

  Lemma weak_equivalence_inv1 (ge ge': genv) (j: meminj) (δ: side) (s1 s3: state) :
    weak_equivalence ge ge' j δ s1 s3 ->
    exists st1 rs1 m1,
      match s3 with
      | State st3 rs3 m3
      | ReturnState st3 rs3 m3 _ => mem_rel ge ge' j δ m1 m3
      end /\
        s1 = match s1 with
             | State _ _ _ => State st1 rs1 m1
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
             | State _ _ _ => State st1 rs1 m1
             | ReturnState _ _ _ cp => ReturnState st1 rs1 m1 cp
             end /\
        s3 = match s3 with
             | State _ _ _ => State st3 rs3 m3
             | ReturnState _ _ _ cp => ReturnState st3 rs3 m3 cp
             end.
  Proof.
    intros weak_s1_s3.
    inv weak_s1_s3; do 6 eexists; eauto.
  Qed.


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
    meminj_preserves_globals s δ W1 W3 j ->
    (* agrees_with j (init_meminj W1 W3) -> *)
    (* def_on_addressable s (Genv.globalenv W1) j δ -> *)
    mem_rel s (Genv.globalenv W1) (Genv.globalenv W3) j (opposite (s cp)) m1 m3 ->
    exists j',
    meminj_preserves_globals s δ W1 W3 j' /\
    (* agrees_with j' (init_meminj W1 W3) /\ *)
    (* def_on_addressable s (Genv.globalenv W1) j' δ /\ *)
      mem_rel s (Genv.globalenv W1) (Genv.globalenv W3) j' (opposite (s cp)) m1' m3 /\ inject_incr j j'.
Proof.
  intros s δ W1 norepet1 W3 j cp lo hi m1 m1' b1 m3 exec inj_pres m1_m3.
  exploit Mem.alloc_left_unmapped_inject; eauto using partial_mem_inject.
  intros (j' & m1'_m3 & incr & j'_b1 & same_inj).
  exists j'. split; [| split]; auto.
  { assert (G: forall s δ p1 p2 j j',
                 meminj_preserves_globals s δ p1 p2 j ->
                 (forall (b: block) gd, Genv.find_def (Genv.globalenv p1) b = Some gd -> j' b = j b) ->
                 (forall (b b': block) delta gd, Genv.find_def (Genv.globalenv p2) b' = Some gd ->
                                            j' b = Some (b', delta) ->
                                            j b = Some (b', delta)) ->
                 inject_incr j j' ->
                 meminj_preserves_globals s δ p1 p2 j').
      { clear.
        intros s δ p1 p2 j j' [A B C D E] rewr1 rewr2 incr.
        constructor.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto. intros ?; split; congruence.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. exploit C; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. erewrite rewr1 in H; eauto.
        - intros. eapply rewr2 in H; eauto. }
      eapply G; eauto.
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
  (* split; auto. *)
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
      intros [|[fd ?]]; try contradiction. eauto.
    + destruct m1_m3 as [C1 C2].
      simpl in C1, C2; simpl.
      split.
      * congruence.
      * destruct (Mem.block_compartment m1 b) eqn:?; try contradiction. intros ?.
        pose proof (ec_can_access_block (external_call_spec _) _ _ _ _ _ _ b (Some c) extcall) as G.
        simpl in G. rewrite Heqo in G. rewrite G in H; auto.
        intros ?.
        destruct H. destruct (Mem.block_compartment m1' b) eqn:?; try contradiction.
        pose proof (Mem.can_access_block_valid_block m1' b c).
        pose proof (proj2 (Mem.block_compartment_valid_block m1 b)).
        exploit (ec_new_valid (external_call_spec ef)); eauto. intros ?.
        assert (c = comp_of ef) by congruence. subst c. destruct δ; simpl in *; congruence.
        apply C2; eauto.
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
          simpl. intros ?.
          destruct G.
          - intros ?. destruct δ; simpl in *; congruence.
          - admit. }
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

  (* Hypothesis match_W1_W3: match_prog s δ W1 W3. *)
  (* Hypothesis match_W2_W3: match_prog s (opposite δ) W2 W3. *)

  (* Notation cp_main := (comp_of_main W1). *)

  Hypothesis norepet1: list_norepet (prog_defs_names W1).
  Hypothesis norepet2: list_norepet (prog_defs_names W2).
  Hypothesis norepet3: list_norepet (prog_defs_names W3).

  (* Context (ge1 ge2: genv). *)
  Notation ge1 := (Genv.globalenv W1).
  Notation ge2 := (Genv.globalenv W2).
  Notation ge3 := (Genv.globalenv W3).

  Lemma invert_symb_eq_block: forall j1 j2 b1 b2 b3 i1,
      meminj_preserves_globals s δ W1 W3 j1 ->
      meminj_preserves_globals s (opposite δ) W2 W3 j2 ->
      Genv.invert_symbol ge1 b2 = Some i1 ->
      Genv.invert_symbol ge2 b1 = Some i1 ->
      Genv.invert_symbol ge3 b3 = Some i1 ->
      b1 = b3 /\ b2 = b3.
  Proof. Admitted.

  Lemma alloc_preserves_rel1:
    forall cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3,
      s |= cp ∈ δ ->
      meminj_preserves_globals s δ W1 W3 j__δ ->
      (* agrees_with j__δ (init_meminj W1 W3) -> *)
      (* def_on_addressable s ge1 j__δ δ -> *)
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      meminj_preserves_globals s δ W1 W3 j__δ' /\
                      (* agrees_with j__δ' (init_meminj W1 W3) /\ *)
                      (* def_on_addressable s ge1 j__δ' δ /\ *)
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      regset_rel j__δ' rs1 rs3 /\
                      j__δ' b1 = Some (b3, 0) /\
                      inject_incr j__δ j__δ'.
  Proof.
    intros cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3 side_cp inj_pres m1_m3 m2_m3 rs1_rs3 alloc1.
    exploit (Mem.alloc_parallel_inject j__δ m1); eauto using partial_mem_inject, Z.le_refl.
    intros [j' [m3' [b3 [? [? [? [? diff]]]]]]].
    exists j', m3', b3.
    split; [| split; [| split; [| split; [| split; [| split]]]]];
      [assumption | (* eapply agrees_with_incr2; eauto | *) (* eapply def_on_addressable_incr; eauto *) | | | intros ?; eauto using val_inject_incr | assumption | assumption].
    { assert (G: forall s δ p1 p2 j j',
                 meminj_preserves_globals s δ p1 p2 j ->
                 (forall (b: block) gd, Genv.find_def (Genv.globalenv p1) b = Some gd -> j' b = j b) ->
                 (forall (b b': block) delta gd, Genv.find_def (Genv.globalenv p2) b' = Some gd ->
                                            j' b = Some (b', delta) ->
                                            j b = Some (b', delta)) ->
                 inject_incr j j' ->
                 meminj_preserves_globals s δ p1 p2 j').
      { clear.
        intros s δ p1 p2 j j' [A B C D E] rewr1 rewr2 incr.
        constructor.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto. intros ?; split; congruence.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. exploit C; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. erewrite rewr1 in H; eauto.
        - intros. eapply rewr2 in H; eauto. }
      eapply G; eauto.
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
      (* destruct (init_meminj W1 W3 b1) as [[] |] eqn:?; auto. *)
      (* exploit init_meminj_invert; eauto. intros [-> [id [? ?]]]. *)
      (* apply Mem.alloc_result in alloc1; subst. *)

      (* pose proof (ple_nextblock1 _ _ _ _ _ _ _ m1_m3). *)
      (* exploit (Senv.find_symbol_below ge1); eauto. intros ?. *)
      (* pose proof (Plt_Ple_trans _ _ _ H6 H5). *)
      (* now exploit Plt_strict; eauto. } *)
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
      meminj_preserves_globals s δ W1 W3 j__δ ->
      (* agrees_with j__δ (init_meminj W1 W3) -> *)
      (* def_on_addressable s ge1 j__δ δ -> *)
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      meminj_preserves_globals s δ W1 W3 j__δ' /\
                      (* agrees_with j__δ' (init_meminj W1 W3) /\ *)
                      (* def_on_addressable s ge1 j__δ' δ /\ *)
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      regset_rel j__δ' rs1 rs3 /\
                      inject_incr j__δ j__δ'.
  Proof.
    intros cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 rs1 rs3 side_cp inj_pres m1_m3 m2_m3 rs1_rs3 alloc1.
    exploit (Mem.alloc_parallel_inject j__δ m1); eauto using partial_mem_inject, Z.le_refl.
    intros [_ [m3' [b3 [alloc3 [_ [_ [_ _]]]]]]].
    exploit (Mem.alloc_left_unmapped_inject j__δ m1); eauto using partial_mem_inject.
    intros [j' [inj [incr [isnone diff]]]].
    exploit Mem.alloc_right_inject; eauto. intros inj'.
    exists j', m3', b3.  split; [| split; [| split; [| split; [| split]]]];
      [assumption | (* eapply agrees_with_incr1; eauto | eapply def_on_addressable_incr; eauto *) | | | intros ?; eauto using val_inject_incr | assumption].
    { assert (G: forall s δ p1 p2 j j',
                 meminj_preserves_globals s δ p1 p2 j ->
                 (forall (b: block) gd, Genv.find_def (Genv.globalenv p1) b = Some gd -> j' b = j b) ->
                 (forall (b b': block) delta gd, Genv.find_def (Genv.globalenv p2) b' = Some gd ->
                                            j' b = Some (b', delta) ->
                                            j b = Some (b', delta)) ->
                 inject_incr j j' ->
                 meminj_preserves_globals s δ p1 p2 j').
      { clear.
        intros s δ p1 p2 j j' [A B C D E] rewr1 rewr2 incr.
        constructor.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto. intros ?; split; congruence.
        - intros. exploit B; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. exploit C; eauto. intros (? & ? & ?).
          exploit incr; eauto.
        - intros. erewrite rewr1 in H; eauto.
        - intros. eapply rewr2 in H; eauto. }
      eapply G; eauto.
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
      meminj_preserves_globals s δ W1 W3 j__δ ->
      (* agrees_with j__δ (init_meminj W1 W3) -> *)
      (* def_on_addressable s ge1 j__δ δ -> *)
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__δ' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                      meminj_preserves_globals s δ W1 W3 j__δ' /\
                      (* agrees_with j__δ' (init_meminj W1 W3) /\ *)
                      (* def_on_addressable s ge1 j__δ' δ /\ *)
                      mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
                      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
                      regset_rel j__δ' rs1 rs3 /\
                      (s |= cp ∈ δ -> j__δ' b1 = Some (b3, 0)) /\
                      inject_incr j__δ j__δ'.
  Proof.
    intros.
    destruct (side_eq (s cp) δ) as [s_cp | s_cp].
    - exploit alloc_preserves_rel1; eauto. now simpl.
      intros [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto).
    - exploit alloc_preserves_rel2; eauto. now simpl; destruct (s cp); destruct δ.
      intros [? [? [? [? [? [? [? [? ?]]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto). simpl; congruence.
  Qed.


  Lemma free_preserves_rel:
    forall cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 b3,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
      j__δ b1 = Some (b3, 0) -> (* we are necessarily in the δ case *)
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      Mem.free m1 b1 lo hi cp = Some m1' ->
      exists m3', Mem.free m3 b3 lo hi cp = Some m3' /\
               mem_rel s ge1 ge3 j__δ δ m1' m3' /\
               mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3'.
  Proof.
    intros cp j__δ j__oppδ m1 m1' m2 m3 lo hi b1 b3 pres_globs1 pres_globs2 ptr_inj m1_m3 m2_m3 free1.
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
        assert (m1_m3' := m1_m3).
        apply partial_mem_inject in m1_m3.
        apply Mem.mi_inj in m1_m3.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m1 b1)) in m1_m3; eauto;
          [| now destruct (Mem.block_compartment m1 b1) eqn:?]; eauto.
        unfold Mem.can_access_block in *.
        (* destruct X as [X | X]; destruct Y as [Y | Y]. *)
        { destruct X as [? | [? X]], Y as [? | [? Y]], δ; simpl in *; try congruence.
          - destruct (Mem.block_compartment m2 b0);
              destruct (Mem.block_compartment m1 b1); try congruence.
          - destruct (Mem.block_compartment m2 b0);
              destruct (Mem.block_compartment m1 b1); try congruence.
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
      - erewrite Mem.nextblock_free; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_free_1; eauto.
      - intros. intros n.
        eapply find_def_perm4; eauto.
        eapply Mem.perm_free_3; eauto. }
  Qed.

  Lemma store_preserves_rel:
    forall cp (j__δ j__oppδ: meminj) m1 m1' m2 m3 ch ofs v1 v3 b1 b3,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
      j__δ b1 = Some (b3, 0) -> (* we are necessarily in the δ case *)
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      Val.inject j__δ v1 v3 ->
      Mem.store ch m1 b1 ofs v1 cp = Some m1' ->
      exists m3', Mem.store ch m3 b3 ofs v3 cp = Some m3' /\
               mem_rel s ge1 ge3 j__δ δ m1' m3' /\
               mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3'.
  Proof.
    intros cp j__δ j__oppδ m1 m1' m2 m3 ch ofs v1 v3 b1 b3 pres_globs1 pres_globs2 ptr_inj m1_m3 m2_m3 val_inj store1.
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
        assert (m1_m3' := m1_m3).
        apply partial_mem_inject in m1_m3.
        apply Mem.mi_inj in m1_m3.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m1 b1)) in m1_m3; eauto;
          [| now destruct (Mem.block_compartment m1 b1) eqn:?]; eauto.
        unfold Mem.can_access_block in *.
        { destruct X as [? | [? X]], Y as [? | [? Y]], δ; simpl in *; try congruence.
          - destruct (Mem.block_compartment m2 b');
              destruct (Mem.block_compartment m1 b1); try congruence.
          - destruct (Mem.block_compartment m2 b');
              destruct (Mem.block_compartment m1 b1); try congruence.
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
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. exploit find_def_valid2; eauto. eapply Mem.store_valid_block_1; eauto.
      - intros; intros n. exploit find_def_perm2; eauto.
        eapply Mem.perm_store_2; eauto. }
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

  Lemma inject_incr_stack_rel1:
    forall j1 j1' j2 st1 st2 st3,
      inject_incr j1 j1' ->
      stack_rel s ge3 δ j1 j2 st1 st2 st3 ->
      stack_rel s ge3 δ j1' j2 st1 st2 st3.
  Proof.
    intros * incr st_rel.
    induction st_rel.
    - constructor; eauto.
    - constructor; eauto.
      inv H.
      + econstructor; eauto.
      + eapply stackframe_related_opp_δ; eauto.
  Qed.

  Lemma inject_incr_stack_rel2:
    forall j1 j2 j2' st1 st2 st3,
      inject_incr j2 j2' ->
      stack_rel s ge3 δ j1 j2 st1 st2 st3 ->
      stack_rel s ge3 δ j1 j2' st1 st2 st3.
  Proof.
    intros * incr st_rel.
    induction st_rel.
    - constructor; eauto.
    - constructor; eauto.
      inv H.
      + econstructor; eauto.
      + eapply stackframe_related_opp_δ; eauto.
  Qed.

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
    (* exploit init_meminj_preserves_globals; eauto. *)
    (* intros inj_pres. *)
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

  (* Definition agrees_with (j1 j2: meminj) := *)
  (*   forall b b' delta', *)
  (*     j2 b = Some (b', delta') -> *)
  (*     j1 b = Some (b', delta'). *)

  (* Lemma agrees_with_inject: forall j j' v v', *)
  (*     agrees_with j j' -> *)
  (*     Val.inject j' v v' -> *)
  (*     Val.inject j v v'. *)
  (* Proof. *)
  (*   intros j j' v v' H inj. unfold agrees_with in H. *)
  (*   inv inj; try now constructor. *)
  (*   eapply H in H0. econstructor; eauto. *)
  (* Qed. *)

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
    intros j__δ b b' gd inj_pres inj_b_b' find_b_gd.
    exploit defs_inject; eauto. intros [gd' [find_def_b' [_ [match_fd_gd' left_implies_eq]]]].
    eauto.
  Qed.

  (* Lemma agrees_with_init_meminj_find_def_preserved: *)
  (*   forall j b b' delta gd, *)
  (*     match_prog s δ W1 W3 -> *)
  (*     agrees_with j (init_meminj W1 W3) -> *)
  (*     j b = Some (b', delta) -> *)
  (*     Genv.find_def ge1 b = Some gd -> *)
  (*     exists gd', *)
  (*       Genv.find_def ge3 b' = Some gd' /\ *)
  (*         match_globdef gd gd' /\ *)
  (*         (forall id : ident, Genv.find_symbol ge1 id = Some b -> kept_genv s ge1 δ id = true -> gd' = gd). *)
  (*   Proof. *)
  (*     intros j b b' delta gd match_W1_W3 agr j_b find_b. *)
  (*     exploit init_meminj_preserves_globals; eauto. intros inj_pres. *)
  (*     eapply find_def_preserved; eauto. *)
  (*     assert (exists b', init_meminj W1 W3 b = Some (b', 0)) as [b'' init_meminj_b]. *)
  (*     { unfold init_meminj. *)
  (*       exploit Genv.find_def_find_symbol_inversion; eauto. *)
  (*       intros (id & A). apply Genv.find_invert_symbol in A as B. rewrite B. *)
  (*       destruct (kept_prog s W1 δ id) eqn:?. *)
  (*       - exploit match_prog_def; eauto. *)
  (*         assert (C: (prog_defmap W1) ! id = Some gd). *)
  (*         { apply Genv.find_def_symbol; eauto. } *)
  (*         rewrite C. intros D. *)
  (*         apply Genv.find_def_symbol in D as [b'' [D E]]; eauto. *)
  (*         rewrite D. eauto. *)
  (*       - exploit match_prog_notdef; eauto. *)
  (*         assert (C: (prog_defmap W1) ! id = Some gd). *)
  (*         { apply Genv.find_def_symbol; eauto. } *)
  (*         rewrite C. intros D. *)
  (*         inversion D as [| ? ? matchgd u E]; subst. symmetry in E. *)
  (*         apply Genv.find_def_symbol in E as [b'' [E F]]; eauto. *)
  (*         rewrite E. eauto. } *)
  (*     exploit agr; eauto. now intros []; congruence. *)
  (*   Qed. *)

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


  (* Lemma agrees_with_init_meminj_find_comp_of_block_preserved: *)
  (*   forall j b b' delta cp, *)
  (*     match_prog s δ W1 W3 -> *)
  (*     agrees_with j (init_meminj W1 W3) -> *)
  (*     j b = Some (b', delta) -> *)
  (*     Genv.find_comp_of_block ge1 b = Some cp -> *)
  (*     Genv.find_comp_of_block ge3 b' = Some cp. *)
  (* Proof. *)
  (*   intros j b b' delta cp match_W1_W3 agr j_b comp_b. *)
  (*   unfold Genv.find_comp_of_block in *. *)
  (*   destruct (Genv.find_def _ b) as [gd |] eqn:?. *)
  (*   - exploit agrees_with_init_meminj_find_def_preserved; eauto. *)
  (*     intros (gd' & -> & H & ?). *)
  (*     destruct H as [? ? H | ? ? H]; now inv H. *)
  (*   - congruence. *)
  (* Qed. *)

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

  (* Lemma agrees_with_init_meminj_find_comp_preserved: *)
  (*   forall j v v' cp, *)
  (*     match_prog s δ W1 W3 -> *)
  (*     agrees_with j (init_meminj W1 W3) -> *)
  (*     v <> Vundef -> *)
  (*     Val.inject j v v' -> *)
  (*     Genv.find_comp ge1 v = Some cp -> *)
  (*     Genv.find_comp ge3 v' = Some cp. *)
  (* Proof. *)
  (*   intros j v v' cp match_W1_W3 agr j_v v_not_undef comp_v. *)
  (*   inv v_not_undef; simpl; auto; try congruence. *)
  (*   eapply agrees_with_init_meminj_find_comp_of_block_preserved; eauto. *)
  (* Qed. *)

End Lemmas.

Ltac eexists_and_split :=
  fun k =>
    match goal with
    | m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
        rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
        exists j; eexists; eexists; split; [| split; [| split; [| split; [| split]]]]; eauto;
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
          (* rewrite same_low_half1 in * *)


          | H: Mem.alloc ?m1 ?cp ?lo1 ?hi1 = (?m1', ?b1),
              m1_m3: mem_rel _ _ _ ?j__δ ?δ ?m1 ?m3,
                m2_m3: mem_rel _ _ _ ?j__oppδ (opposite ?δ) ?m2 ?m3,
                  (* agr: agrees_with ?j__δ (init_meminj _ _), *)
                  (* addr: def_on_addressable _ _ ?j__δ ?δ, *)
                  inj_pres : meminj_preserves_globals _ ?δ _ _ ?j__δ,
                  rs1_rs3: regset_rel _ _ _ |- _ =>
              idtac "alloc case";
              let j__δ' := fresh "j__δ" in
              let m3' := fresh "m3" in
              let b3 := fresh "b3" in
              let alloc3 := fresh "alloc3" in
              (* let agr' := fresh "agr" in *)
              (* let addr' := fresh "addr" in *)
              let inj_pres' := fresh "inj_pres" in
              let m1'_m3' := fresh "m1'_m3'" in
              let m2_m3' := fresh "m2_m3'" in
              let proj := fresh "proj" in
              let incr := fresh "incr" in
              eapply (alloc_preserves_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inj_pres m1_m3 m2_m3 rs1_rs3) in H as
                  [j__δ' [m3' [b3 [alloc3 [inj_pres' [m1'_m3' [m2_m3' [? [proj incr]]]]]]]]];
              idtac "done with alloc";
              clear m1_m3 rs1_rs3 m2_m3 inj_pres
          | H: ?s ?cp = ?δ -> _,
              side_cp: ?s ?cp = ?δ |- _ =>
              specialize (H side_cp)
          | H: ?x = ?x -> _ |- _ =>
              specialize (H eq_refl)

          | H: Mem.store ?ch ?m1 ?b1 ?ofs (?rs1 ?r) ?cp = Some ?m1',
              m1_m3: mem_rel _ _ _ ?j__δ ?δ ?m1 ?m3,
                m2_m3: mem_rel _ _ _ ?j__oppδ (opposite ?δ) ?m2 ?m3,
                  ptr_inj: ?j__δ ?b1 = Some (?b3, 0),
                  (* inj_pres : meminj_preserves_globals _ ?δ _ _ ?j__δ, *)
                  inj_pres1 : meminj_preserves_globals _ ?δ _ _ ?j__δ,
                  inj_pres2 : meminj_preserves_globals _ (opposite ?δ) _ _ ?j__oppδ,
                    rs1_rs3: regset_rel ?j__δ ?rs1 ?rs3 |- _ =>
              idtac "store case";
              let m3' := fresh "m3" in
              eapply (store_preserves_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        inj_pres1 inj_pres2 ptr_inj m1_m3 m2_m3 (rs1_rs3 r)) in H as
                  [m3' [? [? ?]]];
              idtac "done with store";
              clear m1_m3 m2_m3

          | H: Mem.free ?m1 ?b1 ?lo ?hi ?cp = Some ?m1',
              m1_m3: mem_rel _ _ _ ?j__δ ?δ ?m1 ?m3,
                m2_m3: mem_rel _ _ _ ?j__oppδ (opposite ?δ) ?m2 ?m3,
                  inj_pres1 : meminj_preserves_globals _ ?δ _ _ ?j__δ,
                  inj_pres2 : meminj_preserves_globals _ (opposite ?δ) _ _ ?j__oppδ,
                  ptr_inj: ?j__δ ?b1 = Some (?b3, 0) |- _ =>
              (* rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ => *)
              idtac "free case";
              let m3' := fresh "m3" in
              eapply (free_preserves_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        inj_pres1 inj_pres2 ptr_inj m1_m3 m2_m3) in H as
                  [m3' [? [? ?]]];
              idtac "done with free";
              clear m1_m3

          | H: Mem.load ?ch ?m1 ?b1 ?ofs ?cp = Some ?v1,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                ptr_inj: ?j ?b1 = Some (?b3, 0) |- _ =>
              idtac "load case";
              let v3 := fresh "v3" in
              let load3 := fresh "load3" in
              destruct (Mem.load_inject _ _ _ _ _ _ _ _ _ _ (partial_mem_inject _ _ _ _ _ _ _ m1_m3) H ptr_inj) as
                [v3 [load3 ?]];
              rewrite Z.add_0_r in load3;
              idtac "done with load";
              clear H

          | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              (* idtac "Val.cmpu_bool case 0"; *)
              eapply cmpu_bool_preserved with (m3 := m3) in H; eauto using rs1_rs3;
              try rewrite H in *;
              (* idtac "done with Val.cmpu_bool 0"; *)
              try congruence

          | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (Vint ?x) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              (* idtac "Val.cmpu_bool case 1"; *)
              eapply cmpu_bool_preserved with (m3 := m3) (v1' := Vint x) in H; eauto using rs1_rs3;
              try rewrite H in *;
              (* idtac "done with Val.cmpu_bool 1"; *)
              try congruence

          | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (Vint ?x) = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              (* idtac "Val.cmpu_bool case 2"; *)
              eapply cmpu_bool_preserved with (m3 := m3) (v2' := Vint x) in H; eauto using rs1_rs3;
              try rewrite H in *;
              (* idtac "done with Val.cmpu_bool 2"; *)
              try congruence

          | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (Vint ?x) (Vint ?y) = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              (* idtac "Val.cmpu_bool case 3"; *)
              eapply cmpu_bool_preserved with (m3 := m3) (v1' := Vint x) (v2' := Vint y) in H; eauto using rs1_rs3;
              try rewrite H in *;
              (* idtac "done with Val.cmpu_bool 3"; *)
              try congruence

          | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              (* idtac "Val.cmplu_bool case 0"; *)
              eapply cmplu_bool_preserved with (m3 := m3) in H; eauto using rs1_rs3;
              try rewrite H in *;
              (* idtac "done with Val.cmplu_bool 0"; *)
              try congruence

          | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (Vlong ?x) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              (* idtac "Val.cmplu_bool case 1"; *)
              eapply cmplu_bool_preserved with (m3 := m3) (v1' := Vlong x) in H; eauto using rs1_rs3;
              try rewrite H in *;
              (* idtac "done with Val.cmplu_bool 1"; *)
              try congruence

          | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (Vlong ?x) = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              (* idtac "Val.cmplu_bool case 2"; *)
              eapply cmplu_bool_preserved with (m3 := m3) (v2' := Vlong x) in H; eauto using rs1_rs3;
              try rewrite H in *;
              (* idtac "done with Val.cmplu_bool 2"; *)
              try congruence

          | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (Vlong ?x) (Vlong ?y) = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              (* idtac "Val.cmplu_bool case 3"; *)
              eapply cmplu_bool_preserved with (m3 := m3) (v1' := Vlong x) (v2' := Vlong y) in H; eauto using rs1_rs3;
              try rewrite H in *;
              (* idtac "done with Val.cmplu_bool 3"; *)
              try congruence

          | H: Val.cmp_bool ?op (?rs1 ?r) (?rs1 ?r') = Some ?b,
              m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
              (* idtac "Val.cmp_bool case"; *)
              eapply Val.cmp_bool_inject in H; eauto using rs1_rs3;
              try rewrite H in *;
              (* idtac "done with Val.cmp_bool"; *)
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
          (* | H: (let (_) := ?x in _) = Next _ _ |- _ => *)
          (*     let eq := fresh "eq" in *)
          (*     destruct x eqn:eq; simpl in *; try congruence *)
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

          | |- stack_rel _ _ _ _ _ _ _ _ => eauto using inject_incr_stack_rel1, inject_incr_stack_rel2, inject_incr_refl

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

  (* Hypothesis first_instr1: *)
  (*   forall b f i, *)
  (*     s (comp_of f) = δ -> *)
  (*     Genv.find_def ge1 b = Some (Gfun (Internal f)) -> *)
  (*     find_instr (Ptrofs.unsigned Ptrofs.zero) (fn_code f) = Some i -> *)
  (*     match i with *)
  (*     | Pallocframe _ _ => True *)
  (*     | _ => False *)
  (*     end. *)

  (* Hypothesis first_instr2: *)
  (*   forall b f i, *)
  (*     s (comp_of f) = opposite δ -> *)
  (*     Genv.find_def ge1 b = Some (Gfun (Internal f)) -> *)
  (*     find_instr (Ptrofs.unsigned Ptrofs.zero) (fn_code f) = Some i -> *)
  (*     match i with *)
  (*     | Pallocframe _ _ => True *)
  (*     | _ => False *)
  (*     end. *)

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

  Lemma update_stack_call_preserved_internal:
    forall j__δ sg rs1 rs3 st1 st1' st3 cp
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      (rs1 PC <> Vundef) ->
      Genv.find_comp ge1 (rs1 PC) = Some cp ->
      regset_rel j__δ rs1 rs3 ->
      update_stack_call ge1 st1 sg cp rs1 = Some st1' ->
      st1' = st1 /\
        update_stack_call ge3 st3 sg cp rs3 = Some st3.
  Proof.
    intros * inj_pres delta_zero nundef samecomp rs1_rs3.
    unfold update_stack_call.
    rewrite samecomp, Pos.eqb_refl.
    intros R; inv R.
    split; eauto.
    erewrite <- find_comp_preserved, samecomp, Pos.eqb_refl; eauto.
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

  (* Returns *)
  Lemma update_stack_return_preserved_internal:
    forall j__δ rs1 rs3 st1 st1' st3 cp
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      (rs1 PC <> Vundef) ->
      Genv.find_comp ge1 (rs1 PC) = Some cp ->
      regset_rel j__δ rs1 rs3 ->
      update_stack_return ge1 st1 cp rs1 = Some st1' ->
      st1' = st1 /\
        update_stack_return ge3 st3 cp rs3 = Some st3.
  Proof.
    intros * inj_pres delta_zero nundef samecomp rs1_rs3 (* st_rel *).
    unfold update_stack_return.
    rewrite samecomp, Pos.eqb_refl.
    intros R; inv R.
    split; eauto.
    erewrite <- find_comp_preserved, samecomp, Pos.eqb_refl; eauto.
  Qed.

  (* State inversion *)
  Lemma strong_equiv_state_internal_inv:
    forall j__δ st1 rs1 m1 s3 b ofs f i,
      meminj_preserves_globals s δ W1 W3 j__δ ->
      (* agrees_with j__δ (init_meminj W1 W3) -> *)
      strong_equivalence s ge1 ge3 j__δ δ (State st1 rs1 m1) s3 ->
      rs1 PC = Vptr b ofs ->
      Genv.find_def ge1 b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exists st3 rs3 m3 b' f',
        s3 = State st3 rs3 m3 /\
          rs3 PC = Vptr b' ofs /\
          Genv.find_def ge3 b' = Some (Gfun (Internal f')) /\
          (match_fundef (Internal f) (Internal f') /\
             (forall id : ident, Genv.find_symbol ge1 id = Some b -> kept_genv s ge1 δ id = true -> f = f')) /\
          mem_rel s ge1 ge3 j__δ δ m1 m3 /\
          regset_rel j__δ rs1 rs3 /\
          s (comp_of f) = δ.
  Proof.
    intros * inj_pres equiv eq_pc find_fun find_ins (* inj_b_b' *).
    assert (exists b', j__δ b = Some (b', 0)) as [b' inj_b_b'].
    { inv equiv.
      specialize (H5 PC). inv H5; try congruence.
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
    pose proof (H6 PC) as inj.
    rewrite eq_pc in *; simpl in *. inv inj.
    assert (b' = b2) by congruence; subst b2;
      assert (delta = 0) by congruence; subst delta.
    rewrite Ptrofs.add_zero. split; auto.
    rewrite find_fun'.
    repeat (split; auto).
    - intros; exploit left_implies_eq; eauto; congruence.
    - unfold Genv.find_comp_of_block in H3; rewrite find_fun in H3.
      now inv H3.
  Qed.

  Lemma strong_equiv_state_external_inv:
    forall j__δ st1 rs1 m1 s3 b ofs f,
      (* agrees_with j__δ (init_meminj W1 W3) -> *)
      meminj_preserves_globals s δ W1 W3 j__δ ->
      strong_equivalence s ge1 ge3 j__δ δ (State st1 rs1 m1) s3 ->
      rs1 PC = Vptr b ofs ->
      Genv.find_def ge1 b = Some (Gfun (External f)) ->
      exists st3 rs3 m3 b',
        s3 = State st3 rs3 m3 /\
          rs3 PC = Vptr b' ofs /\
          Genv.find_def ge3 b' = Some (Gfun (External f)) /\
          mem_rel s ge1 ge3 j__δ δ m1 m3 /\
          regset_rel j__δ rs1 rs3 /\
          s (comp_of f) = δ.
  Proof.
    intros * inj_pres equiv eq_pc find_fun (* inj_b_b' *).
    assert (exists b', j__δ b = Some (b', 0)) as [b' inj_b_b'].
    { inv equiv.
      specialize (H5 PC). inv H5; try congruence.
      exploit delta_zero; eauto; intros ->; rewrite Ptrofs.add_zero in *.
      exists b2. congruence. }
    exploit find_def_preserved; eauto.
    (* exploit (agrees_with_init_meminj_find_def_preserved s W1 W3); eauto. *)
    intros [fd' [find_fun' [match_f_f' left_implies_eq]]].
    inv equiv; inv match_f_f'. inv H0.
    eexists; eexists; eexists; eexists; split; eauto.
    pose proof (H5 PC) as inj.
    rewrite eq_pc in *; simpl in *. inv inj.
    assert (b' = b2) by congruence; subst b2;
      assert (delta = 0) by congruence; subst delta.
    rewrite Ptrofs.add_zero. split; auto.
    repeat (split; auto).
    unfold Genv.find_comp_of_block in H2. rewrite find_fun in H2. now inv H2.
  Qed.

  Lemma strong_equiv_returnstate_inv:
    forall j__δ st1 rs1 m1 s3 rec_cp,
      (* agrees_with j__δ (init_meminj W1 W3) -> *)
      (* meminj_preserves_globals s δ W1 W3 j__δ -> *)
      strong_equivalence s ge1 ge3 j__δ δ (ReturnState st1 rs1 m1 rec_cp) s3 ->
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
    forall (rs: regset) cp m j__δ rs' m' a v
      (eval: eval_builtin_arg ge1 rs cp (rs X2) m a v)
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      regset_rel j__δ rs rs' ->
      Mem.inject j__δ m m' ->
      exists v',
        eval_builtin_arg ge3 rs' cp (rs' X2) m' a v'
        /\ Val.inject j__δ v v'.
  Proof.
    induction 1; intros MINJ DZ (* SP  *)RS MI.
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
      { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
        destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; auto.
        exploit symbols_inject2; eauto. intros (b' & A & B). rewrite A.
        econstructor; eauto. rewrite Ptrofs.add_zero; auto. }
      exploit Mem.loadv_inject; eauto. intros (v' & A & B). exists v'; split; auto with barg.
      (* econstructor. simpl; eauto. *)
    - econstructor; split; eauto with barg. subst res.
      unfold Genv.symbol_address; simpl; unfold Genv.symbol_address.
      destruct (Genv.find_symbol ge1 id) as [b|] eqn:FS; auto.
      exploit symbols_inject2; eauto. intros (b' & A & B). rewrite A.
      destruct (Genv.find_comp_of_block ge1 b) eqn:FB; auto.
      erewrite <- (find_comp_of_block_preserved s W1 W3); eauto. rewrite FB.
      destruct (cp =? c)%positive; auto.
      econstructor; eauto. now rewrite Ptrofs.add_zero.
      destruct (Genv.find_def ge1 b) as [[] |] eqn:?; auto.
      exploit defs_inject; eauto.
      intros ([] & ? & _ & ? & ?). rewrite H.
      econstructor; eauto. now rewrite Ptrofs.add_zero.
      inv H0.
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
    forall (rs: regset) cp m j__δ rs' m' al vl
      (eval: eval_builtin_args ge1 rs cp (rs X2) m al vl)
      (inj_pres: meminj_preserves_globals s δ W1 W3 j__δ)
      (delta_zero: mem_delta_zero j__δ),
      regset_rel j__δ rs rs' ->
      Mem.inject j__δ m m' ->
      (* (forall id, In id (globals_of_builtin_args al) -> kept id) -> *)
      exists vl',
        eval_builtin_args ge3 rs' cp (rs' X2) m' al vl'
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

  Lemma exec_instr_preserved:
    forall j__δ j__oppδ f i rs1 rs1' rs3 m1 m1' m2 m3 st1 st2 st3,
      s |= has_comp_function f ∈ δ ->
      (* agrees_with j__δ (init_meminj W1 W3) -> *)
      (* def_on_addressable s ge1 j__δ δ -> *)
      meminj_preserves_globals s δ W1 W3 j__δ ->
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
      mem_rel s ge1 ge3 j__δ δ m1 m3 ->
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      regset_rel j__δ rs1 rs3 ->
      stack_rel s ge3 δ j__δ j__oppδ st1 st2 st3 ->
      exec_instr ge1 f i rs1 m1 (has_comp_function f) = Next rs1' m1' ->
      exists j__δ' rs3' m3',
        exec_instr ge3 f i rs3 m3 (has_comp_function f) = Next rs3' m3' /\
          (* agrees_with j__δ' (init_meminj W1 W3) /\ *)
          (* def_on_addressable s ge1 j__δ' δ /\ *)
          meminj_preserves_globals s δ W1 W3 j__δ' /\
          mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
          mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
          regset_rel j__δ' rs1' rs3' /\
          stack_rel s ge3 δ j__δ' j__oppδ st1 st2 st3.
  Proof.
    intros until st3.
    intros side_cp inj_pres1 inj_pres2 (* addressable *) m1_m3 m2_m3 rs1_rs3 st1_st3 exec.

    Local Opaque Val.cmpu_bool Val.cmplu_bool.
    (* Local Opaque low_half high_half. *)
    Local Opaque opposite.

    destruct i; inv exec; simpl in *;
      try now (simpl_before_exists; (eexists_and_split
                                       ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                                               (simpl; try reflexivity; try eassumption;
                                                solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity)))).
    - (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      destruct (Genv.symbol_address ge1 symb Ptrofs.zero) eqn:FS; eauto.
      exploit (symbol_address_inject s δ W1 W3 j__δ symb Ptrofs.zero);
        eauto using delta_zero.
      rewrite FS. intros H. inv H.
      erewrite <- (find_comp_of_block_preserved s W1 W3);
        eauto using delta_zero.
      destruct (Genv.find_comp_of_block ge1 b) eqn:?; eauto.
      destruct (has_comp_function f =? c)%positive eqn:?; eauto.
      destruct (Genv.find_def ge1 b) as [[] |] eqn:?; eauto.
      exploit defs_inject; eauto.
      intros ([] & ? & _ & ? & ?). rewrite H.
      econstructor; eauto.
      inv H0.
    - (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      destruct (Genv.symbol_address ge1 symb Ptrofs.zero) eqn:FS; eauto.
      exploit (symbol_address_inject s δ W1 W3 j__δ symb Ptrofs.zero);
        eauto using delta_zero.
      rewrite FS. intros H. inv H.
      erewrite <- (find_comp_of_block_preserved s W1 W3);
        eauto using delta_zero.
      destruct (Genv.find_comp_of_block ge1 b) eqn:?; eauto.
      destruct (has_comp_function f =? c)%positive eqn:?; eauto.
      destruct (Genv.find_def ge1 b) as [[] |] eqn:?; eauto.
      exploit defs_inject; eauto.
      intros ([] & ? & _ & ? & ?). rewrite H.
      econstructor; eauto.
      inv H0.
    - (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      destruct (Genv.symbol_address ge1 id ofs) eqn:FS; eauto.
      exploit (symbol_address_inject s δ W1 W3 j__δ id ofs);
        eauto using delta_zero.
      rewrite FS. intros H. inv H.
      erewrite <- (find_comp_of_block_preserved s W1 W3);
        eauto using delta_zero.
      destruct (Genv.find_comp_of_block ge1 b) eqn:?; eauto.
      destruct (has_comp_function f =? c)%positive eqn:?; eauto.
      destruct (Genv.find_def ge1 b) as [[] |] eqn:?; eauto.
      exploit defs_inject; eauto.
      intros ([] & ? & _ & ? & ?). rewrite H.
      econstructor; eauto.
      inv H0.
    - (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      replace (high_half ge1 id ofs) with (Genv.symbol_address ge1 id ofs).
      replace (high_half ge3 id ofs) with (Genv.symbol_address ge3 id ofs).
      destruct (Genv.symbol_address ge1 id ofs) eqn:FS; eauto.
      exploit (symbol_address_inject s δ W1 W3 j__δ id ofs);
        eauto using delta_zero.
      rewrite FS. intros H. inv H.
      erewrite <- (find_comp_of_block_preserved s W1 W3);
        eauto using delta_zero.
      destruct (Genv.find_comp_of_block ge1 b) eqn:?; eauto.
      destruct (has_comp_function f =? c)%positive eqn:?; eauto.
      destruct (Genv.find_def ge1 b) as [[] |] eqn:?; eauto.
      exploit defs_inject; eauto.
      intros ([] & ? & _ & ? & ?). rewrite H.
      econstructor; eauto.
      inv H0.
      reflexivity. reflexivity.
      Unshelve.
      all: try assumption.
      all: eapply match_prog_unique; eauto.
  Qed.

  Lemma exec_instr_preserves_weak:
    forall j__δ j__oppδ f i rs2 rs2' m2 m2' m3 st1 st2 st3,
      s (has_comp_function f) = δ ->
      exec_instr ge2 f i rs2 m2 (has_comp_function f) = Next rs2' m2' ->
      (* meminj_preserves_globals s δ W1 W3 j__δ -> *)
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
      (* agrees_with j__oppδ (init_meminj W2 W3) -> *)
      (* def_on_addressable s ge2 j__oppδ (opposite δ) -> *)
      (* meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ -> *)
      mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3 ->
      stack_rel s ge3 δ j__δ j__oppδ st1 st2 st3 ->
      exists j__oppδ',
      (* meminj_preserves_globals s δ W1 W3 j__δ -> *)
      meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ' /\
        (* agrees_with j__oppδ' (init_meminj W2 W3) /\ *)
        (* def_on_addressable s ge2 j__oppδ' (opposite δ) /\ *)
        mem_rel s ge2 ge3 j__oppδ' (opposite δ) m2' m3 /\
          stack_rel s ge3 δ j__δ j__oppδ' st1 st2 st3.
  Proof.
    intros j__δ j__oppδ f i rs2 rs2' m2 m2' m3 st1 st2 st3 side_f exec (* agr addr *) inj_pres m2_m3 st_rel.
    destruct i; inv exec; simpl in *;
      try (now simpl_before_exists; eauto);
      try (now exploit exec_store_preserves_weak; eauto).
    - (* alloc + store *)
      simpl_before_exists.
      exploit alloc_preserves_weak; eauto.
      intros [j' [? [? ?]]].
      exploit store_preserves_weak; eauto.
      intros ?. exists j'; split; [| split]; eauto using inject_incr_stack_rel2.
      (* now eapply def_on_addressable_incr; eauto. *)
    - (* free *)
      simpl_before_exists.
      exists j__oppδ; split; [| split]; auto.
      constructor.
      + intros b'. apply same_dom in m2_m3.
        specialize (m2_m3 b').
        simpl in *. erewrite Mem.free_result with (m2 := m2'); eauto.  unfold Mem.unchecked_free in *.
        destruct (zle sz 0); now subst.
      + eapply Mem.free_left_inject; eauto using partial_mem_inject.
      + eapply delta_zero; eauto.
      + erewrite Mem.nextblock_free; eauto using ple_nextblock1.
      + eapply ple_nextblock2; eauto.
      + intros. eapply Mem.valid_block_free_1; eauto using find_def_valid1.
      + intros. eapply find_def_valid2; eauto.
      + intros. intros n.
        eapply find_def_perm1; eauto.
        eapply Mem.perm_free_3; eauto.
      + intros. eapply find_def_perm2; eauto.
      + intros. eapply same_high_half; eauto.
  Qed.

  (* External calls preserved *)
  Lemma external_call_inject_left:
    forall ef vargs m1 t vres m2 j__δ j__oppδ m1' vargs' m3 rs1 rs3 st1 st2 st3,
      s (comp_of ef) = δ ->
      meminj_preserves_globals s δ W1 W3 j__δ ->
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
          meminj_preserves_globals s δ W1 W3 j__δ' /\
          mem_rel s ge1 ge3 j__δ' δ m1' m3' /\
          mem_rel s ge2 ge3 j__oppδ (opposite δ) m2 m3' /\
          regset_rel j__δ' rs1 rs3 /\
          stack_rel s ge3 δ j__δ' j__oppδ st1 st2 st3.
  Proof.
    intros * s_ef inj_pres extcall1 inj_args m1_m3 m2_m3 rs1_rs3 st_rel.
    exploit external_call_mem_inject_gen; eauto using partial_mem_inject.
    eapply globals_symbols_inject; eauto.
    intros (j__δ' & vres' & m3' & extcall3 & inj_res & inj_mem & unchanged1 & unchanged2 & incr & inj_sep & comp_new).

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


  Notation comp_of1 := (@comp_of _ (has_comp_state W1)).
  Notation comp_of2 := (@comp_of _ (has_comp_state W2)).
  Notation comp_of3 := (@comp_of _ (has_comp_state W3)).

  Definition stack_of_state (s: state) :=
    match s with
    | State st _ _ | ReturnState st _ _ _ => st
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

  Lemma regset_rel_invalidate_call: forall j rs1' rs3' sig,
      regset_rel j rs1' rs3' ->
      regset_rel j (invalidate_call rs1' sig) (invalidate_call rs3' sig).
  Proof.
    intros ? ? ? ? H.
    intros r. specialize (H r).
    unfold invalidate_call.
    destruct orb; auto.
  Qed.

  Lemma regset_rel_invalidate_cross_call: forall j rs1' rs3' cp cp',
      mem_delta_zero j ->
      regset_rel j rs1' rs3' ->
      regset_rel j (invalidate_cross_call rs1' cp cp') (invalidate_cross_call rs3' cp cp').
  Proof.
    intros ? ? ? ? ? dz H.
    intros r. specialize (H r).
    unfold invalidate_cross_call.
    destruct Genv.type_of_call; try auto.
    destruct preg_eq; try congruence.
    subst; inv H; auto. econstructor; eauto. exploit dz; eauto.
    intros ->. now rewrite Ptrofs.add_zero.
    destruct preg_eq; try congruence. now constructor.
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

  Lemma invalidate_return_PC_comp: forall (ge: genv) rs cp cp' st,
      (cp <> cp' -> rs PC = asm_parent_ra st) ->
      Genv.find_comp ge (invalidate_cross_return rs cp cp' st PC) =
        Genv.find_comp ge (rs PC).
  Proof. intros.
         unfold invalidate_cross_return.
         unfold Genv.type_of_call.
         destruct (Pos.eq_dec cp cp'). subst. rewrite Pos.eqb_refl. reflexivity.
         rewrite H; eauto. apply Pos.eqb_neq in n. rewrite n. simpl.
         reflexivity.
  Qed.

  (* Some simulation diagrams *)
  Lemma step_E0_strong: forall (s1 s1': state),
      Step (semantics W1) s1 E0 s1' ->
      forall (s2 s3: state) j__δ j__oppδ,
        meminj_preserves_globals s δ W1 W3 j__δ ->
        meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
        (* agrees_with j__δ (init_meminj W1 W3) -> *)
        (* def_on_addressable s ge1 j__δ δ -> *)
        stack_rel s ge3 δ j__δ j__oppδ (stack_of_state s1) (stack_of_state s2) (stack_of_state s3) ->
        strong_equivalence s ge1 ge3 j__δ δ s1 s3 ->
        weak_equivalence s ge2 ge3 j__oppδ (opposite δ) s2 s3 ->
        exists (s3': state) j__δ',
          Plus (semantics W3) s3 E0 s3' /\
            meminj_preserves_globals s δ W1 W3 j__δ' /\
            meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ /\
            (* agrees_with j__δ' (init_meminj W1 W3) /\ *)
            (* def_on_addressable s ge1 j__δ' δ /\ *)
            stack_rel s ge3 δ j__δ' j__oppδ (stack_of_state s1') (stack_of_state s2) (stack_of_state s3') /\
            strong_equivalence s ge1 ge3 j__δ' δ s1' s3' /\
            weak_equivalence s ge2 ge3 j__oppδ (opposite δ) s2 s3'.
  Proof.
    (* simpl. *)
    intros s1 s1' H s2 s3 j__δ j__oppδ inj_pres1 inj_pres2 st_rel strong_s1_s3 weak_s2_s3.
    exploit step_E0_same_cp; eauto. intros same_comp.
    simpl in H.
    inv H; simpl in same_comp.
    - exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_genv. rewrite find_id.
        destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        now simpl in *; rewrite side_f; destruct δ. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      exploit exec_instr_preserved; simpl; eauto.
      intros (j__δ' & rs3' & m3' & exec_instr' & inj_pres' & m1_m3' & m2_m3' & rs1_rs3' & st_rel').

      assert (exists b', rs3' PC = Vptr b' ofs') as [b3' rs3'_PC].
      { pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc.
        assert (delta = 0) by now eapply (delta_zero s ge1 ge3); eauto. subst delta. rewrite Ptrofs.add_zero in *.
        eauto. }

      exists (State st3 rs3' m3'), j__δ'; split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        econstructor; eauto.
        specialize (rs1_rs3' PC) as inj_pc. rewrite NEXTPC, rs3'_PC in inj_pc.
        erewrite <- (find_comp_of_block_preserved _ W1 W3); eauto using delta_zero.
        (* exploit find_comp_of_block_preserved; *)
        (* exploit (agrees_with_init_meminj_find_comp_of_block_preserved s W1 W3); eauto. *)
        inv inj_pc; try congruence.
        exploit (delta_zero s ge1 ge3); eauto; intros ->.
        now rewrite Ptrofs.add_zero in *; eauto.
      + eauto.
      + eauto.
      + eauto.
      + econstructor; eauto.
        * simpl; rewrite NEXTPC; simpl in *; rewrite <- ALLOWED. auto.
      + inv weak_s2_s3; inv A; econstructor; eauto.
        * erewrite <- (find_comp_preserved _ W1 W3 _ j__δ');
            eauto using delta_zero; try congruence.
          rewrite <- same_comp.
          erewrite (find_comp_preserved _ W1 W3 _ j__δ);
            eauto using delta_zero; try congruence.
        * erewrite <- (find_comp_preserved _ W1 W3 _ j__δ');
            eauto using delta_zero; try congruence.
          rewrite <- same_comp.
          erewrite (find_comp_preserved _ W1 W3 _ j__δ);
            eauto using delta_zero; try congruence.

    - exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_genv. rewrite find_id.
        destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        now simpl in *; rewrite side_f; destruct δ. }
      intros <-.
      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      exploit exec_instr_preserved; simpl; eauto.
      intros (j__δ' & rs3' & m3' & exec_instr' & inj_pres' & m1_m3' & m2_m3' & rs1_rs3' & st_rel').

      assert (exists b', rs3' PC = Vptr b' Ptrofs.zero) as [b3' rs3'_PC].
      { pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc.
        assert (delta = 0) by now eapply (delta_zero s ge1 ge3); eauto. subst delta. rewrite Ptrofs.add_zero in *.
        eauto. }
      assert (Genv.find_comp ge1 (rs' PC) = Some (comp_of f)).
      { rewrite invalidate_cross_call_PC, invalidate_call_PC in same_comp. rewrite <- same_comp, H0; simpl.
        erewrite Genv.find_def_find_comp_of_block; eauto. reflexivity. }
      eapply update_stack_call_preserved_internal with (st3 := st3) in STUPD as [? STUPD]; eauto using delta_zero; try congruence.
      subst st'.
      exploit call_arguments_preserved; eauto.
      intros [args' [inj_args call_args']].

      exists (State st3 (invalidate_cross_call (invalidate_call rs3' sig) (comp_of f) (comp_of f)) m3'), j__δ';
        split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_internal_call; eauto.
        * eapply allowed_call_preserved with (v := Vptr b' Ptrofs.zero);
            eauto using delta_zero.
          congruence.
          specialize (rs1_rs3' PC) as inj_pc. rewrite NEXTPC, rs3'_PC in inj_pc.
          inv inj_pc; try congruence. exploit (delta_zero s ge1 ge3); eauto; intros ->.
          (* rewrite Ptrofs.add_zero in *. *)
          (* eapply Val.inject_ptr; eauto. *)
        * rewrite <- H, NEXTPC; simpl.
          specialize (rs1_rs3' PC); inv rs1_rs3'; try congruence.
          assert (b1 = b') by congruence; subst.
          assert (b2 = b3') by congruence; subst.
          erewrite <- find_comp_of_block_preserved; eauto using delta_zero.
        * intros.
          exploit Genv.type_of_call_same_cp; eauto. contradiction.
        * intros ?.
          exploit Genv.type_of_call_same_cp; eauto. contradiction.
        * constructor; eauto.
          now apply Genv.type_of_call_same_cp.
      + eauto.
      + eauto.
      + simpl. eauto.
      + econstructor.
        rewrite invalidate_cross_call_PC, invalidate_call_PC; eauto. eauto.
        replace (has_comp_function f) with (comp_of f) by reflexivity.
        assert (cp' = comp_of f).
        { rewrite NEXTPC in H. simpl in H; rewrite NEXTCOMP in H. now inv H. }
        subst.
        eapply regset_rel_invalidate_cross_call; eauto using delta_zero.
        eapply regset_rel_invalidate_call; eauto.
        eauto.
      + inv weak_s2_s3; inv A; econstructor; eauto.
        * rewrite <- H10.
          rewrite invalidate_cross_call_PC.
          rewrite invalidate_call_PC.
          erewrite <- (find_comp_preserved _ W1 W3 _ j__δ'); eauto using delta_zero;
            try congruence.
          erewrite <- (find_comp_preserved _ W1 W3 _ j__δ (rs PC)); eauto using delta_zero;
            try congruence.
          rewrite H, H0; simpl. unfold Genv.find_comp_of_block. rewrite H1.
          reflexivity.
        * rewrite <- H10.
          rewrite invalidate_cross_call_PC.
          rewrite invalidate_call_PC.
          erewrite <- (find_comp_preserved _ W1 W3 _ j__δ'); eauto using delta_zero;
            try congruence.
          erewrite <- (find_comp_preserved _ W1 W3 _ j__δ (rs PC)); eauto using delta_zero;
            try congruence.
          rewrite H, H0; simpl. unfold Genv.find_comp_of_block. rewrite H1.
          reflexivity.

    (** [State] to [ReturnState] *)
    - exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_genv. rewrite find_id.
        unfold Genv.find_funct_ptr in H1. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        now simpl in *; rewrite side_f; destruct δ. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      exploit exec_instr_preserved; simpl; eauto.
      intros (j__δ' & rs3' & m3' & exec_instr' & inj_pres' & m1_m3' & m2_m3' & rs1_rs3' & st_rel').



      exists (ReturnState st3 rs3' m3' (comp_of f)), j__δ'; split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_internal_return; eauto.
      + eauto.
      + eauto.
      + simpl; eauto.
      + econstructor; eauto.
      + inv weak_s2_s3; inv A.
        * econstructor; eauto.
          rewrite H7, <- H9.
          erewrite <- (find_comp_preserved _ W1 W3 _ j__δ); eauto using delta_zero;
            try congruence.
          now destruct (s (comp_of f)).
        * assert (rec_cp = comp_of f).
          { erewrite <- (find_comp_preserved _ W1 W3 _ j__δ) in H9; eauto using delta_zero;
              try congruence.
            rewrite same_comp in H9. now inv H9. }
          subst rec_cp.
          econstructor; eauto.

    (** [ReturnState] to [State] *)
    - exploit strong_equiv_returnstate_inv; eauto.
      intros (st3 & rs3 & m3 & ? & m1_m3 & rs1_rs3); subst.

      (* inv weak_s2_s3. *)

      eapply update_stack_return_preserved_internal with (st3 := st3) in STUPD as [? STUPD];
        eauto using delta_zero; try congruence.
      subst st'.
      simpl in st_rel.
      assert (same_sg: sig_of_call st = sig_of_call st3) by (inv st_rel; [reflexivity | inv H4; auto]).

      assert (res_inj: Val.inject j__δ (return_value rs (sig_of_call st)) (return_value rs3 (sig_of_call st3))).
      { simpl in st_rel.
        rewrite <- same_sg.
        unfold return_value.
        destruct (loc_result (sig_of_call st)).
        - now apply rs1_rs3.
        - apply Val.longofwords_inject; now apply rs1_rs3. }

      assert (rec_cp = cp').
      { inv EV; auto.
        unfold Genv.type_of_call in H.
        destruct Pos.eqb eqn:?; try now auto.
        now apply Peqb_true_eq in Heqb.
      }
      subst rec_cp.
      rewrite invalidate_return_PC_comp in same_comp.
      rewrite invalidate_return_PC in same_comp.
      rewrite NEXTCOMP in same_comp; inv same_comp.

      exists (State st3 (invalidate_return rs3 (sig_of_call st3)) m3), j__δ;
        split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_return; eauto.
        * pose proof (rs1_rs3 PC) as inj_pc; inv inj_pc; try congruence.
          unfold Vnullptr; destruct Archi.ptr64; congruence.
        * pose proof (rs1_rs3 PC) as inj_pc; inv inj_pc; try congruence.
        * erewrite <- (find_comp_preserved _ W1 W3); eauto using delta_zero.
        * congruence.
        * congruence.
        * intros; exploit Genv.type_of_call_same_cp; eauto; contradiction.
        (* * erewrite <- (find_comp_preserved _ W1 W3); eauto using delta_zero. *)
        (* * eapply stack_rel_same_callee in st_rel as [R _]; eauto. simpl in R; rewrite <- R. *)
        (*   rewrite (match_prog_comp_of_main _ _ _ _ match_W1_W3). rewrite same_comp. *)
        (*   erewrite find_comp_ignore_offset_preserved; eauto using delta_zero. *)
        (*   simpl; congruence. *)
        (* * eapply stack_rel_same_callee in st_rel as [R _]; eauto. simpl in R; rewrite <- R. *)
        (*   rewrite (match_prog_comp_of_main _ _ _ _ match_W1_W3). rewrite same_comp. eauto. *)
        (* * eapply stack_rel_same_callee in st_rel as [R _]; eauto. simpl in R; rewrite <- R. *)
        (*   rewrite (match_prog_comp_of_main _ _ _ _ match_W1_W3). rewrite same_comp. *)
        (*   erewrite find_comp_ignore_offset_preserved; eauto using delta_zero. *)
        (*   unfold Genv.type_of_call; rewrite Pos.eqb_refl; congruence. *)
        * eapply return_trace_inj; eauto. rewrite <- same_sg. eauto.
        * unfold invalidate_cross_return.
          inv EV. destruct Genv.type_of_call; now auto.
      + eauto.
      + eauto.
      + simpl. eauto.
      + econstructor; try rewrite same_sg; eauto using regset_rel_invalidate_return.
        rewrite invalidate_return_PC_comp with (ge := ge1). eauto. eauto.
        (* congruence. *)
        now inv strong_s1_s3.
        unfold invalidate_cross_return.
          inv EV. destruct Genv.type_of_call; try congruence.
          eapply regset_rel_invalidate_return; eauto.
      + inv weak_s2_s3; econstructor; eauto;
          rewrite invalidate_return_PC;
        erewrite <- (find_comp_preserved _ W1 W3); eauto using delta_zero.
      + congruence.
      + rewrite same_comp.
        rewrite invalidate_return_PC_comp.
        rewrite invalidate_return_PC. reflexivity.
        auto.


    (** Builtin *)
    - exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_genv. rewrite find_id.
        unfold Genv.find_funct_ptr in H1. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        now simpl in *; rewrite side_f; destruct δ. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).

      exploit eval_builtin_args_inject; eauto using delta_zero, partial_mem_inject.
      intros (vl' & eval_args' & inj_args').
      exploit external_call_inject_left; eauto using partial_mem_inject.
      rewrite ALLOWED; auto.
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      eexists; exists j__δ'; split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_builtin; eauto.
      + eauto.
      + eauto.
      + simpl. eapply inject_incr_stack_rel1; eauto.
      + econstructor; eauto.
        * simpl. rewrite <- same_comp. rewrite H0; simpl.
          erewrite Genv.find_def_find_comp_of_block; eauto. reflexivity.
        * eapply regset_rel_return_from_builtin; eauto.
      + inv weak_s2_s3; inv A; econstructor; eauto.
        * exploit regset_rel_return_from_builtin; eauto. intros ?.
          erewrite <- (find_comp_preserved _ W1 W3); eauto using delta_zero.
          rewrite <- same_comp.
          erewrite (find_comp_preserved _ W1 W3); eauto using delta_zero.
          congruence.
          rewrite nextinstr_pc_return_builtin_value, H0; eauto. simpl; congruence.
        * exploit regset_rel_return_from_builtin; eauto. intros ?.
          erewrite <- (find_comp_preserved _ W1 W3); eauto using delta_zero.
          rewrite <- same_comp.
          erewrite (find_comp_preserved _ W1 W3); eauto using delta_zero.
          congruence.
          rewrite nextinstr_pc_return_builtin_value, H0; eauto. simpl; congruence.

    (** External call *)
    - exploit strong_equiv_state_external_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & ? & eq_pc' & find_funct & m1_m3 & rs1_rs3 & side_ef);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).

      exploit extcall_arguments_preserved; eauto.
      intros (args' & inj_args & extcall_args').

      exploit external_call_inject_left; eauto using partial_mem_inject.
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').
      eexists; exists j__δ'; split; [| split; [| split; [| split; [| split]]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_external; eauto.
        (* rewrite eq_pc'; simpl; unfold Genv.find_comp; simpl; rewrite find_funct; destruct Ptrofs.eq_dec; try congruence. *)
        (* eapply stack_rel_same_callee in st_rel as [R ?]. rewrite <- R, (match_prog_comp_of_main _ _ _ _ match_W1_W3); simpl. *)
        (* rewrite <- REC_CURCOMP, H0; simpl; unfold Genv.find_comp; simpl; rewrite H1. now destruct Ptrofs.eq_dec; try congruence. *)
      + eauto.
      + eauto.
      + simpl. eapply inject_incr_stack_rel1; eauto.
      + econstructor; eauto.
        (* * simpl. rewrite <- same_comp. rewrite H0; simpl; unfold Genv.find_comp; simpl; rewrite H1. destruct Ptrofs.eq_dec; try congruence; auto. *)
        * eapply regset_rel_return_from_external; eauto.
      + inv weak_s2_s3; inv A.
        * econstructor; eauto.
          rewrite H6, <- H8.
          erewrite <- (find_comp_preserved _ W1 W3); eauto using delta_zero.
          congruence.
          now destruct (s (comp_of ef)).
        * assert (rec_cp = comp_of ef).
          { erewrite <- (find_comp_preserved _ W1 W3) in H8; eauto using delta_zero.
            rewrite H0 in H8; simpl in H8; erewrite Genv.find_def_find_comp_of_block in H8;
              eauto.
            inv H8. reflexivity. congruence. }
          subst rec_cp.
          econstructor; eauto.
  Qed.

  Lemma step_E0_weak: forall (s2 s2': state),
      Step (semantics W2) s2 E0 s2' ->
      forall (s1 s3: state) j__δ j__oppδ,
        meminj_preserves_globals s δ W1 W3 j__δ ->
        meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
        stack_rel s ge3 δ j__δ j__oppδ (stack_of_state s1) (stack_of_state s2) (stack_of_state s3) ->
        strong_equivalence s ge1 ge3 j__δ δ s1 s3 ->
        weak_equivalence s ge2 ge3 j__oppδ (opposite δ) s2 s3 ->
        exists j__oppδ',
          meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ' /\
          stack_rel s ge3 δ j__δ j__oppδ' (stack_of_state s1) (stack_of_state s2') (stack_of_state s3) /\
                    strong_equivalence s ge1 ge3 j__δ δ s1 s3 /\
                    weak_equivalence s ge2 ge3 j__oppδ' (opposite δ) s2' s3.
  Proof.
    intros s2 s2' H s1 s3 j__left j__right inj_pres1 inj_pres2 st_rel strong_s1_s3 weak_s2_s3.
    exploit step_E0_same_cp; eauto. intros same_comp.
    simpl in H.
    inv H; simpl in same_comp.

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      assert (f_left: s (has_comp_function f) = δ).
      { inv weak_s2_s3; inv B.
        - rewrite H0 in H8; simpl in H8;
            erewrite Genv.find_def_find_comp_of_block in H8; eauto.
          inv H8.
          now destruct δ.
        - rewrite H0 in H8; simpl in H8;
            erewrite Genv.find_def_find_comp_of_block in H8; eauto.
          inv H8.
          now destruct δ. }
      exploit exec_instr_preserves_weak; eauto.
      intros (j__oppδ' & ? & m'_m3 & st_rel').
      eexists.
      repeat (split; eauto).
      inv weak_s2_s3; inv B;
        econstructor; eauto; now (simpl; rewrite <- same_comp).

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      assert (f_left: s (has_comp_function f) = δ).
      { inv weak_s2_s3; inv B.
        - rewrite H0 in H7; simpl in H7;
            erewrite Genv.find_def_find_comp_of_block in H7; eauto.
          inv H7.
          now destruct δ.
        - rewrite H0 in H7; simpl in H7;
            erewrite Genv.find_def_find_comp_of_block in H7; eauto.
          inv H7.
          now destruct δ. }
      exploit exec_instr_preserves_weak; eauto.
      intros (j__right' & ? & m'_m3 & st_rel').
      assert (st' = st2); [| subst st'].
      { unfold update_stack_call in STUPD.
        assert (same_comp': Some (comp_of f) = Genv.find_comp ge2 (rs' PC)).
        { inv EV; auto. unfold Genv.type_of_call in *.
          destruct (Pos.eqb_spec (comp_of f) cp'); simpl; eauto.
          simpl in e. rewrite e.  now rewrite NEXTPC; simpl.  contradiction. }
        simpl in same_comp'.
        rewrite <- same_comp', Pos.eqb_refl in STUPD.
        now inv STUPD. }
      eexists.
      repeat (split; eauto).
      inv weak_s2_s3; inv B; econstructor; eauto; now (simpl; rewrite <- same_comp).

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      exploit exec_instr_preserves_weak; eauto.
      { inv weak_s2_s3; inv B.
        - rewrite H0 in H7; simpl in H7;
            erewrite Genv.find_def_find_comp_of_block in H7; eauto.
          inv H7.
          now destruct δ.
        - rewrite H0 in H7; simpl in H7;
            erewrite Genv.find_def_find_comp_of_block in H7; eauto.
          inv H7.
          now destruct δ. }
      intros (j__right' & ? & m'_m3 & st_rel').

      eexists.
      repeat (split; eauto).
      inv weak_s2_s3; inv B.
      + rewrite H8 in same_comp; inv same_comp; auto.
        constructor; eauto.
      + rewrite H8 in same_comp; inv same_comp; auto.
        constructor; eauto.

    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A.

      rewrite invalidate_return_PC_comp in same_comp; eauto.
      rewrite invalidate_return_PC in same_comp;
        rewrite NEXTCOMP in same_comp; inv same_comp.

      assert (st' = st2); [| subst st'].
      { unfold update_stack_return in STUPD.
        rewrite NEXTCOMP, Pos.eqb_refl in STUPD. now inv STUPD. }
      eexists.
      repeat (split; eauto).
      inv weak_s2_s3; inv B;
        econstructor; eauto.
      rewrite invalidate_return_PC_comp; eauto.
      rewrite invalidate_return_PC_comp; eauto.


    - exploit weak_equivalence_inv; eauto.
      intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A. simpl.
      exploit extcall_preserves_mem_rel_opp_side1; eauto.
      { inv weak_s2_s3.
        - rewrite H0 in H7; simpl in H7;
            erewrite Genv.find_def_find_comp_of_block in H7; eauto.
          inv H7. simpl in ALLOWED. rewrite <- ALLOWED in H10.
          now destruct δ.
        - rewrite H0 in H7; simpl in H7;
            erewrite Genv.find_def_find_comp_of_block in H7; eauto.
          inv H7. simpl in H9, ALLOWED. rewrite <- ALLOWED in H9.
          now destruct δ. }
      intros m'_m3'.

      eexists; do 3 (split; eauto).
      inv weak_s2_s3; inv B; (econstructor; eauto);
        rewrite <- same_comp; auto.

    - exploit weak_equivalence_inv; eauto. intros (st2 & st3 & rs2 & rs3 & m2 & m3 & m2_m3 & A & B).
      inv A. simpl in *.
      exploit extcall_preserves_mem_rel_opp_side1; eauto.
      { inv weak_s2_s3; inv B.
        - rewrite H0 in H6; simpl in H6;
            erewrite Genv.find_def_find_comp_of_block in H6; eauto.
          inv H6.
          now destruct δ.
        - rewrite H0 in H6; simpl in H6;
            erewrite Genv.find_def_find_comp_of_block in H6; eauto.
          inv H6.
          now destruct δ. }
      intros m'_m3'.

      eexists; do 3 (split; eauto).
      inv weak_s2_s3; inv B.
      + rewrite H6 in same_comp; inv same_comp; auto. econstructor; eauto.
      + rewrite H6 in same_comp; inv same_comp; auto. econstructor; eauto.
  Qed.

  Lemma transf_regset_rel:
    forall cp cp' rs rs' j__oppδ' m1 m3 sig args,
      Forall not_ptr args ->
      Val.inject j__oppδ' (rs PC) (rs' PC) ->
      ( match rs RA, rs' RA with
        | Vptr b0 _, Vptr b3 _ => j__oppδ' b0 = Some (b3, 0%Z)
        | _, _ => False
        end) ->
      cp <> cp' ->
      call_arguments rs m1 sig args ->
      call_arguments rs' m3 sig args ->
      regset_rel j__oppδ' (invalidate_cross_call (invalidate_call rs sig) cp cp')
        (invalidate_cross_call (invalidate_call rs' sig) cp cp').
    Proof.
      unfold invalidate_cross_call.
      unfold invalidate_call.
      intros * noptr inj_pc inj_x1 diff call1 call2 r.
      assert (Genv.type_of_call cp cp' = Genv.CrossCompartmentCall) as ->.
      { unfold Genv.type_of_call.
        destruct (cp =? cp')%positive eqn:?; try congruence.
        exfalso. apply diff. apply Peqb_true_eq. auto. }
      destruct (preg_eq r PC) eqn:?; [subst; simpl; auto|].
      destruct (preg_eq r X1). subst.  rewrite Heqs0.
      (* destruct (preg_eq r X2); [subst; simpl; auto|]. *)
      destruct in_dec; simpl; auto.
      destruct (rs X1); try now constructor.
      destruct (rs' X1); try contradiction.
      econstructor; eauto.
      destruct (preg_eq r X2). constructor.
      destruct in_dec; simpl; auto.
      unfold LTL.parameters_mregs in *.
      unfold call_arguments in *.
      clear Heqs0.
      clear n. clear n0. clear n1.
      revert args noptr call1 call2 r i. clear.
      remember (loc_parameters sig) as ls. clear Heqls.
      Local Opaque all_mregs.
      induction ls.
      - simpl. now auto.
      - intros [| arg args] noptr H1 H2 r H; try now inv H1.
        inv noptr. inv H1. inv H2.
        specialize (IHls args H5 H9 H10).
        admit.
    Admitted.

  Lemma step_t: forall (s1 s1': state) (s2 s2': state) e,
      Step (semantics W1) s1 (e :: nil) s1' ->
      Step (semantics W2) s2 (e :: nil) s2' ->
      forall (s3: state) j__δ j__oppδ,
        meminj_preserves_globals s δ W1 W3 j__δ ->
        meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ ->
        stack_rel s ge3 δ j__δ j__oppδ (stack_of_state s1) (stack_of_state s2) (stack_of_state s3) ->
        strong_equivalence s ge1 ge3 j__δ δ s1 s3 ->
        weak_equivalence s ge2 ge3 j__oppδ (opposite δ) s2 s3 ->
        exists s3' j__δ' j__oppδ',
          Plus (semantics W3) s3 (e :: nil) s3' /\
          meminj_preserves_globals s δ W1 W3 j__δ' /\
          meminj_preserves_globals s (opposite δ) W2 W3 j__oppδ' /\
            stack_rel s ge3 δ j__δ' j__oppδ' (stack_of_state s1') (stack_of_state s2') (stack_of_state s3') /\
            ((strong_equivalence s ge1 ge3 j__δ' δ s1' s3' /\
                weak_equivalence s ge2 ge3 j__oppδ' (opposite δ) s2' s3') \/
               (weak_equivalence s ge1 ge3 j__δ' δ s1' s3' /\
                  strong_equivalence s ge2 ge3 j__oppδ' (opposite δ) s2' s3')).
  Proof.
    intros s1 s1' s2 s2' e step1 step2 s3 j__δ j__oppδ inj_pres_δ inj_pres_opp_δ
      st_rel strong_s1_s3 weak_s2_s3.
    simpl in step1, step2.

    inv step1; inv step2;
      try now (do 2 match goal with
                 | H: call_trace _ _ _ _ _ _ (?e :: nil) |- _ => inv H
                 | H: return_trace _ _ _ _ _ (?e :: nil) |- _ => inv H
                 | H: external_call _ _ _ _ (?e :: nil) _ _ |- _ => eapply ec_no_crossing in H;
                                                                 eauto using external_call_spec
                 end); try contradiction.
    (* Should get 6 cases *)

    - (* Call *)
      exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_genv. rewrite find_id.
        unfold Genv.find_funct_ptr in H0. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        now simpl in *; rewrite side_f; destruct δ. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A). injection A; intros -> -> ->; clear A.
      exploit exec_instr_preserved; simpl; eauto.
      intros (j__δ' & rs3' & m3' & exec_instr' & inj_pres' & m1_m3' & m2_m3' & rs1_rs3' & st_rel').
      assert (side_f0: s (has_comp_function f0) = δ).
      { clear -side_f EV EV0.
        inv EV; inv EV0. simpl; congruence. }
      exploit exec_instr_preserves_weak; simpl; [exact side_f0 | | | | | ]; eauto.
      intros (j__oppδ' & ? & m'0_m3' & st_rel'').

      assert (exists b', rs3' PC = Vptr b' Ptrofs.zero) as [b3' rs3'_PC].
      { pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc.
        assert (delta = 0) by now eapply (delta_zero s ge1 ge3); eauto. subst delta. rewrite Ptrofs.add_zero in *.
        eauto. }

      exploit call_arguments_preserved; eauto.
      intros [args' [inj_args call_args']].

      assert (diff_comp: comp_of f <> cp').
      { clear -EV.
        inv EV; eauto.
        intros neg; rewrite neg in H0. now apply Genv.type_of_call_same_cp in H0. }

      exploit (exec_instr_call_pc ge1 f i); eauto.
      exploit (exec_instr_call_pc ge2 f0 i0); eauto.
      exploit (exec_instr_call_pc ge3 f i); eauto.
      rewrite eq_pc', H4, H; simpl.
      intros rs3'_X1 rs'0_X1 rs'_X1.

      assert (st' = Stackframe b sig (rs' X2) (Ptrofs.add ofs Ptrofs.one)
                      :: st).
      { clear -rs'_X1 STUPD NEXTPC NEXTCOMP diff_comp.
        unfold update_stack_call in STUPD. rewrite NEXTPC in STUPD; simpl in STUPD; rewrite NEXTCOMP in STUPD.
        apply Pos.eqb_neq in diff_comp; simpl in diff_comp; rewrite diff_comp in STUPD.
        rewrite rs'_X1 in STUPD. congruence. }

      assert (Genv.find_comp ge3 (rs3' PC) = Some cp') as NEXTCOMP'.
      { erewrite <- (find_comp_preserved s W1 W3); eauto using delta_zero.
        rewrite NEXTPC; eauto.
        congruence. }

      assert (cp'0 = cp') as ->.
      { clear -EV EV0.
        inv EV; inv EV0. congruence. }


      assert (diff_comp': comp_of f0 <> cp').
      { clear -EV0.
        inv EV0; eauto.
        intros neg; rewrite neg in H0. now apply Genv.type_of_call_same_cp in H0. }

      assert (st'0 = Stackframe b0 sig0 (rs'0 X2) (Ptrofs.add ofs0 Ptrofs.one)
                       :: st2).
      { clear -rs'0_X1 STUPD0 diff_comp' NEXTPC0 NEXTCOMP0.
        unfold update_stack_call in STUPD0.
        rewrite NEXTPC0 in STUPD0; simpl in STUPD0; rewrite NEXTCOMP0 in STUPD0.
        apply Pos.eqb_neq in diff_comp'; simpl in diff_comp'; rewrite diff_comp' in STUPD0.
        rewrite rs'0_X1 in STUPD0. congruence. }

      assert (inj1: Val.inject j__δ' (Vptr b (Ptrofs.add ofs Ptrofs.one)) (Vptr b3 (Ptrofs.add ofs Ptrofs.one))).
      { specialize (rs1_rs3' X1). rewrite rs'_X1, rs3'_X1 in rs1_rs3'.
        auto. }

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
        assert (gd0 = gd) by congruence; subst gd0.
        inv match_gd; inv match_gd0. inv H4; inv H7; auto. }
      subst sig0.


      exists (State (Stackframe b3 sig (rs3' X2) (Ptrofs.add ofs Ptrofs.one) :: st3)
           (invalidate_cross_call (invalidate_call rs3' sig) (comp_of f) cp') m3'),
        j__δ', j__oppδ'; split; [| split; [| split; [| split]]]; try assumption.
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_internal_call; eauto.
        * eapply allowed_call_preserved with (v := Vptr b' Ptrofs.zero); eauto using delta_zero.
          congruence.
          specialize (rs1_rs3' PC) as inj_pc. rewrite NEXTPC, rs3'_PC in inj_pc.
          inv inj_pc; try congruence. exploit (delta_zero s ge1 ge3); eauto; intros ->.
          (* rewrite Ptrofs.add_zero in *. *)
          (* eapply Val.inject_ptr; eauto. *)
        * rewrite rs3'_PC in NEXTCOMP'; now simpl in NEXTCOMP'; eauto.
        * unfold update_stack_call.
          rewrite NEXTCOMP'.
          apply Pos.eqb_neq in diff_comp; rewrite diff_comp.
          rewrite rs3'_X1. reflexivity.
        * intros.
          specialize (rs1_rs3' PC). rewrite rs3'_PC, NEXTPC in rs1_rs3'.
          exploit CALLSIG; eauto.
          (* { clear -EV. inv EV; auto. } *)
          intros [fd [Hfd ->]].
          (* apply Genv.find_funct_ptr_iff in Hfd. *)
          inv rs1_rs3'.
          eapply (defs_inject _ _ _ _ _ inj_pres') in Hfd as [gd [find_gd [_ [match_gd ?]]]]; eauto.
          inv match_gd.
          inv H13; eexists; split; eauto.
        * intros ?.
          exploit Val.inject_list_not_ptr; eauto.
        * specialize (rs1_rs3' PC); rewrite rs3'_PC, NEXTPC in rs1_rs3'.
          (* TODO: factorize *)
          eapply call_trace_preserved with (v := Vptr b' Ptrofs.zero); eauto using delta_zero.
      + subst; simpl in *. econstructor; eauto.
        econstructor; auto. simpl. erewrite Genv.find_def_find_comp_of_block; eauto.
        reflexivity.
      + destruct (side_eq (s cp') δ) as [e1 | n1].
        * left; split.
          -- econstructor; eauto. rewrite invalidate_cross_call_PC, invalidate_call_PC, NEXTPC; simpl; auto.
             eauto using regset_rel_invalidate_cross_call, regset_rel_invalidate_call, delta_zero.
          -- econstructor; eauto.
             rewrite invalidate_cross_call_PC, invalidate_call_PC, NEXTPC0; simpl; auto.
             eauto.
             rewrite invalidate_cross_call_PC, invalidate_call_PC; simpl; auto.
             now destruct δ.
        * right; split.
          -- econstructor; eauto;
               [rewrite invalidate_cross_call_PC, invalidate_call_PC, NEXTPC | |]; try now auto.
             eauto.
             rewrite invalidate_cross_call_PC, invalidate_call_PC; simpl; auto.
             destruct δ, (s cp'); now auto.
          -- econstructor; eauto;
               [rewrite invalidate_cross_call_PC, invalidate_call_PC, NEXTPC0; eauto |  |].
             destruct δ, (s cp'); now eauto.
             assert (has_comp_function f0 = comp_of f).
             { inv weak_s2_s3; eauto.
               rewrite H4, eq_pc' in *.
               clear -H17 H19 H5 find_funct.
               unfold Genv.find_comp in *. simpl in *.
               erewrite Genv.find_def_find_comp_of_block in H19; eauto.
               erewrite Genv.find_def_find_comp_of_block in H17; eauto.
               inv H19; inv H17. auto. }
             rewrite H12.
             assert (G: match rs'0 RA, rs3' RA with
                     | Vptr b0 _, Vptr b3 _ => j__oppδ' b0 = Some (b3, 0%Z)
                     | _, _ => False
                     end).
             { rewrite rs'0_X1, rs3'_X1.
               assert (EV': call_trace ge3 (comp_of f) cp' (Vptr b3' Ptrofs.zero) args' (sig_args sig) (e :: nil)).
               { specialize (rs1_rs3' PC); rewrite rs3'_PC, NEXTPC in rs1_rs3'.
                 (* TODO: factorize *)
                 eapply call_trace_preserved with (v := Vptr b' Ptrofs.zero); eauto using delta_zero. }
               (* clear -H0 H5 find_funct inj_pres' H9 m'0_m3' inj1 EV EV0 EV' match_W1_W3 match_W2_W3. *)
               inv EV; inv EV0; inv EV'.
               inv H19; inv H15; inv H24. admit. }
             eapply transf_regset_rel. eapply NO_CROSS_PTR0; eauto.
             unfold Genv.type_of_call. destruct (comp_of f0 =? cp')%positive eqn:X; auto.
             apply Peqb_true_eq in X. congruence.
             rewrite NEXTPC0, rs3'_PC.
             econstructor.
             { (* b'0 and b3' point to the same function *)

               assert (EV': call_trace ge3 (comp_of f) cp' (Vptr b3' Ptrofs.zero) args' (sig_args sig) (e :: nil)).
               { specialize (rs1_rs3' PC); rewrite rs3'_PC, NEXTPC in rs1_rs3'.
                 (* TODO: factorize *)
                 eapply call_trace_preserved with (v := Vptr b' Ptrofs.zero); eauto using delta_zero. }
               inv EV0; inv EV; inv EV'. simpl in *.
               inv H15. inv H29. inv H24.
               exploit (invert_symb_eq_block s W1 W2 W3); eauto using match_prog_unique.
               admit. }
             instantiate (1 := 0%Z). now rewrite Ptrofs.add_zero.
             auto. auto.
             eapply ARGS0.
             assert (args0 = args') by admit.
             subst; eauto.

    - (* Return *)
      exploit strong_equiv_returnstate_inv; eauto.
      intros (st3 & rs3 & m3 & ? & m_m3 & rs_rs3); subst s3.
      exploit weak_equivalence_inv; eauto; simpl.
      intros (? & ? & ? & ? & ? & ? & m1_m3 & A & B);
        injection A; injection B; intros <- <- <- <- <- <-; clear A B.

      assert (diff_comp1: rec_cp <> cp').
      { clear -EV.
        inv EV.
        now intros H; rewrite H in *; exploit Genv.type_of_call_same_cp; eauto. }
      assert (exists frame1, st = frame1 :: st') as [frame1 ->].
      { unfold update_stack_return in STUPD.
        rewrite NEXTCOMP in STUPD.
        apply Pos.eqb_neq in diff_comp1; simpl in diff_comp1; rewrite diff_comp1 in STUPD.
        destruct st as [|frame1 st1]; try congruence. inv STUPD. eauto. }

      assert (cp'0 = cp') as ->.
      { clear -EV EV0.
        inv EV; inv EV0. congruence. }

      assert (rec_cp0 = rec_cp) as ->.
      { clear -EV EV0.
        inv EV; inv EV0. congruence. }

      assert (exists frame2, st0 = frame2 :: st'0) as [frame2 ->].
      { unfold update_stack_return in STUPD0.
        rewrite NEXTCOMP0 in STUPD0.
        apply Pos.eqb_neq in diff_comp1; rewrite diff_comp1 in STUPD0.
        destruct st0 as [|frame2 st2]; try congruence. inv STUPD0. eauto. }

      assert (exists frame3 st3', st3 = frame3 :: st3' /\
                               stackframe_rel s ge3 δ j__δ j__oppδ frame1 frame2 frame3 /\
                               stack_rel s ge3 δ j__δ j__oppδ st' st'0 st3')
        as [frame3 [st3' [-> [frame_rel st_rel']]]] by now inv st_rel; eauto.

      assert (update_stack_return ge3 (frame3 :: st3')
                rec_cp rs3 =
                Some st3').
      { unfold update_stack_return.
        erewrite <- (find_comp_preserved s W1 W3 _ _ (rs PC)); eauto using delta_zero.
        rewrite NEXTCOMP.
        apply Pos.eqb_neq in diff_comp1; rewrite diff_comp1. reflexivity. }

      assert (rs3 PC <> Vnullptr).
      { clear -H H0 rs_rs3. specialize (rs_rs3 PC).
        unfold Vnullptr in *; destruct Archi.ptr64; inv rs_rs3; congruence. }
      assert (rs3 PC <> Vundef).
      { clear -H H0 rs_rs3. specialize (rs_rs3 PC).
        unfold Vnullptr in *; destruct Archi.ptr64; inv rs_rs3; congruence. }
      assert (rec_cp <> cp' -> rs3 PC = asm_parent_ra (frame3 :: st3')).
      { inv frame_rel; simpl; eauto.
        intros. exploit PC_RA; eauto.
        simpl. admit.
        intros. exploit PC_RA0; eauto.
        simpl. admit. }

      assert (rec_cp <> cp' -> rs3 X2 = asm_parent_sp (frame3 :: st3')).
      { inv frame_rel; simpl; eauto. admit. admit. }


      assert (inj_res: Val.inject j__δ (return_value rs (sig_of_call (frame3 :: st3')))
                         (return_value rs3 (sig_of_call (frame3 :: st3')))). {
        unfold return_value.
        destruct (loc_result (sig_of_call (frame3 :: st3'))).
        - specialize (rs_rs3 (preg_of r)); eauto.
        - pose proof (rs_rs3 (preg_of rhi)) as X;
            pose proof (rs_rs3 (preg_of rlo)) as Y.
          now eapply Val.longofwords_inject. }
      assert (NO_CROSS_PTR':
               Genv.type_of_call cp' rec_cp = Genv.CrossCompartmentCall ->
               not_ptr (return_value rs3 (sig_of_call (frame3 :: st3')))).
      { intros ?. exploit NO_CROSS_PTR; eauto.
        assert (sig_of_call (frame1 :: st') = sig_of_call (frame3 :: st3')) as ->.
        { inv frame_rel; auto. }
        clear -inj_res. simpl in *.
        inv inj_res; eauto; try intuition congruence.
        contradiction. }
      assert (EV3: return_trace ge3 cp' rec_cp
                     (return_value rs3 (sig_of_call (frame3 :: st3'))) (sig_res (sig_of_call (frame3 :: st3')))
                     (e :: nil)).
      {
        eapply return_trace_inj; eauto.
        assert (sig_of_call (frame1 :: st') = sig_of_call (frame3 :: st3')) as <-.
        { inv frame_rel; auto. } eauto.
        assert (sig_of_call (frame1 :: st') = sig_of_call (frame3 :: st3')) as <-.
        { inv frame_rel; auto. } eauto. }

      assert (Genv.find_comp ge3 (rs3 PC) = Some cp').
      { erewrite <- (find_comp_preserved s W1 W3 _ _ (rs PC)); eauto using delta_zero. }

      exists (State st3' (invalidate_return rs3 (sig_of_call (frame3 :: st3'))) m3); exists j__δ, j__oppδ; split; [| split; [| split; [| split]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        econstructor; eauto. admit.

      + eauto.
      + eauto.
      + eauto.
      + (* simpl in *. *)
        destruct (side_eq (s cp') δ) as [e1 | n1].
        * left; split.
          -- econstructor; eauto.
             admit.
             assert (sig_of_call (frame1 :: st') = sig_of_call (frame3 :: st3')) as <-.
             { inv frame_rel; auto. }
             admit.
             (* eapply regset_rel_invalidate_return; eauto. *)
          -- econstructor; eauto.
             admit.
             now destruct δ.
        * right; split.
          -- econstructor; eauto.
             admit.
             now destruct δ, (s cp').
          -- econstructor; eauto.
             admit. admit. admit.

    - (* Builtin *)
      exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_genv. rewrite find_id.
        unfold Genv.find_funct_ptr in H0. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        now simpl in *; rewrite side_f in *; destruct δ. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      injection A; intros -> -> ->.

      exploit eval_builtin_args_inject; eauto using delta_zero, partial_mem_inject.
      intros (vl' & eval_args' & inj_args').
      exploit external_call_inject_left; eauto using partial_mem_inject.
      rewrite ALLOWED; auto.
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      exploit extcall_preserves_mem_rel_opp_side1; eauto.
      { inv weak_s2_s3; eauto.
        rewrite H4 in H14. simpl in H14.
        erewrite Genv.find_def_find_comp_of_block in H14; eauto. inv H14.
        rewrite ALLOWED0. now auto. }
      intros m'0_m3'.

      eexists; exists j__δ', j__oppδ; split; [| split; [| split; [| split]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_builtin; eauto.
      + eauto.
      + eauto.
      + simpl. eapply inject_incr_stack_rel1; eauto.
      + left; split.
        * econstructor; eauto.
          -- simpl.
             assert (R: nextinstr (set_res res vres
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
             rewrite R.
             rewrite H; simpl.
             erewrite Genv.find_def_find_comp_of_block; eauto. reflexivity.
          -- eapply regset_rel_return_from_builtin; eauto.
        * inv weak_s2_s3; inv A; econstructor; eauto.
          -- simpl.
             assert (R: nextinstr (set_res res0 vres0
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
             rewrite R.
             rewrite H4 in *; simpl in *. now auto.
          -- simpl.
             assert (R: nextinstr (set_res res vres'
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
             rewrite R.
             rewrite eq_pc' in *; simpl in *; now auto.

    - (* builtin / external call *)
      exploit strong_equiv_state_internal_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & f' & ? & eq_pc' & find_funct & [match_f_f' left_implies_eq] & m1_m3 & rs1_rs3 & side_f);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].
      exploit left_implies_eq; eauto.
      { unfold kept_genv. rewrite find_id.
        unfold Genv.find_funct_ptr in H0. destruct (Genv.find_def ge1 b) as [[f''|]|] eqn:R; try congruence.
        assert (f'' = Internal f) by congruence; subst f''. unfold Genv.find_def in R; rewrite R.
        now simpl in *; rewrite side_f in *; destruct δ. }
      intros <-.

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      injection A; intros -> -> ->.

      exploit eval_builtin_args_inject; eauto using delta_zero, partial_mem_inject.
      intros (vl' & eval_args' & inj_args').
      exploit external_call_inject_left; eauto using partial_mem_inject.
      rewrite ALLOWED; auto.
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      exploit extcall_preserves_mem_rel_opp_side1; eauto.
      { inv weak_s2_s3; eauto.
        rewrite H4 in H13. simpl in H13.
        erewrite Genv.find_def_find_comp_of_block in H13; eauto. inv H13.
        now auto. }
      intros m'0_m3'.

      eexists; exists j__δ', j__oppδ; split; [| split; [| split; [| split]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_builtin; eauto.
      + eauto.
      + eauto.
      + simpl. eapply inject_incr_stack_rel1; eauto.
      + left; split.
        * econstructor; eauto.
          -- simpl.
             assert (R: nextinstr (set_res res vres
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
             rewrite R.
             rewrite H; simpl.
             erewrite Genv.find_def_find_comp_of_block; eauto. reflexivity.
          -- eapply regset_rel_return_from_builtin; eauto.
        * inv weak_s2_s3; inv A; econstructor; eauto.
          -- simpl.
             rewrite H4 in H13; simpl in H13.
             erewrite Genv.find_def_find_comp_of_block in H13; eauto. inv H13; auto.
          -- simpl.
             assert (R: nextinstr (set_res res vres'
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
             rewrite R.
             rewrite eq_pc' in *; simpl in *.
             rewrite H15.
             rewrite H4 in H13; simpl in H13.
             erewrite Genv.find_def_find_comp_of_block in H13; eauto. inv H13; auto.

    - (* external_call / builtin *)
      exploit strong_equiv_state_external_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & ? & eq_pc' & find_funct & m1_m3 & rs1_rs3 & side_ef);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      injection A; intros <- <- <-.

      exploit extcall_arguments_preserved; eauto.
      intros (args' & inj_args & extcall_args').


      exploit (extcall_preserves_mem_rel_opp_side1 s ge2 ge3 j__oppδ (opposite δ)
                 m0 m'0 m3); eauto.
      { rewrite ALLOWED. inv weak_s2_s3; simpl in *.
        rewrite H3 in H13. simpl in H13.
        erewrite Genv.find_def_find_comp_of_block in H13; eauto. inv H13.
        now auto. }
      intros m'0_m3.

      exploit external_call_inject_left; eauto using partial_mem_inject.
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      eexists; exists j__δ', j__oppδ; split; [| split; [| split; [| split]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_external; eauto.
      + eauto.
      + eauto.
      + simpl. eapply inject_incr_stack_rel1; eauto.
      + left; split.
        * econstructor; eauto.
          eapply regset_rel_return_from_external; eauto.
        * inv weak_s2_s3; inv A; econstructor; eauto.
          -- assert (R: nextinstr (set_res res0 vres
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
             simpl. rewrite R.
             rewrite H3 in *; simpl in *.
             rewrite eq_pc' in *; simpl in *.
             erewrite Genv.find_def_find_comp_of_block in H15; eauto.
             rewrite H13; auto.
          -- now destruct (s (comp_of ef)).

    - (* External call *)
      exploit strong_equiv_state_external_inv; eauto.
      intros (st3 & rs3 & m3 & b3 & ? & eq_pc' & find_funct & m1_m3 & rs1_rs3 & side_ef);
        subst s3.
      exploit find_def_find_symbol; eauto. intros [id find_id].

      exploit weak_equivalence_inv1; eauto. intros (st2 & rs2 & m2 & m2_m3 & A).
      injection A; intros <- <- <-.

      exploit extcall_arguments_preserved; eauto.
      intros (args' & inj_args & extcall_args').


      exploit (extcall_preserves_mem_rel_opp_side1 s ge2 ge3 j__oppδ (opposite δ)
                 m0 m'0 m3); eauto.
      { inv weak_s2_s3; simpl in *.
        rewrite H3 in H12; simpl in H12.
        erewrite Genv.find_def_find_comp_of_block in H12; eauto. inv H12.
        now auto. }
      intros m'0_m3.

      exploit external_call_inject_left; eauto using partial_mem_inject.
      intros (j__δ' & vres' & m3' & extcall' & inj_res & unchanged1 & unchanged2 & incr & sep & inj_pres' & m'_m3' & m2_m3' & rs_rs3' & st_rel').

      remember ((set_pair (loc_external_result (ef_sig ef)) vres' (undef_caller_save_regs rs3)) # PC <- (rs3 X1)) as rs3'.
      exists (ReturnState st3 rs3' m3' (comp_of ef)).
      exists j__δ', j__oppδ; split; [| split; [| split; [| split]]].
      + econstructor; [| now eapply star_refl | now traceEq].
        eapply exec_step_external; eauto.
      + eauto.
      + eauto.
      + simpl. eapply inject_incr_stack_rel1; eauto.
      + left; split.
        * econstructor; eauto. subst rs3'.
          eapply regset_rel_return_from_external; eauto.
        * inv weak_s2_s3; inv A.
          assert (comp_of ef = comp_of ef0) as R.
          {
            rewrite H3 in H12; simpl in H12.
            erewrite Genv.find_def_find_comp_of_block in H12; eauto.
            rewrite eq_pc' in H14; simpl in H14.
            erewrite Genv.find_def_find_comp_of_block in H14; eauto. inv H12; inv H14. auto. }
          rewrite R in *.
          econstructor; eauto. now destruct (s (comp_of ef0)).
  Admitted.

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

  Hypothesis cp_main_not_none:
    cp_main <> None.

  Hypothesis norepet1: list_norepet (prog_defs_names W1).
  Hypothesis norepet2: list_norepet (prog_defs_names W2).

  Notation ge1 := (Genv.globalenv W1).
  Notation ge2 := (Genv.globalenv W2).
  Notation ge3 := (Genv.globalenv W3).

  Hypothesis same_cp_main1:
    Genv.find_comp ge2 (Genv.symbol_address ge2 (prog_main W2) Ptrofs.zero) =
      Genv.find_comp ge1 (Genv.symbol_address ge1 (prog_main W1) Ptrofs.zero).
  Hypothesis same_cp_main2:
    Genv.find_comp ge3 (Genv.symbol_address ge3 (prog_main W3) Ptrofs.zero) =
      Genv.find_comp ge1 (Genv.symbol_address ge1 (prog_main W1) Ptrofs.zero).

  Hypothesis same_low_half1: low_half ge1 = low_half ge3.
  Hypothesis same_low_half2: low_half ge2 = low_half ge3.

  Hypothesis found_in_W3_kept1: forall id v,
    (s (comp_of v) = Left -> In (id, Gvar v) (prog_defs W3) ->
                 kept_prog s W1 Left id = true).
  Hypothesis found_in_W3_kept2: forall id v,
    (s (comp_of v) = Right -> In (id, Gvar v) (prog_defs W3) ->
                 kept_prog s W2 Right id = true).


  Hypothesis init_mem_correct1: forall m1 m3, Genv.init_mem W1 = Some m1 ->
                               Genv.init_mem W3 = Some m3 ->
                               mem_rel s ge1 ge3 (init_meminj W1 W3) Left m1 m3.
  Hypothesis init_mem_correct2: forall m2 m3, Genv.init_mem W2 = Some m2 ->
                               Genv.init_mem W3 = Some m3 ->
                               mem_rel s ge2 ge3 (init_meminj W2 W3) Right m2 m3.

  Let single_L1 := sd_traces (semantics_determinate W1).
  Let single_L2 := sd_traces (semantics_determinate W2).
  Let single_L3 := sd_traces (semantics_determinate W3).

  Notation comp_of1 := (@comp_of _ (has_comp_state W1)).
  Notation comp_of2 := (@comp_of _ (has_comp_state W2)).
  Notation comp_of3 := (@comp_of _ (has_comp_state W3)).

  Lemma simulation:
    @threeway_simulation (semantics W1) (semantics W2) (semantics W3)
      single_L1 single_L2 single_L3.
  Proof.
    apply threeway_simulation_diagram
      with (metadata := (meminj * meminj)%type)
           (common_equivalence := fun '(j__left, j__right) s1 s2 s3 =>
                                    stack_rel s ge3 Left j__left j__right
                                      (stack_of_state s1) (stack_of_state s2) (stack_of_state s3))
           (strong_equivalence1 := fun '(j__left, j__right) s1 s3 =>
                                       meminj_preserves_globals s Left W1 W3 j__left /\
                                         strong_equivalence s ge1 ge3 j__left Left s1 s3)
           (strong_equivalence2 := fun '(j__left, j__right) s2 s3 =>
                                       meminj_preserves_globals s Right W2 W3 j__right /\
                                         strong_equivalence s ge2 ge3 j__right Right s2 s3)
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
      exploit symbols_inject2; eauto. intros [? [-> ?]]; auto.
      destruct (Genv.find_symbol ge3 id) eqn:?.
      exploit symbols_inject3; eauto. intros [? [? ?]]; auto. congruence.
      auto.
      clear -match_W1_W3. exploit init_meminj_preserves_globals; eauto.
      intros ?.
      unfold Genv.public_symbol, ge1, ge3.
      rewrite 2!(Genv.genv_public_add_globals). fold ge1. fold ge3. simpl.
      erewrite match_prog_public; eauto.
      destruct (Genv.find_symbol ge1 id) eqn:?.
      exploit symbols_inject2; eauto. intros [? [-> ?]]; auto.
      destruct (Genv.find_symbol ge3 id) eqn:?.
      exploit symbols_inject3; eauto. intros [? [? ?]]; auto. congruence.
      auto.
    - simpl. intros id.
      clear -match_W2_W3. exploit init_meminj_preserves_globals; eauto.
      intros ?.
      unfold Genv.public_symbol, ge2, ge3.
      rewrite 2!(Genv.genv_public_add_globals). fold ge2. fold ge3. simpl.
      erewrite match_prog_public; eauto.
      destruct (Genv.find_symbol ge2 id) eqn:?.
      exploit symbols_inject2; eauto. intros [? [-> ?]]; auto.
      destruct (Genv.find_symbol ge3 id) eqn:?.
      exploit symbols_inject3; eauto. intros [? [? ?]]; auto. congruence.
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
          unfold kept_prog. unfold kept_genv.
          unfold kept_prog. unfold kept_genv. eapply found_in_W3_kept2; eauto.
      }
      eexists; eexists (init_meminj W1 W3, init_meminj W2 W3). split.
      + econstructor; eauto.
      + inv ini1; inv ini2.
        destruct (Genv.find_comp ge1 (Genv.symbol_address ge (prog_main W1) Ptrofs.zero))
                   as [cp |] eqn:ini_cp.
        * destruct (s cp) eqn:ini_side.
          -- eapply match_states_left; simpl; eauto.
             ++ econstructor; eauto.
             ++ split; eauto using init_meminj_preserves_globals.
                econstructor; eauto.
                { subst rs0. intros x.
                  setoid_rewrite Pregmap.gsspec.
                  destruct (Pregmap.elt_eq).
                  { unfold Vnullptr. destruct Archi.ptr64; now constructor. }
                  setoid_rewrite Pregmap.gsspec.
                  destruct (Pregmap.elt_eq).
                  { unfold Vnullptr. destruct Archi.ptr64; now constructor. }
                  setoid_rewrite Pregmap.gsspec.
                  destruct (Pregmap.elt_eq).
                  { unfold Genv.symbol_address.
                    destruct (Genv.find_symbol ge (prog_main W1)) eqn:?; try now constructor.
                    exploit (symbols_inject2 s Left W1 W3 (init_meminj W1 W3)); eauto.
                    now eapply init_meminj_preserves_globals.
                    erewrite (match_prog_main _ _ _ _ match_W1_W3); eauto.
                    intros [? [-> ?]]. econstructor; eauto. }
                  setoid_rewrite Pregmap.gi. now constructor. auto. }
             ++ split; eauto using init_meminj_preserves_globals.
                econstructor; eauto.
                { subst rs1. Simpl. subst ge ge0. rewrite same_cp_main1; eauto. }
                { Simpl. rewrite same_cp_main2. eauto. }
          -- eapply match_states_right; simpl; eauto.
             ++ econstructor; eauto.
             ++ split; eauto using init_meminj_preserves_globals.
                econstructor; eauto.
                { Simpl. rewrite same_cp_main2. eauto. }
             ++ split; eauto using init_meminj_preserves_globals.
                econstructor; eauto.
                { subst rs1 ge ge0; Simpl. rewrite same_cp_main1. eauto. }
                { subst rs1. intros x.
                  setoid_rewrite Pregmap.gsspec.
                  destruct (Pregmap.elt_eq).
                  { unfold Vnullptr. destruct Archi.ptr64; now constructor. }
                  setoid_rewrite Pregmap.gsspec.
                  destruct (Pregmap.elt_eq).
                  { unfold Vnullptr. destruct Archi.ptr64; now constructor. }
                  setoid_rewrite Pregmap.gsspec.
                  destruct (Pregmap.elt_eq).
                  { unfold Genv.symbol_address.
                    subst ge0.
                    destruct (Genv.find_symbol ge2 (prog_main W2)) eqn:?; try now constructor.
                    exploit (symbols_inject2 s Right W2 W3 (init_meminj W2 W3)); eauto.
                    now eapply init_meminj_preserves_globals. subst ge.
                    erewrite (match_prog_main _ _ _ _ match_W2_W3); eauto.
                    intros [? [-> ?]]. econstructor; eauto. }
                  setoid_rewrite Pregmap.gi. now constructor. auto. }
        * exfalso. eapply cp_main_not_none.
          unfold cp_main. unfold Genv.symbol_address in *. subst ge.
          destruct (Genv.find_symbol ge1 (prog_main W1)); try congruence.
          auto.
    - intros s1 s1' H s2 s3 (j__left & j__right) (? & ?) (? & ?) ?.
      exploit (step_E0_strong s W1 W2 W3 Left); eauto.
      intros (s3' & j__left' & ? & ? & ? & ? & ? & ?).
      exists s3'; exists (j__left', j__right); split; [assumption |].
      split; [| split]; [| | assumption]; split; eauto.
    - intros s1 s1' H s2 s3 (j__left & j__right) (? & ?) (? & ?) ?.
      exploit (step_E0_strong s W2 W1 W3 (opposite Left)); eauto using stack_rel_comm.
      intros (s3' & j__right' & ? & ? & ? & S & ? & ?).
      exists s3'; exists (j__left, j__right'); split; [assumption |].
      split; [| split]; [| | ].
      + split; eauto.
      + split; eauto.
      + eapply stack_rel_comm in S; eauto.
    - intros s1 s1' H s2 s3 (j__left & j__right) (? & ?) (? & ?) ?.
      exploit (step_E0_weak s W2 W1 W3 (opposite Left)); eauto using stack_rel_comm.
      intros (j__left' & ? & S & ? & ?).
      exists (j__left', j__right).
      split; [| split; apply stack_rel_comm in S; simpl in S]; eauto.
    - intros s1 s1' H s2 s3 (j__left & j__right) (? & ?) (? & ?) ?.
      exploit (step_E0_weak s W1 W2 W3 Left); eauto.
      intros (j__right' & ? & S & ? & ?).
      exists (j__left, j__right').
      split; [| split]; eauto.
    - intros s1 e s1' H s2 s2' H0 s3 (j__left & j__right) H1.
      destruct H1 as [[? ?] ? ? ? ? [? ?] [? ?]
                     | [? ?] ? ? ? ? [? ?] [? ?]].
      + exploit (step_t s W1 W2 W3 Left); eauto.
        intros (s3' & j__left' & j__right' & ? & ? & ? & ? & X).
        exists s3'; exists (j__left', j__right'); split; eauto.
        destruct X as [[? ?] | [? ?]]; [left; eauto | right; eauto].
      + exploit (step_t s W2 W1 W3 (opposite Left)); eauto using stack_rel_comm.
        intros (s3' & j__right' & j__left' & ? & ? & ? & S & X).
        eapply stack_rel_comm in S; simpl in S.
        exists s3'; exists (j__left', j__right'); split; eauto.
        destruct X as [[? ?] | [? ?]]; [right; eauto | left; eauto].
  Qed.

End Simulation.
