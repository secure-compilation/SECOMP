Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Split.
Require Export Memdata.
Require Export Memtype.
Require Import Memory.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).


Section WINJ.

  Import Mem.

  (** * Generic weak injections *)

  (** A memory state [m1] generically weakly injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
   *)

  Record mem_winj (f: meminj) (m1 m2: mem) : Prop :=
    mk_mem_winj {
        mwi_perm:
        forall b1 b2 delta ofs k p,
          f b1 = Some(b2, delta) ->
          perm m1 b1 ofs k p ->
          perm m2 b2 (ofs + delta) k p;
        mwi_own:
        forall b1 b2 delta cp,
          f b1 = Some(b2, delta) ->
          can_access_block m1 b1 cp ->
          can_access_block m2 b2 cp;
        mwi_align:
        forall b1 b2 delta chunk ofs p,
          f b1 = Some(b2, delta) ->
          range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
          (align_chunk chunk | delta);
      }.

  (** Preservation of permissions *)

  Lemma perm_winj:
    forall f m1 m2 b1 ofs k p b2 delta,
      mem_winj f m1 m2 ->
      perm m1 b1 ofs k p ->
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p.
  Proof.
    intros. eapply mwi_perm; eauto.
  Qed.

  Lemma range_perm_winj:
    forall f m1 m2 b1 lo hi k p b2 delta,
      mem_winj f m1 m2 ->
      range_perm m1 b1 lo hi k p ->
      f b1 = Some(b2, delta) ->
      range_perm m2 b2 (lo + delta) (hi + delta) k p.
  Proof.
    intros; red; intros.
    replace ofs with ((ofs - delta) + delta) by lia.
    eapply perm_winj; eauto. apply H0. lia.
  Qed.

  Lemma can_access_block_winj:
    forall f m1 m2 b1 cp b2 delta,
      mem_winj f m1 m2 ->
      can_access_block m1 b1 cp ->
      f b1 = Some(b2, delta) ->
      can_access_block m2 b2 cp.
  Proof.
    intros; red.
    eapply mwi_own; eauto.
  Qed.

  Lemma valid_access_winj:
    forall f m1 m2 b1 b2 delta chunk ofs p cp,
      mem_winj f m1 m2 ->
      f b1 = Some(b2, delta) ->
      valid_access m1 chunk b1 ofs p cp ->
      valid_access m2 chunk b2 (ofs + delta) p cp.
  Proof.
    intros. destruct H1 as [A [B C]]. constructor.
    replace (ofs + delta + size_chunk chunk)
      with ((ofs + size_chunk chunk) + delta) by lia.
    eapply range_perm_winj; eauto.
    split. eapply mwi_own; eauto.
    apply Z.divide_add_r; auto. eapply mwi_align; eauto with mem.
  Qed.

  (** Preservation of stores. *)

  Lemma setN_winj:
    forall (access: Z -> Prop) delta f vl1 vl2,
      list_forall2 (memval_inject f) vl1 vl2 ->
      forall p c1 c2,
        (forall q, access q -> memval_inject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) ->
        (forall q, access q -> memval_inject f (ZMap.get q (setN vl1 p c1))
                                       (ZMap.get (q + delta) (setN vl2 (p + delta) c2))).
  Proof.
    induction 1; intros; simpl.
    auto.
    replace (p + delta + 1) with ((p + 1) + delta) by lia.
    apply IHlist_forall2; auto.
    intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
    rewrite ZMap.gss. auto.
    rewrite ZMap.gso. auto. unfold ZIndexed.t in *. lia.
  Qed.

  Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
    forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
      b1 <> b2 ->
      f b1 = Some (b1', delta1) ->
      f b2 = Some (b2', delta2) ->
      perm m b1 ofs1 Max Nonempty ->
      perm m b2 ofs2 Max Nonempty ->
      b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

  Lemma store_mapped_winj:
    forall f chunk m1 b1 ofs v1 cp n1 m2 b2 delta v2,
      mem_winj f m1 m2 ->
      store chunk m1 b1 ofs v1 cp = Some n1 ->
      meminj_no_overlap f m1 ->
      f b1 = Some (b2, delta) ->
      exists n2,
        store chunk m2 b2 (ofs + delta) v2 cp = Some n2
        /\ mem_winj f n1 n2.
  Proof.
    intros.
    assert (valid_access m2 chunk b2 (ofs + delta) Writable (Some cp)).
    eapply valid_access_winj; eauto with mem.
    destruct (valid_access_store _ _ _ _ _ v2 H3) as [n2 STORE].
    exists n2; split. auto.
    constructor.
    (* perm *)
    intros. eapply perm_store_1; [eexact STORE|].
    eapply mwi_perm; eauto.
    eapply perm_store_2; eauto.
    (* own *)
    intros.
    apply (proj1 (store_can_access_block_inj _ _ _ _ _ _ _ STORE _ _)).
    eapply mwi_own; try eassumption.
    apply (proj2 (store_can_access_block_inj _ _ _ _ _ _ _ H0 _ _)).
    assumption.
    (* align *)
    intros. eapply mwi_align with (ofs := ofs0) (p := p); eauto.
    red; intros; eauto with mem.
  Qed.

  Lemma store_unmapped_winj:
    forall f chunk m1 b1 ofs v1 cp n1 m2,
      mem_winj f m1 m2 ->
      store chunk m1 b1 ofs v1 cp = Some n1 ->
      f b1 = None ->
      mem_winj f n1 m2.
  Proof.
    intros. constructor.
    (* perm *)
    intros. eapply mwi_perm; eauto with mem.
    (* own *)
    intros. eapply mwi_own; eauto.
    (* RB: NOTE: Should be solvable by properly extended hint databases. *)
    apply (proj2 (store_can_access_block_inj _ _ _ _ _ _ _ H0 _ _)).
    assumption.
    (* align *)
    intros. eapply mwi_align with (ofs := ofs0) (p := p); eauto.
    red; intros; eauto with mem.
  Qed.

  Lemma store_outside_winj:
    forall f m1 m2 chunk b ofs v cp m2',
      mem_winj f m1 m2 ->
      (forall b' delta ofs',
          f b' = Some(b, delta) ->
          perm m1 b' ofs' Cur Readable ->
          ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
      store chunk m2 b ofs v cp = Some m2' ->
      mem_winj f m1 m2'.
  Proof.
    intros. inv H. constructor.
    (* perm *)
    eauto with mem.
    (* own *)
    intros.
    (* RB: NOTE: Ditto re: hint databases. *)
    apply (proj1 (store_can_access_block_inj _ _ _ _ _ _ _ H1 _ _)); eauto.
    (* access *)
    intros; eapply mwi_align0; eauto.
  Qed.

  Lemma storebytes_mapped_winj:
    forall f m1 b1 ofs bytes1 cp n1 m2 b2 delta bytes2,
      mem_winj f m1 m2 ->
      storebytes m1 b1 ofs bytes1 cp = Some n1 ->
      meminj_no_overlap f m1 ->
      f b1 = Some (b2, delta) ->
      list_forall2 (memval_inject f) bytes1 bytes2 ->
      exists n2,
        storebytes m2 b2 (ofs + delta) bytes2 cp = Some n2
        /\ mem_winj f n1 n2.
  Proof.
    intros. inversion H.
    assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z.of_nat (length bytes2)) Cur Writable).
    replace (ofs + delta + Z.of_nat (length bytes2))
      with ((ofs + Z.of_nat (length bytes1)) + delta).
    eapply range_perm_winj; eauto with mem.
    rewrite (list_forall2_length H3). lia.
    (* eapply storebytes_range_perm; eauto. *)
    destruct (range_perm_storebytes _ _ _ _ cp H4) as [n2 STORE].
    eapply can_access_block_winj; try eassumption. eapply storebytes_can_access_block_1; eassumption.
    exists n2; split. eauto.
    constructor.
    (* perm *)
    intros.
    eapply perm_storebytes_1; [apply STORE |].
    eapply mwi_perm0; eauto.
    eapply perm_storebytes_2; eauto.
    (* own *)
    intros.
    eapply storebytes_can_access_block_inj_1; [apply STORE |].
    eapply mwi_own0; eauto.
    eapply storebytes_can_access_block_inj_2; eauto.
    (* align *)
    intros. eapply mwi_align with (ofs := ofs0) (p := p); eauto.
    red; intros. eapply perm_storebytes_2; eauto.
  Qed.

  Lemma storebytes_unmapped_winj:
    forall f m1 b1 ofs bytes1 cp n1 m2,
      mem_winj f m1 m2 ->
      storebytes m1 b1 ofs bytes1 cp = Some n1 ->
      f b1 = None ->
      mem_winj f n1 m2.
  Proof.
    intros. inversion H.
    constructor.
    (* perm *)
    intros. eapply mwi_perm0; eauto. eapply perm_storebytes_2; eauto.
    (* own *)
    intros.
    eapply mwi_own0; try eassumption.
    eapply storebytes_can_access_block_inj_2; eassumption.
    (* align *)
    intros. eapply mwi_align with (ofs := ofs0) (p := p); eauto.
    red; intros. eapply perm_storebytes_2; eauto.
  Qed.

  Lemma storebytes_outside_winj:
    forall f m1 m2 b ofs bytes2 cp m2',
      mem_winj f m1 m2 ->
      (forall b' delta ofs',
          f b' = Some(b, delta) ->
          perm m1 b' ofs' Cur Readable ->
          ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
      storebytes m2 b ofs bytes2 cp = Some m2' ->
      mem_winj f m1 m2'.
  Proof.
    intros. inversion H. constructor.
    (* perm *)
    intros. eapply perm_storebytes_1; eauto with mem.
    (* own *)
    intros. eapply storebytes_can_access_block_inj_1; eauto.
    (* align *)
    eauto.
  Qed.

  Lemma storebytes_empty_winj:
    forall f m1 b1 ofs1 cp1 m1' m2 b2 ofs2 cp2 m2',
      mem_winj f m1 m2 ->
      storebytes m1 b1 ofs1 nil cp1 = Some m1' ->
      storebytes m2 b2 ofs2 nil cp2 = Some m2' ->
      mem_winj f m1' m2'.
  Proof.
    intros. destruct H. constructor.
    (* perm *)
    intros.
    eapply perm_storebytes_1; eauto.
    eapply mwi_perm0; eauto.
    eapply perm_storebytes_2; eauto.
    (* own *)
    intros.
    eapply storebytes_can_access_block_inj_1; eauto.
    eapply mwi_own0; eauto.
    eapply storebytes_can_access_block_inj_2; eauto.
    (* align *)
    intros. eapply mwi_align0 with (ofs := ofs) (p := p); eauto.
    red; intros. eapply perm_storebytes_2; eauto.
  Qed.

(** Preservation of allocations *)

  Lemma alloc_right_winj:
    forall f m1 m2 c lo hi b2 m2',
      mem_winj f m1 m2 ->
      alloc m2 c lo hi = (m2', b2) ->
      mem_winj f m1 m2'.
  Proof.
    intros. injection H0. intros NEXT MEM.
    inversion H. constructor.
    (* perm *)
    intros. eapply perm_alloc_1; eauto.
    (* own *)
    intros. eapply alloc_can_access_block_other_inj_1; eauto.
    (* align *)
    eauto.
  Qed.

  Remark can_access_block_component :
    forall m b cp cp', can_access_block m b (Some cp) -> can_access_block m b (Some cp') -> cp = cp'.
  Proof.
    congruence.
  Qed.

  Lemma alloc_left_unmapped_winj:
    forall f m1 m2 c lo hi m1' b1,
      mem_winj f m1 m2 ->
      alloc m1 c lo hi = (m1', b1) ->
      f b1 = None ->
      mem_winj f m1' m2.
  Proof.
    intros. inversion H. constructor.
    (* perm *)
    intros. exploit perm_alloc_inv; eauto. intros.
    destruct (eq_block b0 b1). congruence. eauto.
    (* own *)
    intros. eapply mwi_own0; try eassumption. destruct (eq_block b0 b1).
    subst b0. congruence.
    eapply alloc_can_access_block_other_inj_2; eassumption.
    (* align *)
    intros. eapply mwi_align0 with (ofs := ofs) (p := p); eauto.
    red; intros. exploit perm_alloc_inv; eauto.
    destruct (eq_block b0 b1); auto. congruence.
  Qed.

  Definition winj_offset_aligned (delta: Z) (size: Z) : Prop :=
    forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

  Lemma alloc_left_mapped_winj:
    forall f m1 m2 c lo hi m1' b1 b2 delta,
      mem_winj f m1 m2 ->
      alloc m1 c lo hi = (m1', b1) ->
      valid_block m2 b2 ->
      winj_offset_aligned delta (hi-lo) ->
      (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
      f b1 = Some(b2, delta) ->
      forall OWN : can_access_block m2 b2 (Some c),
        mem_winj f m1' m2.
  Proof.
    intros. inversion H. constructor.
    (* perm *)
    intros.
    exploit perm_alloc_inv; eauto. intros. destruct (eq_block b0 b1). subst b0.
    rewrite H4 in H5; inv H5. eauto. eauto.
    (* own *)
    intros. destruct cp as [cp |]; [| trivial]. destruct (eq_block b0 b1).
    {
      subst b0. rewrite H4 in H5. inv H5.
      apply owned_new_block in H0.
      unfold can_access_block in *. rewrite H0 in H6. inv H6.
      exact OWN.
    }
    {
      eapply mwi_own0; eauto. eapply alloc_can_access_block_other_inj_2; eassumption.
    }
    (* align *)
    intros. destruct (eq_block b0 b1).
    subst b0. assert (delta0 = delta) by congruence. subst delta0.
    assert (lo <= ofs < hi).
    { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
    assert (lo <= ofs + size_chunk chunk - 1 < hi).
    { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
    apply H2. lia.
    eapply mwi_align0 with (ofs := ofs) (p := p); eauto.
    red; intros. eapply perm_alloc_4; eauto.
  Qed.

  Lemma free_left_winj:
    forall f m1 m2 b lo hi cp m1',
      mem_winj f m1 m2 ->
      free m1 b lo hi cp = Some m1' ->
      mem_winj f m1' m2.
  Proof.
    intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
    (* perm *)
    intros. eauto with mem.
    (* own *)
    intros. eapply mwi_own0; eauto. eapply free_can_access_block_inj_2; eassumption.
    (* align *)
    intros. eapply mwi_align0 with (ofs := ofs) (p := p); eauto.
    red; intros; eapply perm_free_3; eauto.
  Qed.

  Lemma free_right_winj:
    forall f m1 m2 b lo hi cp m2',
      mem_winj f m1 m2 ->
      free m2 b lo hi cp = Some m2' ->
      (forall b' delta ofs k p,
          f b' = Some(b, delta) ->
          perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
      mem_winj f m1 m2'.
  Proof.
    intros. exploit free_result; eauto. intro FREE. inversion H.
    assert (PERM:
             forall b1 b2 delta ofs k p,
               f b1 = Some (b2, delta) ->
               perm m1 b1 ofs k p -> perm m2' b2 (ofs + delta) k p).
    intros.
    intros. eapply perm_free_1; eauto.
    destruct (eq_block b2 b); auto. subst b. right.
    assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto.
    lia.
    constructor.
    (* perm *)
    auto.
    (* own *)
    intros. eapply free_can_access_block_inj_1; eauto.
    (* align *)
    eapply mwi_align0; eauto.
  Qed.

  (** Preservation of [drop_perm] operations. *)

  Lemma drop_unmapped_winj:
    forall f m1 m2 b lo hi p cp m1',
      mem_winj f m1 m2 ->
      drop_perm m1 b lo hi p cp = Some m1' ->
      f b = None ->
      mem_winj f m1' m2.
  Proof.
    intros. inv H. constructor.
    (* perm *)
    intros. eapply mwi_perm0; eauto. eapply perm_drop_4; eauto.
    (* own *)
    intros. eapply mwi_own0; eauto. eapply can_access_block_drop_2; eauto.
    (* align *)
    intros. eapply mwi_align0 with (ofs := ofs) (p := p0); eauto.
    red; intros; eapply perm_drop_4; eauto.
  Qed.

  Lemma drop_mapped_winj:
    forall f m1 m2 b1 b2 delta lo hi p cp m1',
      mem_winj f m1 m2 ->
      drop_perm m1 b1 lo hi p cp = Some m1' ->
      meminj_no_overlap f m1 ->
      (* forall DISP : meminj_no_dispute f m1, *)
      f b1 = Some(b2, delta) ->
      exists m2',
        drop_perm m2 b2 (lo + delta) (hi + delta) p cp = Some m2'
        /\ mem_winj f m1' m2'.
  Proof.
    intros.
    assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p cp = Some m2' }).
    apply range_perm_drop_2. red; intros.
    replace ofs with ((ofs - delta) + delta) by lia.
    eapply perm_winj; eauto. eapply range_perm_drop_1; eauto. lia.
    eapply mwi_own; eauto. eapply can_access_block_drop_3; eauto.
    destruct X as [m2' DROP]. exists m2'; split; auto.
    inv H.
    constructor.
    (* perm *)
    intros.
    assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mwi_perm0; eauto. eapply perm_drop_4; eauto.
    destruct (eq_block b1 b0).
    (* b1 = b0 *)
    subst b0. rewrite H2 in H; inv H.
    destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto.
    destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto.
    assert (perm_order p p0).
    eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). lia. eauto.
    apply perm_implies with p; auto.
    eapply perm_drop_1. eauto. lia.
    (* b1 <> b0 *)
    eapply perm_drop_3; eauto.
    destruct (eq_block b3 b2); auto.
    destruct (zlt (ofs + delta0) (lo + delta)); auto.
    destruct (zle (hi + delta) (ofs + delta0)); auto.
    exploit H1; eauto.
    instantiate (1 := ofs + delta0 - delta).
    apply perm_cur_max. apply perm_implies with Freeable.
    eapply range_perm_drop_1; eauto. lia. auto with mem.
    eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.
    eauto with mem.
    intuition.
    (* own *)
    intros.
    pose proof can_access_block_drop_2 _ _ _ _ _ _ _ H0 _ _ H3 as Hown1.
    pose proof can_access_block_drop_3 _ _ _ _ _ _ _ DROP as Hown2.
    pose proof mwi_own0 _ _ _ _ H Hown1 as Hown3.
    eapply can_access_block_drop_1; eassumption.
    (* align *)
    intros. eapply mwi_align0 with (ofs := ofs) (p := p0); eauto.
    red; intros; eapply perm_drop_4; eauto.
  Qed.

  Lemma drop_outside_winj: forall f m1 m2 b lo hi p cp m2',
      mem_winj f m1 m2 ->
      drop_perm m2 b lo hi p cp = Some m2' ->
      (forall b' delta ofs' k p,
          f b' = Some(b, delta) ->
          perm m1 b' ofs' k p ->
          lo <= ofs' + delta < hi -> False) ->
      mem_winj f m1 m2'.
  Proof.
    intros. inv H. constructor.
    (* perm *)
    intros. eapply perm_drop_3; eauto.
    destruct (eq_block b2 b); auto. subst b2. right.
    destruct (zlt (ofs + delta) lo); auto.
    destruct (zle hi (ofs + delta)); auto.
    byContradiction. exploit H1; eauto. lia.
    (* own *)
    intros. eapply can_access_block_drop_1; eauto.
    (* align *)
    eapply mwi_align0; eauto.
  Qed.



  (** * Memory injections *)

  (** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
   *)

  Record winject' (f: meminj) (m1 m2: mem) : Prop :=
    mk_winject {
        mwi_inj:
        mem_winj f m1 m2;
        mi_freeblocks:
        forall b, ~(valid_block m1 b) -> f b = None;
        mwi_mappedblocks:
        forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
        mwi_no_overlap:
        meminj_no_overlap f m1;
        mwi_representable:
        forall b b' delta ofs,
          f b = Some(b', delta) ->
          perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
          delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
        mwi_perm_inv:
        forall b1 ofs b2 delta k p,
          f b1 = Some(b2, delta) ->
          perm m2 b2 (ofs + delta) k p ->
          perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
      }.
  Definition winject := winject'.

  Local Hint Resolve mwi_mappedblocks: mem.

  (** Preservation of access validity and pointer validity *)

  Theorem valid_block_winject_1:
    forall f m1 m2 b1 b2 delta,
      f b1 = Some(b2, delta) ->
      winject f m1 m2 ->
      valid_block m1 b1.
  Proof.
    intros. inv H. destruct (plt b1 (nextblock m1)). auto.
    assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
  Qed.

  Theorem valid_block_winject_2:
    forall f m1 m2 b1 b2 delta,
      f b1 = Some(b2, delta) ->
      winject f m1 m2 ->
      valid_block m2 b2.
  Proof.
    intros. eapply mwi_mappedblocks; eauto.
  Qed.

  Local Hint Resolve valid_block_winject_1 valid_block_winject_2: mem.

  Theorem perm_winject:
    forall f m1 m2 b1 b2 delta ofs k p,
      f b1 = Some(b2, delta) ->
      winject f m1 m2 ->
      perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.
  Proof.
    intros. inv H0. eapply perm_winj; eauto.
  Qed.

  Theorem perm_winject_inv:
    forall f m1 m2 b1 ofs b2 delta k p,
      winject f m1 m2 ->
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty.
  Proof.
    intros. eapply mwi_perm_inv; eauto.
  Qed.

  Theorem range_perm_winject:
    forall f m1 m2 b1 b2 delta lo hi k p,
      f b1 = Some(b2, delta) ->
      winject f m1 m2 ->
      range_perm m1 b1 lo hi k p -> range_perm m2 b2 (lo + delta) (hi + delta) k p.
  Proof.
    intros. inv H0. eapply range_perm_winj; eauto.
  Qed.

  Theorem valid_access_winject:
    forall f m1 m2 chunk b1 ofs b2 delta p cp,
      f b1 = Some(b2, delta) ->
      winject f m1 m2 ->
      valid_access m1 chunk b1 ofs p cp ->
      valid_access m2 chunk b2 (ofs + delta) p cp.
  Proof.
    intros. eapply valid_access_winj; eauto. apply mwi_inj; auto.
  Qed.

  Theorem valid_pointer_winject:
    forall f m1 m2 b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      winject f m1 m2 ->
      valid_pointer m1 b1 ofs = true ->
      valid_pointer m2 b2 (ofs + delta) = true.
  Proof.
    intros.
    pose proof valid_pointer_can_access_block _ _ _ H1 as [cp Hown].
    unfold can_access_block in Hown.
    rewrite (valid_pointer_valid_access_nonpriv _ _ _ _ Hown) in H1.
    rewrite valid_pointer_valid_access_nonpriv.
    eapply valid_access_winject; eauto.
    inv H0. inv mwi_inj0. eapply mwi_own0 with (cp := Some cp); eauto.
  Qed.

  Theorem weak_valid_pointer_winject:
    forall f m1 m2 b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      winject f m1 m2 ->
      weak_valid_pointer m1 b1 ofs = true ->
      weak_valid_pointer m2 b2 (ofs + delta) = true.
  Proof.
    intros until 2. unfold weak_valid_pointer. rewrite !orb_true_iff.
    replace (ofs + delta - 1) with ((ofs - 1) + delta) by lia.
    intros []; eauto using valid_pointer_winject.
  Qed.

  (** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

  Lemma address_winject:
    forall f m1 m2 b1 ofs1 b2 delta p,
      winject f m1 m2 ->
      perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
      f b1 = Some (b2, delta) ->
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
  Proof.
    intros.
    assert (perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem.
    exploit mwi_representable; eauto. intros [A B].
    assert (0 <= delta <= Ptrofs.max_unsigned).
    generalize (Ptrofs.unsigned_range ofs1). lia.
    unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; lia.
  Qed.

  Lemma address_winject':
    forall f m1 m2 chunk b1 ofs1 cp b2 delta,
      winject f m1 m2 ->
      valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty cp ->
      f b1 = Some (b2, delta) ->
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
  Proof.
    intros. destruct H0. eapply address_winject; eauto.
    apply H0. generalize (size_chunk_pos chunk). lia.
  Qed.

  Theorem weak_valid_pointer_winject_no_overflow:
    forall f m1 m2 b ofs b' delta,
      winject f m1 m2 ->
      weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
      f b = Some(b', delta) ->
      0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
  Proof.
    intros. rewrite weak_valid_pointer_spec in H0.
    rewrite ! valid_pointer_nonempty_perm in H0.
    exploit mwi_representable; eauto. destruct H0; eauto with mem.
    intros [A B].
    pose proof (Ptrofs.unsigned_range ofs).
    rewrite Ptrofs.unsigned_repr; lia.
  Qed.

  Theorem valid_pointer_winject_no_overflow:
    forall f m1 m2 b ofs b' delta,
      winject f m1 m2 ->
      valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
      f b = Some(b', delta) ->
      0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
  Proof.
    eauto using weak_valid_pointer_winject_no_overflow, valid_pointer_implies.
  Qed.

  Theorem valid_pointer_winject_val:
    forall f m1 m2 b ofs b' ofs',
      winject f m1 m2 ->
      valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
      Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
      valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
  Proof.
    intros. inv H1.
    pose proof valid_pointer_can_access_block _ _ _ H0 as [cp Hown].
    erewrite address_winject'; eauto.
    eapply valid_pointer_winject; eauto.
    rewrite valid_pointer_valid_access_nonpriv in H0. eauto.
    eauto.
  Qed.

  Theorem weak_valid_pointer_winject_val:
    forall f m1 m2 b ofs b' ofs',
      winject f m1 m2 ->
      weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
      Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
      weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
  Proof.
    intros. inv H1.
    exploit weak_valid_pointer_winject; eauto. intros W.
    rewrite weak_valid_pointer_spec in H0.
    rewrite ! valid_pointer_nonempty_perm in H0.
    exploit mwi_representable; eauto. destruct H0; eauto with mem.
    intros [A B].
    pose proof (Ptrofs.unsigned_range ofs).
    unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; auto; lia.
  Qed.

  Theorem winject_no_overlap:
    forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
      winject f m1 m2 ->
      b1 <> b2 ->
      f b1 = Some (b1', delta1) ->
      f b2 = Some (b2', delta2) ->
      perm m1 b1 ofs1 Max Nonempty ->
      perm m1 b2 ofs2 Max Nonempty ->
      b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
  Proof.
    intros. inv H. eapply mwi_no_overlap0; eauto.
  Qed.

  Theorem different_pointers_winject:
    forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
      winject f m m' ->
      b1 <> b2 ->
      valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
      valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
      f b1 = Some (b1', delta1) ->
      f b2 = Some (b2', delta2) ->
      b1' <> b2' \/
        Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
          Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
  Proof.
    intros.
    destruct (valid_pointer_can_access_block _ _ _ H1) as [cp1 Hown1].
    destruct (valid_pointer_can_access_block _ _ _ H2) as [cp2 Hown2].
    rewrite valid_pointer_valid_access_nonpriv in H1.
    rewrite valid_pointer_valid_access_nonpriv in H2.
    rewrite (address_winject' _ _ _ _ _ _ (Some cp1) _ _ H H1 H3).
    rewrite (address_winject' _ _ _ _ _ _ (Some cp2) _ _ H H2 H4).
    inv H1. simpl in H5. inv H2. simpl in H1.
    eapply mwi_no_overlap; eauto.
    apply perm_cur_max. apply (H5 (Ptrofs.unsigned ofs1)). lia.
    apply perm_cur_max. apply (H1 (Ptrofs.unsigned ofs2)). lia.
    congruence.
    congruence.
  Qed.

  Theorem disjoint_or_equal_winject:
    forall f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
      winject f m m' ->
      f b1 = Some(b1', delta1) ->
      f b2 = Some(b2', delta2) ->
      range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
      range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
      sz > 0 ->
      b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
      b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
      \/ ofs1 + delta1 + sz <= ofs2 + delta2
      \/ ofs2 + delta2 + sz <= ofs1 + delta1.
  Proof.
    intros.
    destruct (eq_block b1 b2).
    assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst.
    destruct H5. congruence. right. destruct H5. left; congruence. right. lia.
    destruct (eq_block b1' b2'); auto. subst. right. right.
    set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz)).
    set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz)).
    change (snd i1 <= fst i2 \/ snd i2 <= fst i1).
    apply Intv.range_disjoint'; simpl; try lia.
    unfold Intv.disjoint, Intv.In; simpl; intros. red; intros.
    exploit mwi_no_overlap; eauto.
    instantiate (1 := x - delta1). apply H2. lia.
    instantiate (1 := x - delta2). apply H3. lia.
    intuition.
  Qed.

  Theorem aligned_area_winject:
    forall f m m' b ofs al sz b' delta cp,
      winject f m m' ->
      al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
      (al | sz) ->
      range_perm m b ofs (ofs + sz) Cur Nonempty ->
      (al | ofs) ->
      f b = Some(b', delta) ->
      forall OWN : can_access_block m b cp,
        (al | ofs + delta).
  Proof.
    intros.
    assert (P: al > 0) by lia.
    assert (Q: Z.abs al <= Z.abs sz). apply Zdivide_bounds; auto. lia.
    rewrite Z.abs_eq in Q; try lia. rewrite Z.abs_eq in Q; try lia.
    assert (R: exists chunk, al = align_chunk chunk /\ al = size_chunk chunk).
    destruct H0. subst; exists Mint8unsigned; auto.
    destruct H0. subst; exists Mint16unsigned; auto.
    destruct H0. subst; exists Mint32; auto.
    subst; exists Mint64; auto.
    destruct R as [chunk [A B]].
    assert (valid_access m chunk b ofs Nonempty cp).
    split. red; intros; apply H3. lia.
    split. assumption. congruence.
    exploit valid_access_winject; eauto. intros [C [D E]].
    congruence.
  Qed.

  (** Preservation of stores *)

  Theorem store_mapped_winject:
    forall f chunk m1 b1 ofs v1 cp n1 m2 b2 delta v2,
      winject f m1 m2 ->
      store chunk m1 b1 ofs v1 cp = Some n1 ->
      f b1 = Some (b2, delta) ->
      exists n2,
        store chunk m2 b2 (ofs + delta) v2 cp = Some n2
        /\ winject f n1 n2.
  Proof.
    intros. inversion H.
    exploit store_mapped_winj; eauto. intros [n2 [STORE MI]].
    exists n2; split. eauto. constructor.
    (* winj *)
    auto.
    (* freeblocks *)
    eauto with mem.
    (* mappedblocks *)
    eauto with mem.
    (* no overlap *)
    red; intros. eauto with mem.
    (* representable *)
    intros. eapply mwi_representable; try eassumption.
    destruct H3; eauto with mem.
    (* perm inv *)
    intros. exploit mwi_perm_inv0; eauto using perm_store_2.
    intuition eauto using perm_store_1, perm_store_2.
  Qed.

  Theorem store_unmapped_winject:
    forall f chunk m1 b1 ofs v1 cp n1 m2,
      winject f m1 m2 ->
      store chunk m1 b1 ofs v1 cp = Some n1 ->
      f b1 = None ->
      winject f n1 m2.
  Proof.
    intros. inversion H.
    constructor.
    (* winj *)
    eapply store_unmapped_winj; eauto.
    (* freeblocks *)
    eauto with mem.
    (* mappedblocks *)
    eauto with mem.
    (* no overlap *)
    red; intros. eauto with mem.
    (* representable *)
    intros. eapply mwi_representable; try eassumption.
    destruct H3; eauto with mem.
    (* perm inv *)
    intros. exploit mwi_perm_inv0; eauto using perm_store_2.
    intuition eauto using perm_store_1, perm_store_2.
  Qed.

  Theorem store_outside_winject:
    forall f m1 m2 chunk b ofs v cp m2',
      winject f m1 m2 ->
      (forall b' delta ofs',
          f b' = Some(b, delta) ->
          perm m1 b' ofs' Cur Readable ->
          ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
      store chunk m2 b ofs v cp = Some m2' ->
      winject f m1 m2'.
  Proof.
    intros. inversion H. constructor.
    (* winj *)
    eapply store_outside_winj; eauto.
    (* freeblocks *)
    auto.
    (* mappedblocks *)
    eauto with mem.
    (* no overlap *)
    auto.
    (* representable *)
    eauto with mem.
    (* perm inv *)
    intros. eauto using perm_store_2.
  Qed.

  Theorem storev_mapped_winject:
    forall f chunk m1 a1 v1 cp n1 m2 a2 v2,
      winject f m1 m2 ->
      storev chunk m1 a1 v1 cp = Some n1 ->
      Val.inject f a1 a2 ->
      Val.inject f v1 v2 ->
      exists n2,
        storev chunk m2 a2 v2 cp = Some n2 /\ winject f n1 n2.
  Proof.
    intros. inv H1; simpl in H0; try discriminate.
    unfold storev.
    replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
      with (Ptrofs.unsigned ofs1 + delta).
    eapply store_mapped_winject; eauto.
    symmetry. eapply address_winject'; eauto with mem.
  Qed.

  Theorem storebytes_mapped_winject:
    forall f m1 b1 ofs bytes1 cp n1 m2 b2 delta bytes2,
      winject f m1 m2 ->
      storebytes m1 b1 ofs bytes1 cp = Some n1 ->
      f b1 = Some (b2, delta) ->
      list_forall2 (memval_inject f) bytes1 bytes2 ->
      exists n2,
        storebytes m2 b2 (ofs + delta) bytes2 cp = Some n2
        /\ winject f n1 n2.
  Proof.
    intros. inversion H.
    exploit storebytes_mapped_winj; eauto. intros [n2 [STORE MI]].
    exists n2; split. eauto. constructor.
    (* winj *)
    auto.
    (* freeblocks *)
    intros. apply mi_freeblocks0. red; intros; elim H3; eapply storebytes_valid_block_1; eauto.
    (* mappedblocks *)
    intros. eapply storebytes_valid_block_1; eauto.
    (* no overlap *)
    red; intros. eapply mwi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
    (* representable *)
    intros. eapply mwi_representable0; eauto.
    destruct H4; eauto using perm_storebytes_2.
    (* perm inv *)
    intros. exploit mwi_perm_inv0; eauto using perm_storebytes_2.
    intuition eauto using perm_storebytes_1, perm_storebytes_2.
  Qed.

  Theorem storebytes_unmapped_winject:
    forall f m1 b1 ofs bytes1 cp n1 m2,
      winject f m1 m2 ->
      storebytes m1 b1 ofs bytes1 cp = Some n1 ->
      f b1 = None ->
      winject f n1 m2.
  Proof.
    intros. inversion H.
    constructor.
    (* winj *)
    eapply storebytes_unmapped_winj; eauto.
    (* freeblocks *)
    intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
    (* mappedblocks *)
    eauto with mem.
    (* no overlap *)
    red; intros. eapply mwi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
    (* representable *)
    intros. eapply mwi_representable0; eauto.
    destruct H3; eauto using perm_storebytes_2.
    (* perm inv *)
    intros. exploit mwi_perm_inv0; eauto.
    intuition eauto using perm_storebytes_1, perm_storebytes_2.
  Qed.

  Theorem storebytes_outside_winject:
    forall f m1 m2 b ofs bytes2 cp m2',
      winject f m1 m2 ->
      (forall b' delta ofs',
          f b' = Some(b, delta) ->
          perm m1 b' ofs' Cur Readable ->
          ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
      storebytes m2 b ofs bytes2 cp = Some m2' ->
      winject f m1 m2'.
  Proof.
    intros. inversion H. constructor.
    (* winj *)
    eapply storebytes_outside_winj; eauto.
    (* freeblocks *)
    auto.
    (* mappedblocks *)
    intros. eapply storebytes_valid_block_1; eauto.
    (* no overlap *)
    auto.
    (* representable *)
    auto.
    (* perm inv *)
    intros. eapply mwi_perm_inv0; eauto using perm_storebytes_2.
  Qed.

  Theorem storebytes_empty_winject:
    forall f m1 b1 ofs1 cp1 m1' m2 b2 ofs2 cp2 m2',
      winject f m1 m2 ->
      storebytes m1 b1 ofs1 nil cp1 = Some m1' ->
      storebytes m2 b2 ofs2 nil cp2 = Some m2' ->
      winject f m1' m2'.
  Proof.
    intros. inversion H. constructor; intros.
    (* winj *)
    eapply storebytes_empty_winj; eauto.
    (* freeblocks *)
    intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
    (* mappedblocks *)
    intros. eapply storebytes_valid_block_1; eauto.
    (* no overlap *)
    red; intros. eapply mwi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
    (* representable *)
    intros. eapply mwi_representable0; eauto.
    destruct H3; eauto using perm_storebytes_2.
    (* perm inv *)
    intros. exploit mwi_perm_inv0; eauto using perm_storebytes_2.
    intuition eauto using perm_storebytes_1, perm_storebytes_2.
  Qed.

  (* Preservation of allocations *)

  Theorem alloc_right_winject:
    forall f m1 m2 c lo hi b2 m2',
      winject f m1 m2 ->
      alloc m2 c lo hi = (m2', b2) ->
      winject f m1 m2'.
  Proof.
    intros. injection H0. intros NEXT MEM.
    inversion H. constructor.
    (* winj *)
    eapply alloc_right_winj; eauto.
    (* freeblocks *)
    auto.
    (* mappedblocks *)
    eauto with mem.
    (* no overlap *)
    auto.
    (* representable *)
    auto.
    (* perm inv *)
    intros. eapply perm_alloc_inv in H2; eauto. destruct (eq_block b0 b2).
    subst b0. eelim fresh_block_alloc; eauto.
    eapply mwi_perm_inv0; eauto.
  Qed.

  Theorem alloc_left_unmapped_winject:
    forall f m1 m2 c lo hi m1' b1,
      winject f m1 m2 ->
      alloc m1 c lo hi = (m1', b1) ->
      exists f',
        winject f' m1' m2
        /\ inject_incr f f'
        /\ f' b1 = None
        /\ (forall b, b <> b1 -> f' b = f b).
  Proof.
    intros. inversion H.
    set (f' := fun b => if eq_block b b1 then None else f b).
    assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
    assert (mem_winj f' m1 m2).
    inversion mwi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    eapply mwi_align0; eauto.
    exists f'; split. constructor.
    (* winj *)
    eapply alloc_left_unmapped_winj; eauto. unfold f'; apply dec_eq_true.
    (* freeblocks *)
    intros. unfold f'. destruct (eq_block b b1). auto.
    apply mi_freeblocks0. red; intro; elim H3. eauto with mem.
    (* mappedblocks *)
    unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
    (* no overlap *)
    unfold f'; red; intros.
    destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
    eapply mwi_no_overlap0. eexact H3. eauto. eauto.
    exploit perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
    exploit perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto.
    (* representable *)
    unfold f'; intros.
    destruct (eq_block b b1); try discriminate.
    eapply mwi_representable0; try eassumption.
    destruct H4; eauto using perm_alloc_4.
    (* perm inv *)
    intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate.
    exploit mwi_perm_inv0; eauto.
    intuition eauto using perm_alloc_1, perm_alloc_4.
    (* incr *)
    split. auto.
    (* image *)
    split. unfold f'; apply dec_eq_true.
    (* incr *)
    intros; unfold f'; apply dec_eq_false; auto.
  Qed.

  Theorem alloc_left_mapped_winject:
    forall f m1 m2 c lo hi m1' b1 b2 delta,
      winject f m1 m2 ->
      alloc m1 c lo hi = (m1', b1) ->
      valid_block m2 b2 ->
      forall OWN : can_access_block m2 b2 (Some c),
        0 <= delta <= Ptrofs.max_unsigned ->
        (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
        (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
        winj_offset_aligned delta (hi-lo) ->
        (forall b delta' ofs k p,
            f b = Some (b2, delta') ->
            perm m1 b ofs k p ->
            lo + delta <= ofs + delta' < hi + delta -> False) ->
        exists f',
          winject f' m1' m2
          /\ inject_incr f f'
          /\ f' b1 = Some(b2, delta)
          /\ (forall b, b <> b1 -> f' b = f b).
  Proof.
    intros. inversion H.
    set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
    assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
    assert (mem_winj f' m1 m2).
    inversion mwi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
    inversion H8. subst b0 b3 delta0.
    elim (fresh_block_alloc _ _ _ _ _ _ H0). eauto with mem.
    eauto.
    unfold f'; intros. destruct cp as [cp |]; [| trivial]. destruct (eq_block b0 b1).
    inversion H8. subst b0 b3 delta0.
    apply unowned_fresh_block with (c' := cp) in H0. contradiction.
    eapply mwi_own0; eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
    inversion H8. subst b0 b3 delta0.
    elim (fresh_block_alloc _ _ _ _ _ _ H0).
    eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); lia.
    eauto.
    exists f'. split. constructor.
    (* winj *)
    eapply alloc_left_mapped_winj; eauto. unfold f'; apply dec_eq_true.
    (* freeblocks *)
    unfold f'; intros. destruct (eq_block b b1). subst b.
    elim H9. eauto with mem.
    eauto with mem.
    (* mappedblocks *)
    unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
    (* overlap *)
    unfold f'; red; intros.
    exploit perm_alloc_inv. eauto. eexact H12. intros P1.
    exploit perm_alloc_inv. eauto. eexact H13. intros P2.
    destruct (eq_block b0 b1); destruct (eq_block b3 b1).
    congruence.
    inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. lia.
    inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. lia.
    eauto.
    (* representable *)
    unfold f'; intros.
    destruct (eq_block b b1).
    subst. injection H9; intros; subst b' delta0. destruct H10.
    exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
    generalize (Ptrofs.unsigned_range_2 ofs). lia.
    exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
    generalize (Ptrofs.unsigned_range_2 ofs). lia.
    eapply mwi_representable0; try eassumption.
    destruct H10; eauto using perm_alloc_4.
    (* perm inv *)
    intros. unfold f' in H9; destruct (eq_block b0 b1).
    inversion H9; clear H9; subst b0 b3 delta0.
    assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by lia.
    destruct EITHER.
    left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
    right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
    exploit mwi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4.
    (* incr *)
    split. auto.
    (* image of b1 *)
    split. unfold f'; apply dec_eq_true.
    (* image of others *)
    intros. unfold f'; apply dec_eq_false; auto.
  Qed.

  Theorem alloc_parallel_winject:
    forall f m1 m2 c lo1 hi1 m1' b1 lo2 hi2,
      winject f m1 m2 ->
      alloc m1 c lo1 hi1 = (m1', b1) ->
      lo2 <= lo1 -> hi1 <= hi2 ->
      exists f', exists m2', exists b2,
        alloc m2 c lo2 hi2 = (m2', b2)
        /\ winject f' m1' m2'
        /\ inject_incr f f'
        /\ f' b1 = Some(b2, 0)
        /\ (forall b, b <> b1 -> f' b = f b).
  Proof.
    intros.
    case_eq (alloc m2 c lo2 hi2). intros m2' b2 ALLOC.
    exploit alloc_left_mapped_winject.
    eapply alloc_right_winject; eauto.
    eauto.
    instantiate (1 := b2). eauto with mem.
    eapply owned_new_block; eauto.
    instantiate (1 := 0). unfold Ptrofs.max_unsigned. generalize Ptrofs.modulus_pos; lia.
    auto.
    intros. apply perm_implies with Freeable; auto with mem.
    eapply perm_alloc_2; eauto. lia.
    red; intros. apply Z.divide_0_r.
    intros. apply (valid_not_valid_diff m2 b2 b2); eauto with mem.
    intros [f' [A [B [C D]]]].
    exists f'; exists m2'; exists b2; auto.
  Qed.

  (** Preservation of [free] operations *)

  Lemma free_left_winject:
    forall f m1 m2 b lo hi cp m1',
      winject f m1 m2 ->
      free m1 b lo hi cp = Some m1' ->
      winject f m1' m2.
  Proof.
    intros. inversion H. constructor.
    (* winj *)
    eapply free_left_winj; eauto.
    (* freeblocks *)
    eauto with mem.
    (* mappedblocks *)
    auto.
    (* no overlap *)
    red; intros. eauto with mem.
    (* representable *)
    intros. eapply mwi_representable0; try eassumption.
    destruct H2; eauto with mem.
    (* perm inv *)
    intros. exploit mwi_perm_inv0; eauto. intuition eauto using perm_free_3.
    eapply perm_free_inv in H4; eauto. destruct H4 as [[A B] | A]; auto.
    subst b1. right; eapply perm_free_2; eauto.
  Qed.

  Lemma free_list_left_winject:
    forall f m2 l cp m1 m1',
      winject f m1 m2 ->
      free_list m1 l cp = Some m1' ->
      winject f m1' m2.
  Proof.
    induction l; simpl; intros.
    inv H0. auto.
    destruct a as [[b lo] hi].
    destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
    apply IHl with cp m11; auto. eapply free_left_winject; eauto.
  Qed.

  Lemma free_right_winject:
    forall f m1 m2 b lo hi cp m2',
      winject f m1 m2 ->
      free m2 b lo hi cp = Some m2' ->
      (forall b1 delta ofs k p,
          f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
          lo <= ofs + delta < hi -> False) ->
      winject f m1 m2'.
  Proof.
    intros. inversion H. constructor.
    (* winj *)
    eapply free_right_winj; eauto.
    (* freeblocks *)
    auto.
    (* mappedblocks *)
    eauto with mem.
    (* no overlap *)
    auto.
    (* representable *)
    auto.
    (* perm inv *)
    intros. eauto using perm_free_3.
  Qed.

  Lemma perm_free_list:
    forall l m cp m' b ofs k p,
      free_list m l cp = Some m' ->
      perm m' b ofs k p ->
      perm m b ofs k p /\
        (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
  Proof.
    induction l; simpl; intros.
    inv H. auto.
    destruct a as [[b1 lo1] hi1].
    destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
    exploit IHl; eauto. intros [A B].
    split. eauto with mem.
    intros. destruct H1. inv H1.
    elim (perm_free_2 _ _ _ _ _ _ E ofs k p). auto. auto.
    eauto.
  Qed.

  Theorem free_winject:
    forall f m1 l cp1 m1' m2 b lo hi cp2 m2',
      winject f m1 m2 ->
      free_list m1 l cp1 = Some m1' ->
      free m2 b lo hi cp2 = Some m2' ->
      (forall b1 delta ofs k p,
          f b1 = Some(b, delta) ->
          perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
          exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
      winject f m1' m2'.
  Proof.
    intros.
    eapply free_right_winject; eauto.
    eapply free_list_left_winject; eauto.
    intros. exploit perm_free_list; eauto. intros [A B].
    exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
  Qed.

  Theorem free_parallel_winject:
    forall f m1 m2 b lo hi cp m1' b' delta,
      winject f m1 m2 ->
      free m1 b lo hi cp = Some m1' ->
      f b = Some(b', delta) ->
      exists m2',
        free m2 b' (lo + delta) (hi + delta) cp = Some m2'
        /\ winject f m1' m2'.
  Proof.
    intros.
    destruct (range_perm_free m2 b' (lo + delta) (hi + delta) cp) as [m2' FREE].
    eapply range_perm_winject; eauto. eapply free_range_perm; eauto.
    inv H. inv mwi_inj0. eapply mwi_own0; eauto. eapply free_can_access_block_1; eauto.
    exists m2'; split; auto.
    eapply free_winject with (m1 := m1) (l := (b,lo,hi)::nil); eauto.
    simpl; rewrite H0; auto.
    intros. destruct (eq_block b1 b).
    subst b1. rewrite H1 in H2; inv H2.
    exists lo, hi; split; auto with coqlib. lia.
    exploit mwi_no_overlap. eexact H. eexact n. eauto. eauto.
    eapply perm_max. eapply perm_implies. eauto. auto with mem.
    instantiate (1 := ofs + delta0 - delta).
    apply perm_cur_max. apply perm_implies with Freeable; auto with mem.
    eapply free_range_perm; eauto. lia.
    intros [A|A]. congruence. lia.
  Qed.

  Lemma drop_outside_winject: forall f m1 m2 b lo hi p cp m2',
      winject f m1 m2 ->
      drop_perm m2 b lo hi p cp = Some m2' ->
      (forall b' delta ofs k p,
          f b' = Some(b, delta) ->
          perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
      winject f m1 m2'.
  Proof.
    intros. destruct H. constructor; eauto.
    eapply drop_outside_winj; eauto.
    intros. unfold valid_block in *. erewrite nextblock_drop; eauto.
    intros. eapply mwi_perm_inv0; eauto using perm_drop_4.
  Qed.

  (** Composing two memory winjections. *)

  Lemma mem_winj_compose:
    forall f f' m1 m2 m3,
      mem_winj f m1 m2 -> mem_winj f' m2 m3 -> mem_winj (compose_meminj f f') m1 m3.
  Proof.
    intros. unfold compose_meminj. inv H; inv H0; constructor; intros.
    (* perm *)
    destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
    destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
    replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by lia.
    eauto.
    (* own *)
    destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
    destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
    eapply mwi_own1; eauto.
    (* align *)
    destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
    destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
    apply Z.divide_add_r.
    eapply mwi_align0; eauto.
    eapply mwi_align1 with (ofs := ofs + delta') (p := p); eauto.
    red; intros. replace ofs0 with ((ofs0 - delta') + delta') by lia.
    eapply mwi_perm0; eauto. apply H0. lia.
  Qed.

  Theorem winject_compose:
    forall f f' m1 m2 m3,
      winject f m1 m2 -> winject f' m2 m3 ->
      winject (compose_meminj f f') m1 m3.
  Proof.
    unfold compose_meminj; intros.
    inv H; inv H0. constructor.
    (* winj *)
    eapply mem_winj_compose; eauto.
    (* unmapped *)
    intros. erewrite mi_freeblocks0; eauto.
    (* mapped *)
    intros.
    destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
    destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
    eauto.
    (* no overlap *)
    red; intros.
    destruct (f b1) as [[b1x delta1x] |] eqn:?; try discriminate.
    destruct (f' b1x) as [[b1y delta1y] |] eqn:?; inv H0.
    destruct (f b2) as [[b2x delta2x] |] eqn:?; try discriminate.
    destruct (f' b2x) as [[b2y delta2y] |] eqn:?; inv H1.
    exploit mwi_no_overlap0; eauto. intros A.
    destruct (eq_block b1x b2x).
    subst b1x. destruct A. congruence.
    assert (delta1y = delta2y) by congruence. right; lia.
    exploit mwi_no_overlap1. eauto. eauto. eauto.
    eapply perm_winj. eauto. eexact H2. eauto.
    eapply perm_winj. eauto. eexact H3. eauto.
    intuition lia.
    (* representable *)
    intros.
    destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
    destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
    exploit mwi_representable0; eauto. intros [A B].
    set (ofs' := Ptrofs.repr (Ptrofs.unsigned ofs + delta1)).
    assert (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs + delta1).
    unfold ofs'; apply Ptrofs.unsigned_repr. auto.
    exploit mwi_representable1. eauto. instantiate (1 := ofs').
    rewrite H.
    replace (Ptrofs.unsigned ofs + delta1 - 1) with
      ((Ptrofs.unsigned ofs - 1) + delta1) by lia.
    destruct H0; eauto using perm_winj.
    rewrite H. lia.
    (* perm inv *)
    intros.
    destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
    destruct (f' b') as [[b'' delta''] |] eqn:?; try discriminate.
    inversion H; clear H; subst b'' delta.
    replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') in H0 by lia.
    exploit mwi_perm_inv1; eauto. intros [A|A].
    eapply mwi_perm_inv0; eauto.
    right; red; intros. elim A. eapply perm_winj; eauto.
  Qed.

  (* Lemma val_lessdef_winject_compose: *)
  (*   forall f v1 v2 v3, *)
  (*     Val.lessdef v1 v2 -> Val.inject f v2 v3 -> Val.inject f v1 v3. *)
  (* Proof. *)
  (*   intros. inv H. auto. auto. *)
  (* Qed. *)

  (* Lemma val_inject_lessdef_compose: *)
  (*   forall f v1 v2 v3, *)
  (*     Val.inject f v1 v2 -> Val.lessdef v2 v3 -> Val.inject f v1 v3. *)
  (* Proof. *)
  (*   intros. inv H0. auto. inv H. auto. *)
  (* Qed. *)

  (** Winjecting a memory into itself. *)

  Definition flat_winj (thr: block) : meminj :=
    fun (b: block) => if plt b thr then Some(b, 0) else None.

  Definition winject_neutral (thr: block) (m: mem) :=
    mem_winj (flat_winj thr) m m.

  Remark flat_winj_no_overlap:
    forall thr m, meminj_no_overlap (flat_winj thr) m.
  Proof.
    unfold flat_winj; intros; red; intros.
    destruct (plt b1 thr); inversion H0; subst.
    destruct (plt b2 thr); inversion H1; subst.
    auto.
  Qed.

  Theorem neutral_winject:
    forall m, winject_neutral (nextblock m) m -> winject (flat_winj (nextblock m)) m m.
  Proof.
    intros. constructor.
    (* meminj *)
    auto.
    (* freeblocks *)
    unfold flat_winj, valid_block; intros.
    apply pred_dec_false. auto.
    (* mappedblocks *)
    unfold flat_winj, valid_block; intros.
    destruct (plt b (nextblock m)); inversion H0; subst. auto.
    (* no overlap *)
    apply flat_winj_no_overlap.
    (* range *)
    unfold flat_winj; intros.
    destruct (plt b (nextblock m)); inv H0. generalize (Ptrofs.unsigned_range_2 ofs); lia.
    (* perm inv *)
    unfold flat_winj; intros.
    destruct (plt b1 (nextblock m)); inv H0.
    rewrite Z.add_0_r in H1; auto.
  Qed.

  Theorem empty_winject_neutral:
    forall thr, winject_neutral thr empty.
  Proof.
    intros; red; constructor.
    (* perm *)
    unfold flat_winj; intros. destruct (plt b1 thr); inv H.
    replace (ofs + 0) with ofs by lia; auto.
    (* own *)
    intros. destruct cp as [cp| ]; [| trivial].
    unfold can_access_block, block_compartment in H0.
    now rewrite PTree.gempty in H0.
    (* align *)
    unfold flat_winj; intros. destruct (plt b1 thr); inv H. apply Z.divide_0_r.
  Qed.

  Theorem alloc_winject_neutral:
    forall thr m c lo hi b m',
      alloc m c lo hi = (m', b) ->
      winject_neutral thr m ->
      Plt (nextblock m) thr ->
      winject_neutral thr m'.
  Proof.
    intros; red.
    eapply alloc_left_mapped_winj with (m1 := m) (b2 := b) (delta := 0).
    eapply alloc_right_winj; eauto. eauto. eauto with mem.
    red. intros. apply Z.divide_0_r.
    intros.
    apply perm_implies with Freeable; auto with mem.
    eapply perm_alloc_2; eauto. lia.
    unfold flat_winj. apply pred_dec_true.
    rewrite (alloc_result _ _ _ _ _ _ H). auto.
    eapply owned_new_block; eauto.
  Qed.

  (* Theorem store_winject_neutral: *)
  (*   forall chunk m b ofs v cp m' thr, *)
  (*     store chunk m b ofs v cp = Some m' -> *)
  (*     winject_neutral thr m -> *)
  (*     Plt b thr -> *)
  (*     Val.inject (flat_winj thr) v v -> *)
  (*     winject_neutral thr m'. *)
  (* Proof. *)
  (*   intros; red. *)
  (*   exploit store_mapped_winj. eauto. eauto. apply flat_winj_no_overlap. *)
  (*   unfold flat_winj. apply pred_dec_true; auto. eauto. *)
  (*   replace (ofs + 0) with ofs by lia. *)
  (*   intros [m'' [A B]]. congruence. *)
  (* Qed. *)

  Theorem drop_winject_neutral:
    forall m b lo hi p cp m' thr,
      drop_perm m b lo hi p cp = Some m' ->
      winject_neutral thr m ->
      Plt b thr ->
      winject_neutral thr m'.
  Proof.
    unfold winject_neutral; intros.
    exploit drop_mapped_winj; eauto. apply flat_winj_no_overlap.
    unfold flat_winj. apply pred_dec_true; eauto.
    repeat rewrite Z.add_0_r. intros [m'' [A B]]. congruence.
  Qed.

End WINJ.

Section PROPS.

  Lemma mem_winj_inj_incr
        j1 j2 m m'
        (INCR: inject_incr j1 j2)
        (WINJ: mem_winj j2 m m')
    :
    mem_winj j1 m m'.
  Proof. inv WINJ. split; eauto. Qed.

  Lemma winject_inj_incr
        j1 j2 m m'
        (INCR: inject_incr j1 j2)
        (WINJ: winject j2 m m')
    :
    winject j1 m m'.
  Proof.
    inv WINJ. split; eauto. eapply mem_winj_inj_incr; eauto.
    { intros. destruct (j1 b) as [[b' ofs']|] eqn: JB; auto. specialize (INCR _ _ _ JB). specialize (mi_freeblocks0 _ H). rewrite INCR in mi_freeblocks0. congruence. }
    { unfold meminj_no_overlap in *. intros. eapply mwi_no_overlap0; eauto. }
  Qed.

  Lemma mem_inj_implies_mem_winj
        j m m'
        (INJ: Mem.mem_inj j m m')
    :
    mem_winj j m m'.
  Proof. inv INJ. split; auto. Qed.

  Lemma inject_implies_winject
        j m m'
        (INJ: Mem.inject j m m')
    :
    winject j m m'.
  Proof. inv INJ. split; auto. apply mem_inj_implies_mem_winj; auto. Qed.

  Definition mem_inj_val f m1 m2 :=
    forall (b1 : block) (ofs : Z) (b2 : block) (delta : Z),
      f b1 = Some (b2, delta) -> Mem.perm m1 b1 ofs Cur Readable -> memval_inject f (ZMap.get ofs (Mem.mem_contents m1) # b1) (ZMap.get (ofs + delta) (Mem.mem_contents m2) # b2).

  Lemma mem_winj_to_mem_inj
        j m m'
        (WINJ: mem_winj j m m')
        (INJV: mem_inj_val j m m')
    :
    Mem.mem_inj j m m'.
  Proof. inv WINJ. split; eauto. Qed.

  Lemma winject_to_inject
        j m m'
        (WINJ: winject j m m')
        (INJV: mem_inj_val j m m')
    :
    Mem.inject j m m'.
  Proof. inv WINJ. split; eauto. apply mem_winj_to_mem_inj; auto. Qed.

End PROPS.
