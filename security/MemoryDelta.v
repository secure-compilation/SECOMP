Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.
Require Import MemoryWeak.



Section AUX.

  Lemma alloc_left_unmapped_winject_keep:
    forall f m1 m2 c lo hi m1' b1,
      winject f m1 m2 ->
      Mem.alloc m1 c lo hi = (m1', b1) ->
      winject f m1' m2.
  Proof.
    intros. set (f' := fun b => if eq_block b b1 then None else f b).
    cut (winject f' m1' m2 /\ inject_incr f f' /\ f' b1 = None /\ (forall b, b <> b1 -> f' b = f b)).
    { clear - f'. intros (INJ & INCR & _ & _). unfold inject_incr in INCR.
      assert (f' = f).
      { eapply Axioms.functional_extensionality. intros x. destruct (eq_block x b1).
        - subst x. destruct (f b1) eqn:FB.
          + destruct p. specialize (INCR _ _ _ FB). auto.
          + subst f'. simpl. rewrite pred_dec_true; auto.
        - subst f'. simpl. rewrite pred_dec_false; auto.
      }
      rewrite <- H. apply INJ.
    }
    inversion H. assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
    assert (mem_winj f' m1 m2).
    inversion mwi_inj; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    eapply mwi_align; eauto.
    split. constructor.
    (* inj *)
    eapply alloc_left_unmapped_winj; eauto. unfold f'; apply dec_eq_true.
    (* freeblocks *)
    intros. unfold f'. destruct (eq_block b b1). auto.
    apply mi_freeblocks. red; intro; elim H3. eauto with mem.
    (* mappedblocks *)
    unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
    (* no overlap *)
    unfold f'; red; intros.
    destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
    eapply mwi_no_overlap. eexact H3. eauto. eauto.
    exploit Mem.perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
    exploit Mem.perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto.
    (* representable *)
    unfold f'; intros.
    destruct (eq_block b b1); try discriminate.
    eapply mwi_representable; try eassumption.
    destruct H4; eauto using Mem.perm_alloc_4.
    (* perm inv *)
    intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate.
    exploit mwi_perm_inv; eauto.
    intuition eauto using Mem.perm_alloc_1, Mem.perm_alloc_4.
    (* incr *)
    split. auto.
    (* image *)
    split. unfold f'; apply dec_eq_true.
    (* incr *)
    intros; unfold f'; apply dec_eq_false; auto.
  Qed.

  Lemma alloc_left_unmapped_inject_keep:
    forall f m1 m2 c lo hi m1' b1,
      Mem.inject f m1 m2 ->
      Mem.alloc m1 c lo hi = (m1', b1) ->
      Mem.inject f m1' m2.
  Proof.
    intros. set (f' := fun b => if eq_block b b1 then None else f b).
    cut (Mem.inject f' m1' m2 /\ inject_incr f f' /\ f' b1 = None /\ (forall b, b <> b1 -> f' b = f b)).
    { clear - f'. intros (INJ & INCR & _ & _). unfold inject_incr in INCR.
      assert (f' = f).
      { eapply Axioms.functional_extensionality. intros x. destruct (eq_block x b1).
        - subst x. destruct (f b1) eqn:FB.
          + destruct p. specialize (INCR _ _ _ FB). auto.
          + subst f'. simpl. rewrite pred_dec_true; auto.
        - subst f'. simpl. rewrite pred_dec_false; auto.
      }
      rewrite <- H. apply INJ.
    }
    inversion H. assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
    assert (Mem.mem_inj f' m1 m2).
    inversion mi_inj; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    eapply mi_align; eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    apply memval_inject_incr with f; auto.
    split. constructor.
    (* inj *)
    eapply Mem.alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true.
    (* freeblocks *)
    intros. unfold f'. destruct (eq_block b b1). auto.
    apply mi_freeblocks. red; intro; elim H3. eauto with mem.
    (* mappedblocks *)
    unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
    (* no overlap *)
    unfold f'; red; intros.
    destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
    eapply mi_no_overlap. eexact H3. eauto. eauto.
    exploit Mem.perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
    exploit Mem.perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto.
    (* representable *)
    unfold f'; intros.
    destruct (eq_block b b1); try discriminate.
    eapply mi_representable; try eassumption.
    destruct H4; eauto using Mem.perm_alloc_4.
    (* perm inv *)
    intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate.
    exploit mi_perm_inv; eauto.
    intuition eauto using Mem.perm_alloc_1, Mem.perm_alloc_4.
    (* incr *)
    split. auto.
    (* image *)
    split. unfold f'; apply dec_eq_true.
    (* incr *)
    intros; unfold f'; apply dec_eq_false; auto.
  Qed.

End AUX.


Section PUBINJ.

  (* Memory injection for public global symbols: visible for external calls *)
  Definition meminj_public (ge: Senv.t): meminj :=
    fun b => match Senv.invert_symbol ge b with
          | Some id => if Senv.public_symbol ge id then Some (b, 0%Z) else None
          | None => None
          end.

  Definition meminj_strict (j: meminj) := forall b1 b2 b' ofsd1 ofsd2, j b1 = Some (b', ofsd1) -> j b2 = Some (b', ofsd2) -> b1 = b2.

  Lemma meminj_public_strict ge: meminj_strict (meminj_public ge).
  Proof.
    unfold meminj_strict. intros. unfold meminj_public in *; simpl in *.
    destruct (Senv.invert_symbol ge b1) eqn:INV1. 2: congruence. destruct (Senv.public_symbol ge i) eqn:PUB1. 2: congruence. inv H.
    destruct (Senv.invert_symbol ge b2) eqn:INV2. 2: congruence. destruct (Senv.public_symbol ge i0) eqn:PUB2. 2: congruence. inv H0.
    auto.
  Qed.

End PUBINJ.

Section MEMDELTA.

  (** Memory delta data and apply *)

  (* Data to get injection by invoking correct Mem.store: inj + (apply delta) = inj *)
  Definition mem_delta_store := (memory_chunk * block * Z * val * compartment)%type.
  Definition mem_delta_bytes := (block * Z * (list memval) * compartment)%type.
  Definition mem_delta_alloc := (compartment * Z * Z)%type.
  Definition mem_delta_free := (block * Z * Z * compartment)%type.

  Inductive mem_delta_kind :=
  | mem_delta_kind_store (d: mem_delta_store)
  | mem_delta_kind_bytes (d: mem_delta_bytes)
  | mem_delta_kind_alloc (d: mem_delta_alloc)
  | mem_delta_kind_free (d: mem_delta_free)
  .

  (* old to new *)
  Definition mem_delta := list mem_delta_kind.

  Definition mem_delta_apply_store (om: option mem) (d: mem_delta_store): option mem :=
    let '(ch, b, ofs, v, cp) := d in
    match om with
    | Some m => Mem.store ch m b ofs v cp
    | None => None
    end.

  Lemma mem_delta_apply_store_none
        d
    :
    mem_delta_apply_store None d = None.
  Proof. unfold mem_delta_apply_store. destruct d as [[[[d0 d1] d2] d3] d4]. auto. Qed.

  Definition mem_delta_apply_bytes (om: option mem) (d: mem_delta_bytes): option mem :=
    let '(b, ofs, mvs, cp) := d in
    match om with
    | Some m => Mem.storebytes m b ofs mvs cp
    | None => None
    end.

  Lemma mem_delta_apply_bytes_none
        d
    :
    mem_delta_apply_bytes None d = None.
  Proof. unfold mem_delta_apply_bytes. destruct d as [[[d0 d1] d2] d3]. auto. Qed.

  Definition mem_delta_apply_alloc (om: option mem) (d: mem_delta_alloc): option mem :=
    let '(cp, lo, hi) := d in
    match om with
    | Some m => Some (fst (Mem.alloc m cp lo hi))
    | None => None
    end.

  Lemma mem_delta_apply_alloc_none
        d
    :
    mem_delta_apply_alloc None d = None.
  Proof. unfold mem_delta_apply_alloc. destruct d as [[d0 d1] d2]. auto. Qed.

  Definition mem_delta_apply_free (om: option mem) (d: mem_delta_free): option mem :=
    let '(b, lo, hi, cp) := d in
    match om with
    | Some m => Mem.free m b lo hi cp
    | None => None
    end.

  Lemma mem_delta_apply_free_none
        d
    :
    mem_delta_apply_free None d = None.
  Proof. unfold mem_delta_apply_free. destruct d as [[[d0 d1] d2] d3]. auto. Qed.


  Definition mem_delta_apply (d: mem_delta) (om0: option mem) : option mem :=
    fold_left (fun om data =>
                 match data with
                 | mem_delta_kind_store d => mem_delta_apply_store om d
                 | mem_delta_kind_bytes d => mem_delta_apply_bytes om d
                 | mem_delta_kind_alloc d => mem_delta_apply_alloc om d
                 | mem_delta_kind_free d => mem_delta_apply_free om d
                 end
              ) d om0.

  Lemma mem_delta_apply_cons
        d m0 k
    :
    mem_delta_apply (k :: d) m0 =
      match k with
      | mem_delta_kind_store dd => mem_delta_apply d (mem_delta_apply_store (m0) dd)
      | mem_delta_kind_bytes dd => mem_delta_apply d (mem_delta_apply_bytes (m0) dd)
      | mem_delta_kind_alloc dd => mem_delta_apply d (mem_delta_apply_alloc (m0) dd)
      | mem_delta_kind_free dd => mem_delta_apply d (mem_delta_apply_free (m0) dd)
      end.
  Proof. simpl. destruct k; auto. Qed.

  Lemma mem_delta_apply_app
        d0 d1 m0
    :
    mem_delta_apply (d0 ++ d1) m0 = mem_delta_apply d1 (mem_delta_apply d0 m0).
  Proof.
    revert d1 m0. induction d0; intros.
    { simpl. auto. }
    rewrite <- app_comm_cons. rewrite ! mem_delta_apply_cons. destruct a; auto.
  Qed.

  Lemma mem_delta_apply_none
        d
    :
    mem_delta_apply d None = None.
  Proof.
    induction d; auto. rewrite mem_delta_apply_cons.
    destruct a; [rewrite mem_delta_apply_store_none | rewrite mem_delta_apply_bytes_none | rewrite mem_delta_apply_alloc_none | rewrite mem_delta_apply_free_none]; rewrite IHd; auto.
  Qed.

  Lemma mem_delta_apply_some
        d om m'
        (APPD: mem_delta_apply d om = Some m')
    :
    exists m, om = Some m.
  Proof. destruct om; eauto. rewrite mem_delta_apply_none in APPD. inv APPD. Qed.    


  Definition mem_delta_apply_inj (j: meminj) (d: mem_delta) (om0: option mem) : option mem :=
    fold_left (fun om data =>
                 match data with
                 | mem_delta_kind_store (ch, b, ofs, v, cp) =>
                     match j b with
                     | Some (b', ofsd) =>
                         mem_delta_apply_store om (ch, b', (ofs + ofsd)%Z, v, cp)
                     | None => om
                     end
                 | _ => om
                 end) d (om0).

  Lemma mem_delta_apply_inj_cons
        j d m0 k
    :
    mem_delta_apply_inj j (k :: d) m0 =
      match k with
      | mem_delta_kind_store (ch, b, ofs, v, cp) =>
          match j b with
          | Some (b', ofsd) =>
              mem_delta_apply_inj j d (mem_delta_apply_store m0 (ch, b', (ofs + ofsd)%Z, v, cp))
          | None => mem_delta_apply_inj j d m0
          end
      | mem_delta_kind_bytes dd
      | mem_delta_kind_alloc dd
      | mem_delta_kind_free dd => mem_delta_apply_inj j d m0
      end.
  Proof. simpl. destruct k; auto. destruct d0 as [[[[a0 a1] a2] a3] a4]. destruct (j a1); auto. destruct p. auto. Qed.

  Lemma mem_delta_apply_inj_app
        j d0 d1 m0
    :
    mem_delta_apply_inj j (d0 ++ d1) m0 = mem_delta_apply_inj j d1 (mem_delta_apply_inj j d0 m0).
  Proof.
    revert j d1 m0. induction d0; intros.
    { simpl. auto. }
    rewrite <- app_comm_cons. rewrite ! mem_delta_apply_inj_cons. destruct a; auto.
    { destruct d as [[[[a0 a1] a2] a3] a4]. destruct (j a1); auto. destruct p; auto. }
  Qed.

  Lemma mem_delta_apply_inj_none
        j d
    :
    mem_delta_apply_inj j d None = None.
  Proof.
    induction d; auto. rewrite mem_delta_apply_inj_cons.
    destruct a. destruct d0 as [[[[a0 a1] a2] a3] a4]. destruct (j a1). destruct p. rewrite mem_delta_apply_store_none. all: rewrite IHd; auto.
  Qed.

  Lemma mem_delta_apply_inj_some
        j d om m'
        (APPD: mem_delta_apply_inj j d om = Some m')
    :
    exists m, om = Some m.
  Proof. destruct om; eauto. rewrite mem_delta_apply_inj_none in APPD. inv APPD. Qed.    


  (** Delta and injection relations *)

  Definition mem_delta_kind_inj_wf (j: meminj): mem_delta_kind -> Prop :=
    fun data =>
      match data with
      | mem_delta_kind_bytes (b, ofs, mvs, cp) => (j b) = None
      | mem_delta_kind_free (b, lo, hi, cp) => (j b) = None
      | _ => True
      end.

  Definition mem_delta_inj_wf (j: meminj): mem_delta -> Prop :=
    fun d => Forall (fun data => mem_delta_kind_inj_wf j data) d.

  Lemma mem_delta_inj_wf_rev
        j d
    :
    mem_delta_inj_wf j d <-> mem_delta_inj_wf j (rev d).
  Proof.
    unfold mem_delta_inj_wf. split; intros. apply Forall_rev; auto. rewrite <- rev_involutive. apply Forall_rev. auto.
  Qed.

  Definition meminj_first_order (j: meminj) (m: mem) :=
    forall b ofs, (j b <> None) -> (Mem.perm m b ofs Cur Readable) -> loc_first_order m b ofs.

  Definition meminj_not_alloc (j: meminj) (m: mem) := forall b, (Mem.nextblock m <= b)%positive -> j b = None.


  (** Delta and location relations *)

  Definition mem_delta_unchanged_store (d: mem_delta_store) (b': block) (ofs': Z): Prop :=
    let '(ch, b, ofs, v, cp) := d in
    (b = b') -> (ofs > ofs' \/ ofs + (size_chunk ch) <= ofs').

  Lemma mem_delta_unchanged_on_store
        d m m'
        (APPD: mem_delta_apply_store (Some m) d = (Some m'))
    :
    Mem.unchanged_on (fun b ofs => mem_delta_unchanged_store d b ofs) m m'.
  Proof.
    destruct d as ((((ch & b) & ofs) & v) & cp). simpl in *.
    eapply Mem.store_unchanged_on. eauto. intros. intros CONTRA. specialize (CONTRA eq_refl). lia.
  Qed.

  Definition mem_delta_unchanged_bytes (d: mem_delta_bytes) (b': block) (ofs': Z): Prop :=
    let '(b, ofs, mvs, cp) := d in
    (b = b') -> (ofs > ofs' \/ ofs + Z.of_nat (Datatypes.length mvs) <= ofs').

  Lemma mem_delta_unchanged_on_bytes
        d m m'
        (APPD: mem_delta_apply_bytes (Some m) d = (Some m'))
    :
    Mem.unchanged_on (fun b ofs => mem_delta_unchanged_bytes d b ofs) m m'.
  Proof.
    destruct d as (((b & ofs) & mvs) & cp). simpl in *.
    eapply Mem.storebytes_unchanged_on. eauto. intros. intros CONTRA. specialize (CONTRA eq_refl). lia.
  Qed.

  Definition mem_delta_unchanged_alloc (d: mem_delta_alloc) (b': block) (ofs': Z): Prop :=
    let '(cp, lo, hi) := d in
    True.

  Lemma mem_delta_unchanged_on_alloc
        d m m'
        (APPD: mem_delta_apply_alloc (Some m) d = (Some m'))
    :
    Mem.unchanged_on (fun b ofs => mem_delta_unchanged_alloc d b ofs) m m'.
  Proof.
    destruct d as ((cp & lo) & hi). simpl in *. destruct (Mem.alloc m cp lo hi) eqn:ALLOC; simpl in *. inv APPD.
    eapply Mem.alloc_unchanged_on. eauto.
  Qed.

  Definition mem_delta_unchanged_free (d: mem_delta_free) (b': block) (ofs': Z): Prop :=
    let '(b, lo, hi, cp) := d in
    (b = b') -> (lo > ofs' \/ hi <= ofs').

  Lemma mem_delta_unchanged_on_free
        d m m'
        (APPD: mem_delta_apply_free (Some m) d = (Some m'))
    :
    Mem.unchanged_on (fun b ofs => mem_delta_unchanged_free d b ofs) m m'.
  Proof.
    destruct d as (((b & lo) & hi) & cp). simpl in *.
    eapply Mem.free_unchanged_on. eauto. intros. intros CONTRA. specialize (CONTRA eq_refl). lia.
  Qed.

  Definition mem_delta_kind_unchanged (k: mem_delta_kind) (b: block) (ofs: Z) :=
    match k with
    | mem_delta_kind_store dd => mem_delta_unchanged_store dd b ofs
    | mem_delta_kind_bytes dd => mem_delta_unchanged_bytes dd b ofs
    | mem_delta_kind_alloc dd => mem_delta_unchanged_alloc dd b ofs
    | mem_delta_kind_free dd => mem_delta_unchanged_free dd b ofs
    end.

  Definition mem_delta_unchanged (d: mem_delta) (b: block) (ofs: Z) :=
    Forall (fun k => mem_delta_kind_unchanged k b ofs) d.

  Lemma mem_delta_unchanged_on
        d m m'
        (APPD: mem_delta_apply d (Some m) = Some m')
    :
    Mem.unchanged_on (fun b ofs => mem_delta_unchanged d b ofs) m m'.
  Proof.
    revert m m' APPD. induction d; intros; simpl.
    { simpl in APPD. inv APPD. apply Mem.unchanged_on_refl. }
    rewrite mem_delta_apply_cons in APPD. destruct a.
    - destruct d0 as [[[[ch b] ofs] v] cp]. destruct (mem_delta_apply_store (Some m) (ch, b, ofs, v, cp)) eqn:MEM.
      2:{ rewrite mem_delta_apply_none in APPD. inv APPD. }
      specialize (IHd _ _ APPD). eapply Mem.unchanged_on_trans.
      2:{ eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H. auto. }
      { eapply Mem.unchanged_on_implies. eapply mem_delta_unchanged_on_store. eauto.
        intros. simpl. intros; subst. inv H. simpl in H3. specialize (H3 eq_refl). auto.
      }
    - destruct d0 as [[[b ofs] mvs] cp]. destruct (mem_delta_apply_bytes (Some m) (b, ofs, mvs, cp)) eqn:MEM.
      2:{ rewrite mem_delta_apply_none in APPD. inv APPD. }
      specialize (IHd _ _ APPD). eapply Mem.unchanged_on_trans.
      2:{ eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H. auto. }
      { eapply Mem.unchanged_on_implies. eapply mem_delta_unchanged_on_bytes. eauto.
        intros. simpl. intros; subst. inv H. simpl in H3. specialize (H3 eq_refl). auto.
      }
    - destruct d0 as [[cp lo] hi]. destruct (mem_delta_apply_alloc (Some m) (cp, lo, hi)) eqn:MEM.
      2:{ rewrite mem_delta_apply_none in APPD. inv APPD. }
      specialize (IHd _ _ APPD). eapply Mem.unchanged_on_trans.
      2:{ eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H. auto. }
      { eapply Mem.unchanged_on_implies. eapply mem_delta_unchanged_on_alloc. eauto.
        intros. simpl. auto.
      }
    - destruct d0 as [[[b lo] hi] cp]. destruct (mem_delta_apply_free (Some m) (b, lo, hi, cp)) eqn:MEM.
      2:{ rewrite mem_delta_apply_none in APPD. inv APPD. }
      specialize (IHd _ _ APPD). eapply Mem.unchanged_on_trans.
      2:{ eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H. auto. }
      { eapply Mem.unchanged_on_implies. eapply mem_delta_unchanged_on_free. eauto.
        intros. simpl. intros; subst. inv H. simpl in H3. specialize (H3 eq_refl). auto.
      }
  Qed.

  Lemma mem_delta_inj_unchanged_on
        j d m m'
        (STRICT: meminj_strict j)
        (APPD: mem_delta_apply_inj j d (Some m) = Some m')
    :
    Mem.unchanged_on (fun b ofs => (forall b0 ofsd, j b0 <> Some (b, ofsd)) \/ (exists b0 ofsd, j b0 = Some (b, ofsd) /\ mem_delta_unchanged d b0 (ofs - ofsd))) m m'.
  Proof.
    revert m m' APPD. induction d; intros; simpl.
    { simpl in APPD. inv APPD. apply Mem.unchanged_on_refl. }
    rewrite mem_delta_apply_inj_cons in APPD. destruct a.
    - destruct d0 as [[[[ch b] ofs] v] cp]. destruct (j b) as [[b' ofs'] |] eqn:JB.
      + exploit mem_delta_apply_inj_some. eauto. intros (mi & MEM). rewrite MEM in APPD.
        specialize (IHd _ _ APPD). eapply Mem.unchanged_on_trans.
        2:{ eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H; eauto. destruct H1 as (b1 & ofsd & JB1 & UNCHG). inv UNCHG. right. eauto. }
        { simpl in *. eapply Mem.store_unchanged_on. eauto. intros. intros [CC | CC].
          - specialize (CC b ofs'). congruence.
          - destruct CC as (b1 & ofsd & JB1 & UNCHG). inv UNCHG. simpl in H2. destruct (Pos.eqb_spec b b1).
            + subst b1. rewrite JB in JB1. inv JB1. specialize (H2 eq_refl). lia.
            + specialize (STRICT _ _ _ _ _ JB JB1). subst b1. lia.
        }
      + specialize (IHd _ _ APPD). eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H; eauto. destruct H1 as (b1 & ofsd & JB1 & UNCHG). inv UNCHG. right. eauto.
    - specialize (IHd _ _ APPD). eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H; eauto. destruct H1 as (b1 & ofsd & JB1 & UNCHG). inv UNCHG. right. eauto.
    - specialize (IHd _ _ APPD). eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H; eauto. destruct H1 as (b1 & ofsd & JB1 & UNCHG). inv UNCHG. right. eauto.
    - specialize (IHd _ _ APPD). eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H; eauto. destruct H1 as (b1 & ofsd & JB1 & UNCHG). inv UNCHG. right. eauto.
  Qed.


  Lemma get_from_setN_same_upto_ofs
        ofs0 ofs l ofsd
        (OFS: ofs0 <= ofs < ofs0 + Z.of_nat (Datatypes.length l))
        (mc1 mc2 : (ZMap.t memval))
    :
    ZMap.get ofs (Mem.setN l ofs0 mc1) = ZMap.get (ofs + ofsd) (Mem.setN l (ofs0 + ofsd) mc2).
  Proof.
    revert ofs0 ofs ofsd OFS mc1 mc2. induction l; simpl; intros.
    { lia. }
    destruct (Z.eqb_spec ofs0 ofs).
    { subst ofs0. clear OFS. rewrite ! Mem.setN_outside; try lia. rewrite ! ZMap.gss. auto. }
    { replace (ofs0 + ofsd + 1) with ((ofs0 + 1) + ofsd) by lia. eapply IHl. lia. }
  Qed.

  Lemma get_from_setN_same
        ofs0 ofs l
        (OFS: ofs0 <= ofs < ofs0 + Z.of_nat (Datatypes.length l))
        (mc1 mc2 : (ZMap.t memval))
    :
    ZMap.get ofs (Mem.setN l ofs0 mc1) = ZMap.get ofs (Mem.setN l ofs0 mc2).
  Proof.
    replace ofs with (ofs + 0) at 2 by lia. replace ofs0 with (ofs0 + 0) at 2 by lia. eapply get_from_setN_same_upto_ofs; auto.
  Qed.

  Lemma mem_store_same_upto_ofs
        ofs ofs0 ch0 v0 cp0 ofsd b b' m1 m2 m1' m2'
        (OFS: ofs0 <= ofs < ofs0 + size_chunk ch0)
        (MEM1: Mem.store ch0 m1 b ofs0 v0 cp0 = Some m1')
        (MEM2: Mem.store ch0 m2 b' (ofs0 + ofsd) v0 cp0 = Some m2')
    :
    ZMap.get ofs (Mem.mem_contents m1') !! b = ZMap.get (ofs + ofsd) (Mem.mem_contents m2') !! b'.
  Proof.
    apply Mem.store_mem_contents in MEM1, MEM2. rewrite MEM1, MEM2. rewrite ! PMap.gss.
    rewrite size_chunk_conv, <- (encode_val_length ch0 v0) in OFS.
    remember (encode_val ch0 v0) as l. remember (Mem.mem_contents m1) as mc1. remember (Mem.mem_contents m2) as mc2. clear - OFS.
    eapply get_from_setN_same_upto_ofs. auto.
  Qed.


  Definition mem_delta_changed_store (d: mem_delta_store) (b': block) (ofs': Z): Prop :=
    let '(ch, b, ofs, v, cp) := d in
    (b = b') /\ (ofs <= ofs' < ofs + (size_chunk ch)).

  Lemma mem_delta_changed_store_same
        d b ofs
        (CHG: mem_delta_changed_store d b ofs)
        m1 m1' m2 m2'
        (APPD1: mem_delta_apply_store (Some m1) d = Some m1')
        (APPD2: mem_delta_apply_store (Some m2) d = Some m2')
    :
    ZMap.get ofs (Mem.mem_contents m1') !! b = ZMap.get ofs (Mem.mem_contents m2') !! b.
  Proof.
    destruct d as [[[[ch0 b0] ofs0] v0] cp0]. destruct CHG as (BLK & OFS). subst b0.
    simpl in *. replace ofs with (ofs + 0) at 2 by lia. eapply mem_store_same_upto_ofs; eauto.
    replace (ofs0 + 0) with ofs0 by lia. eauto.
  Qed.

  Definition mem_delta_changed_bytes (d: mem_delta_bytes) (b': block) (ofs': Z): Prop :=
    let '(b, ofs, mvs, cp) := d in
    (b = b') /\ (ofs <= ofs' < ofs + Z.of_nat (Datatypes.length mvs)).

  Lemma mem_delta_changed_bytes_same
        d b ofs
        (CHG: mem_delta_changed_bytes d b ofs)
        m1 m1' m2 m2'
        (APPD1: mem_delta_apply_bytes (Some m1) d = Some m1')
        (APPD2: mem_delta_apply_bytes (Some m2) d = Some m2')
    :
    ZMap.get ofs (Mem.mem_contents m1') !! b = ZMap.get ofs (Mem.mem_contents m2') !! b.
  Proof.
    destruct d as [[[b0 ofs0] mvs0] cp0]. destruct CHG as (BLK & OFS). subst b0.
    simpl in *. apply Mem.storebytes_mem_contents in APPD1, APPD2. rewrite APPD1, APPD2. rewrite ! PMap.gss.
    eapply get_from_setN_same. auto.
  Qed.

  Definition mem_delta_changed_alloc (d: mem_delta_alloc) (b': block) (ofs': Z): Prop :=
    let '(cp, lo, hi) := d in
    False.

  Lemma mem_delta_changed_alloc_same
        d b ofs
        (CHG: mem_delta_changed_alloc d b ofs)
        m1 m1' m2 m2'
        (APPD1: mem_delta_apply_alloc (Some m1) d = Some m1')
        (APPD2: mem_delta_apply_alloc (Some m2) d = Some m2')
    :
    ZMap.get ofs (Mem.mem_contents m1') !! b = ZMap.get ofs (Mem.mem_contents m2') !! b.
  Proof.
    unfold mem_delta_changed_alloc in CHG. destruct d. destruct p. inv CHG.
  Qed.

  Definition mem_delta_changed_free (d: mem_delta_free) (b': block) (ofs': Z): Prop :=
    let '(b, lo, hi, cp) := d in
    (b = b') /\ (lo <= ofs' < hi).

  Definition mem_delta_kind_changed (k: mem_delta_kind) (b: block) (ofs: Z) :=
    match k with
    | mem_delta_kind_store dd => mem_delta_changed_store dd b ofs
    | mem_delta_kind_bytes dd => mem_delta_changed_bytes dd b ofs
    | mem_delta_kind_alloc dd => mem_delta_changed_alloc dd b ofs
    | mem_delta_kind_free dd => mem_delta_changed_free dd b ofs
    end.

  Definition mem_delta_changed (d: mem_delta) (b: block) (ofs: Z) :=
    Exists (fun k => mem_delta_kind_changed k b ofs) d.


  (** Propperties *)
  Lemma mem_delta_cases_store
        d b ofs
    :
    mem_delta_unchanged_store d b ofs \/ mem_delta_changed_store d b ofs.
  Proof. destruct d as [[[[ch0 b0] ofs0] v0] cp0]. simpl. lia. Qed.

  Lemma mem_delta_cases_bytes
        d b ofs
    :
    mem_delta_unchanged_bytes d b ofs \/ mem_delta_changed_bytes d b ofs.
  Proof. destruct d as [[[b0 ofs0] mvs] cp0]. simpl. lia. Qed.

  Lemma mem_delta_cases_alloc
        d b ofs
    :
    mem_delta_unchanged_alloc d b ofs \/ mem_delta_changed_alloc d b ofs.
  Proof. destruct d as [[x y] z]. simpl. auto. Qed.

  Lemma mem_delta_cases_free
        d b ofs
    :
    mem_delta_unchanged_free d b ofs \/ mem_delta_changed_free d b ofs.
  Proof. destruct d as [[[b0 lo] hi] cp0]. simpl. lia. Qed.

  Lemma mem_delta_cases_kind
        d b ofs
    :
    mem_delta_kind_unchanged d b ofs \/ mem_delta_kind_changed d b ofs.
  Proof. destruct d; simpl. apply mem_delta_cases_store. apply mem_delta_cases_bytes. apply mem_delta_cases_alloc. apply mem_delta_cases_free. Qed.

  Lemma mem_delta_unchanged_or_changed
        d b ofs
    :
    mem_delta_unchanged d b ofs \/ mem_delta_changed d b ofs.
  Proof.
    induction d.
    { left. constructor 1. }
    destruct IHd.
    2:{ right. constructor 2. auto. }
    destruct (mem_delta_cases_kind a b ofs).
    - left. constructor; auto.
    - right. constructor 1; auto.
  Qed.

  Lemma mem_delta_changed_only_by_store
        j d b ofs
        (STRICT: meminj_strict j)
        b' ofsd
        (INJ: j b = Some (b', ofsd))
        (WF: mem_delta_inj_wf j d)
        (CHG: mem_delta_changed d b ofs)
        m1 m1' m2 m2'
        (PERM1: Mem.perm m1 b ofs Cur Readable)
        (PERM2: Mem.perm m2 b' (ofs + ofsd) Cur Readable)
        (APPD1: mem_delta_apply d (Some m1) = Some m1')
        (APPD2: mem_delta_apply_inj j d (Some m2) = Some m2')
    :
    ZMap.get ofs (Mem.mem_contents m1') !! b = ZMap.get (ofs + ofsd) (Mem.mem_contents m2') !! b'.
  Proof.
    revert WF CHG m1 m1' m2 m2' PERM1 PERM2 APPD1 APPD2. induction d; intros.
    { inv CHG. }
    rewrite mem_delta_apply_cons in APPD1. rewrite mem_delta_apply_inj_cons in APPD2. inv WF. rename H1 into WF1, H2 into WF2. inv CHG.
    2:{ specialize (IHd WF2 H0). destruct a.
        - destruct d0 as [[[[ch0 b0 ]ofs0] v0] cp0]. destruct (j b0) as [[b0' ofs0'] |] eqn:JB.
          + exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1.
            exploit mem_delta_apply_inj_some. eapply APPD2. intros (mi2 & MEM2). rewrite MEM2 in APPD2.
            simpl in *. eapply IHd. 3,4: eauto. 1,2: eapply Mem.perm_store_1; eauto.
          + exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. simpl in *. eapply IHd. 3,4: eauto. all: auto. eapply Mem.perm_store_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[[w x] y] z]. simpl in *. eapply IHd. 3,4: eauto. all: auto.
          eapply Mem.perm_storebytes_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[x y] z]. simpl in *. eapply IHd. 3,4: eauto. all: auto.
          destruct (Mem.alloc m1 x y z) eqn:ALLOC. simpl in MEM1. inv MEM1. eapply Mem.perm_alloc_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[[w x] y] z]. simpl in *. eapply IHd. 3,4: eauto. all: auto.
          eapply Mem.perm_free_1; eauto. left. intros CC. subst. congruence.
    }
    rename H0 into CHG. destruct (mem_delta_unchanged_or_changed d b ofs).
    2:{ specialize (IHd WF2 H). destruct a.
        - destruct d0 as [[[[ch0 b0 ]ofs0] v0] cp0]. destruct (j b0) as [[b0' ofs0'] |] eqn:JB.
          + exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1.
            exploit mem_delta_apply_inj_some. eapply APPD2. intros (mi2 & MEM2). rewrite MEM2 in APPD2.
            simpl in *. eapply IHd. 3,4: eauto. 1,2: eapply Mem.perm_store_1; eauto.
          + exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. simpl in *. eapply IHd. 3,4: eauto. all: auto. eapply Mem.perm_store_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[[w x] y] z]. simpl in *. eapply IHd. 3,4: eauto. all: auto.
          eapply Mem.perm_storebytes_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[x y] z]. simpl in *. eapply IHd. 3,4: eauto. all: auto.
          destruct (Mem.alloc m1 x y z) eqn:ALLOC. simpl in MEM1. inv MEM1. eapply Mem.perm_alloc_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[[w x] y] z]. simpl in *. eapply IHd. 3,4: eauto. all: auto.
          eapply Mem.perm_free_1; eauto. left. intros CC. subst. congruence.
    }
    rename H into UNCHG. clear IHd. 
    { destruct a.
      - destruct d0 as [[[[ch0 b0] ofs0] v0] cp0]. destruct CHG as [CHG0 CHG1]. subst b0. rewrite INJ in APPD2.
        exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. exploit mem_delta_apply_inj_some. eapply APPD2. intros (mi2 & MEM2). rewrite MEM2 in APPD2.
        simpl in *.
        eapply mem_delta_unchanged_on in APPD1. exploit (Mem.unchanged_on_contents _ _ _ APPD1 b ofs); auto.
        { eapply Mem.perm_store_1; eauto. }
        intros. rewrite H; clear H.
        eapply mem_delta_inj_unchanged_on in APPD2; auto. exploit (Mem.unchanged_on_contents _ _ _ APPD2 b' (ofs + ofsd)); auto.
        { right. exists b, ofsd. split; auto. replace (ofs + ofsd - ofsd) with ofs by lia. auto. }
        { eapply Mem.perm_store_1; eauto. }
        intros. rewrite H; clear H.
        eapply mem_store_same_upto_ofs; eauto.
      - destruct d0 as [[[w x] y] z]. simpl in *. destruct CHG as [CHG0 CHG1]. subst w. rewrite WF1 in INJ. inv INJ.
      - destruct d0 as [[x y] z]. simpl in *. inv CHG.
      - destruct d0 as [[[w x] y] z]. simpl in *. inv CHG. rewrite WF1 in INJ. inv INJ.
    }
  Qed.

  Lemma mem_delta_apply_preserves_winject
        (j: meminj) m0 m0'
        (WINJ0: winject j m0 m0')
        (d: mem_delta)
        (DWF: mem_delta_inj_wf j d)
        m1
        (APPD: mem_delta_apply d (Some m0) = Some m1)
    :
    exists m1', (mem_delta_apply_inj j d (Some m0') = Some m1') /\ (winject j m1 m1').
  Proof.
    revert m0 m0' WINJ0 DWF m1 APPD. induction d; intros.
    { inv APPD. simpl. exists m0'. split; auto. }
    inv DWF. rename H1 into DWF1, H2 into DWF0. rewrite mem_delta_apply_cons in APPD. rewrite mem_delta_apply_inj_cons.
    destruct a.
    - destruct d0 as ((((ch & b) & ofs) & v) & cp). exploit mem_delta_apply_some. eauto. intros (mi & MEM). rewrite MEM in APPD.
      destruct (j b) as [[b' ofs']|] eqn:JB.
      + exploit store_mapped_winject; eauto. instantiate (1:=v). intros (mi0 & MEM' & WINJ1). specialize (IHd _ _ WINJ1 DWF0 _ APPD). destruct IHd as (m1' & APPD' & WINJ').
        simpl in *. rewrite MEM'. eauto.
      + exploit store_unmapped_winject; eauto.
    - destruct d0 as (((b & ofs) & mvs) & cp). exploit mem_delta_apply_some. eauto. intros (mi & MEM). rewrite MEM in APPD. exploit storebytes_unmapped_winject; eauto.
    - destruct d0 as ((cp & lo) & hi). exploit mem_delta_apply_some. eauto. intros (mi & MEM). rewrite MEM in APPD. simpl in *.
      destruct (Mem.alloc m0 cp lo hi) eqn:ALLOC; simpl in *. inv MEM. exploit alloc_left_unmapped_winject_keep; eauto.
    - destruct d0 as (((b & lo) & hi) & cp). exploit mem_delta_apply_some. eauto. intros (mi & MEM). rewrite MEM in APPD. exploit free_left_winject; eauto.
  Qed.

  Lemma mem_delta_apply_keeps_perm
        j d
        (DWF: mem_delta_inj_wf j d)
        m0 m1
        (APPD : mem_delta_apply d (Some m0) = Some m1)
        b ofs
        (INJ: j b <> None)
        K P
        (PERM: Mem.perm m1 b ofs K P)
        (BOUND: (b < Mem.nextblock m0)%positive)
    :
    Mem.perm m0 b ofs K P.
  Proof.
    revert DWF m0 APPD BOUND. induction d; intros.
    { simpl in *. inv APPD; auto. }
    inv DWF. rename H1 into DWF1, H2 into DWF2. rewrite mem_delta_apply_cons in APPD. specialize (IHd DWF2).
    destruct a; exploit mem_delta_apply_some; eauto; intros (mi & MEM); rewrite MEM in APPD; specialize (IHd _ APPD).
    - destruct d0 as ((((ch0 & b0) & ofs0) & v0) & cp0). simpl in *. eapply Mem.perm_store_2; eauto. eapply IHd. erewrite Mem.nextblock_store; eauto.
    - destruct d0 as (((b0 & ofs0) & mvs0) & cp0). simpl in *. eapply Mem.perm_storebytes_2; eauto. eapply IHd. erewrite Mem.nextblock_storebytes; eauto.
    - destruct d0 as ((cp0 & lo0) & hi0). simpl in *. destruct (Mem.alloc m0 cp0 lo0 hi0) eqn:ALLOC. simpl in *. inv MEM.
      exploit Mem.alloc_result; eauto. intros; subst b0. exploit Mem.nextblock_alloc; eauto. intros EQ.
      eapply Mem.perm_alloc_4. eauto.  eapply IHd. lia. lia.
    - destruct d0 as (((b0 & lo0) & hi0) & cp0). simpl in *.
      eapply Mem.perm_free_3; eauto. eapply IHd. erewrite Mem.nextblock_free; eauto.
  Qed.

  Lemma loc_first_order_always_memval_inject
        m b ofs
        (FO: loc_first_order m b ofs)
        j v
        (VINJ: memval_inject j (ZMap.get ofs (Mem.mem_contents m) !! b) v)
    :
    forall k, memval_inject k (ZMap.get ofs (Mem.mem_contents m) !! b) v.
  Proof.
    unfold loc_first_order in FO. destruct (ZMap.get ofs (Mem.mem_contents m) !! b) eqn:MV; try contradiction.
    inv VINJ. intros. constructor.
  Qed.

  Lemma mem_delta_apply_establish_inject
        (k j: meminj) m0 m0'
        (INJ: Mem.inject k m0 m0')
        (INCR: inject_incr j k)
        (STRICT: meminj_strict j)
        (NALLOC: meminj_not_alloc j m0)
        (d: mem_delta)
        (DWF: mem_delta_inj_wf j d)
        m1
        (APPD: mem_delta_apply d (Some m0) = Some m1)
        (FO: meminj_first_order j m1)
    :
    exists m1', (mem_delta_apply_inj j d (Some m0') = Some m1') /\ (Mem.inject j m1 m1').
  Proof.
    exploit inject_implies_winject; eauto. intros WINJ. exploit winject_inj_incr; eauto. clear WINJ; intro WINJ.
    exploit mem_delta_apply_preserves_winject; eauto. intros (m1' & APPD' & WINJ'). exists m1'. split; auto.
    apply winject_to_inject; auto. unfold mem_inj_val. intros.
    exploit mem_delta_apply_keeps_perm; eauto. congruence.
    { destruct (Pos.ltb_spec0 b1 (Mem.nextblock m0)); auto. exfalso. assert (j b1 = None).
      { eapply NALLOC. lia. }
      congruence.
    }
    intros PERM0.
    destruct (mem_delta_unchanged_or_changed d b1 ofs).
    - exploit mem_delta_unchanged_on; eauto. intros UNCHG1. exploit mem_delta_inj_unchanged_on; eauto. intros UNCHG2.
      erewrite (Mem.unchanged_on_contents _ _ _ UNCHG1). erewrite (Mem.unchanged_on_contents _ _ _ UNCHG2). all: eauto.
      2:{ right. exists b1, delta. split; auto. replace (ofs + delta - delta) with ofs by lia. auto. }
      { inv INJ. inv mi_inj. specialize (mi_memval _ _ _ _ (INCR _ _ _ H) PERM0). eapply loc_first_order_always_memval_inject; eauto.
        exploit FO. erewrite H. congruence. eauto. unfold loc_first_order; intros. destruct (ZMap.get ofs (Mem.mem_contents m1) !! b1) eqn:MEMV1; try contradiction.
        erewrite (Mem.unchanged_on_contents _ _ _ UNCHG1) in MEMV1; eauto. rewrite MEMV1. auto.
      }
      { inv WINJ. inv mwi_inj. eapply mwi_perm; eauto. }
    - rename H1 into CHG. erewrite <- mem_delta_changed_only_by_store; eauto.
      { exploit FO; eauto. rewrite H. congruence. intros. unfold loc_first_order in H1. destruct (ZMap.get ofs (Mem.mem_contents m1) !! b1); try contradiction. constructor. }
      { inv WINJ. inv mwi_inj. eapply mwi_perm; eauto. }
  Qed.

End MEMDELTA.
