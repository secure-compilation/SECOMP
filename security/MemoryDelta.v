Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.
Require Import MemoryWeak.
Require Import Tactics.

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
  Definition mem_delta_storev := (memory_chunk * val * val * compartment)%type.
  Definition mem_delta_store := (memory_chunk * block * Z * val * compartment)%type.
  Definition mem_delta_bytes := (block * Z * (list memval) * compartment)%type.
  Definition mem_delta_alloc := (compartment * Z * Z)%type.
  Definition mem_delta_free := (block * Z * Z * compartment)%type.

  Inductive mem_delta_kind :=
  | mem_delta_kind_storev (d: mem_delta_storev)
  | mem_delta_kind_store (d: mem_delta_store)
  | mem_delta_kind_bytes (d: mem_delta_bytes)
  | mem_delta_kind_alloc (d: mem_delta_alloc)
  | mem_delta_kind_free (d: mem_delta_free)
  .

  (* order: old to new *)
  Definition mem_delta := list mem_delta_kind.

  Definition mem_delta_apply_storev (om: option mem) (d: mem_delta_storev): option mem :=
    let '(ch, ptr, v, cp) := d in
    match om with
    | Some m => Mem.storev ch m ptr v cp
    | None => None
    end.

  Lemma mem_delta_apply_storev_none
        d
    :
    mem_delta_apply_storev None d = None.
  Proof. unfold mem_delta_apply_storev. destruct d as [[[d0 d2] d3] d4]. auto. Qed.

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

  Definition mem_delta_apply_kind (data: mem_delta_kind) (om: option mem) : option mem :=
    match data with
    | mem_delta_kind_storev d => mem_delta_apply_storev om d
    | mem_delta_kind_store d => mem_delta_apply_store om d
    | mem_delta_kind_bytes d => mem_delta_apply_bytes om d
    | mem_delta_kind_alloc d => mem_delta_apply_alloc om d
    | mem_delta_kind_free d => mem_delta_apply_free om d
    end.

  Definition mem_delta_apply (d: mem_delta) (om0: option mem) : option mem :=
    fold_left (fun om data => mem_delta_apply_kind data om) d om0.

  Lemma mem_delta_apply_cons
        d m0 k
    :
    mem_delta_apply (k :: d) m0 =
      match k with
      | mem_delta_kind_storev dd => mem_delta_apply d (mem_delta_apply_storev (m0) dd)
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
    destruct a;
      [rewrite mem_delta_apply_storev_none | rewrite mem_delta_apply_store_none | rewrite mem_delta_apply_bytes_none | rewrite mem_delta_apply_alloc_none | rewrite mem_delta_apply_free_none]; rewrite IHd; auto.
  Qed.

  Lemma mem_delta_apply_some
        d om m'
        (APPD: mem_delta_apply d om = Some m')
    :
    exists m, om = Some m.
  Proof. destruct om; eauto. rewrite mem_delta_apply_none in APPD. inv APPD. Qed.

End MEMDELTA.


Section WFDELTA.
  (** only wf delta is applied for back transltation *)

  (* Refer to encode_val *)
  Definition wf_chunk_val_b (ch: memory_chunk) (v: val) :=
    match v with
    | Vundef => false
    | Vint n =>
        match ch with
        | Mint8signed | Mint8unsigned => true
        | Mint16signed | Mint16unsigned => true
        | Mint32 => true
        | _ => false
        end
    | Vlong n =>
        match ch with
        | Mint64 => true
        | Many32 => false
        | Many64 => false
        | _ => false
        end
    | Vfloat n =>
        match ch with
        | Mfloat64 => true
        | Many32 => false
        | Many64 => false
        | _ => false
        end
    | Vsingle n =>
        match ch with
        | Mfloat32 => true
        | Many32 => false
        | Many64 => false
        | _ => false
        end
    | Vptr _ _ => false
    end.

  Definition wf_mem_delta_storev_b (ge: Senv.t) (cp0: compartment) (d: mem_delta_storev) :=
    let '(ch, ptr, v, cp) := d in
    match ptr with
    | Vptr b ofs => match Senv.invert_symbol ge b with
                   | Some id => (Senv.public_symbol ge id) && (wf_chunk_val_b ch v) && (cp_eq_dec cp0 cp)
                   | _ => false
                   end
    | _ => false
    end.

  Definition wf_mem_delta_kind_b (ge: Senv.t) cp0 (d: mem_delta_kind) :=
    match d with | mem_delta_kind_storev dd => wf_mem_delta_storev_b ge cp0 dd | _ => false end.

  Definition get_wf_mem_delta (ge: Senv.t) cp0 (d: mem_delta): mem_delta :=
    filter (wf_mem_delta_kind_b ge cp0) d.

  Lemma get_wf_mem_delta_cons
        ge cp0 d k
    :
    get_wf_mem_delta ge cp0 (k :: d) =
      if (wf_mem_delta_kind_b ge cp0 k) then k :: (get_wf_mem_delta ge cp0 d) else (get_wf_mem_delta ge cp0 d).
  Proof. ss. Qed.

  Lemma get_wf_mem_delta_app
        ge cp0 d0 d1
    :
    get_wf_mem_delta ge cp0 (d0 ++ d1) = (get_wf_mem_delta ge cp0 d0) ++ (get_wf_mem_delta ge cp0 d1).
  Proof. apply filter_app. Qed.


  Definition mem_delta_apply_wf ge cp0 (d: mem_delta) (om0: option mem): option mem :=
    mem_delta_apply (get_wf_mem_delta ge cp0 d) om0.

  Lemma mem_delta_apply_wf_cons
        ge cp0 d m0 k
    :
    mem_delta_apply_wf ge cp0 (k :: d) m0 =
      if (wf_mem_delta_kind_b ge cp0 k) then mem_delta_apply_wf ge cp0 d (mem_delta_apply_kind k m0) else mem_delta_apply_wf ge cp0 d m0.
  Proof. unfold mem_delta_apply_wf at 1. rewrite get_wf_mem_delta_cons. des_ifs. Qed.

  Lemma mem_delta_apply_wf_app
        ge cp0 d0 d1 m0
    :
    mem_delta_apply_wf ge cp0 (d0 ++ d1) m0 =
      mem_delta_apply_wf ge cp0 d1 (mem_delta_apply_wf ge cp0 d0 m0).
  Proof. unfold mem_delta_apply_wf. rewrite get_wf_mem_delta_app. apply mem_delta_apply_app. Qed.

  Lemma mem_delta_apply_wf_none
        ge cp0 d
    :
    mem_delta_apply_wf ge cp0 d None = None.
  Proof. unfold mem_delta_apply_wf. apply mem_delta_apply_none. Qed.

  Lemma mem_delta_apply_wf_some
        ge cp0 d m0 m1
        (APPD: mem_delta_apply_wf ge cp0 d m0 = Some m1)
    :
    exists m, m0 = Some m.
  Proof. unfold mem_delta_apply_wf in APPD. exploit mem_delta_apply_some; eauto. Qed.

End WFDELTA.


Section PROPS.

  (** Delta and location relations *)

  Let mcps := PTree.t compartment.

  Definition mem_delta_unchanged_storev (d: mem_delta_storev) (b': block) (ofs': Z): Prop :=
    let '(ch, ptr, v, cp) := d in
    match ptr with
    | Vptr b ofs0 => let ofs := (Ptrofs.unsigned ofs0) in (b = b') -> (ofs > ofs' \/ ofs + (size_chunk ch) <= ofs')
    | _ => True
    end.

  Lemma mem_delta_unchanged_on_storev
        d m m'
        (APPD: mem_delta_apply_storev (Some m) d = (Some m'))
    :
    Mem.unchanged_on (fun b ofs => mem_delta_unchanged_storev d b ofs) m m'.
  Proof.
    destruct d as (((ch & ptr) & v) & cp). ss. unfold Mem.storev in APPD. des_ifs.
    eapply Mem.store_unchanged_on. eauto. intros. intros CONTRA. specialize (CONTRA eq_refl). lia.
  Qed.

  Definition mem_delta_unchanged_store (d: mem_delta_store) (b': block) (ofs': Z): Prop :=
    let '(ch, b, ofs, v, cp) := d in (b = b') -> (ofs > ofs' \/ ofs + (size_chunk ch) <= ofs').

  Lemma mem_delta_unchanged_on_store
        d m m'
        (APPD: mem_delta_apply_store (Some m) d = (Some m'))
    :
    Mem.unchanged_on (fun b ofs => mem_delta_unchanged_store d b ofs) m m'.
  Proof.
    destruct d as ((((ch & b) & ofs) & v) & cp). ss.
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
    | mem_delta_kind_storev dd => mem_delta_unchanged_storev dd b ofs
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
    - destruct d0 as [[[ch ptr] v] cp]. destruct (mem_delta_apply_storev (Some m) (ch, ptr, v, cp)) eqn:MEM.
      2:{ rewrite mem_delta_apply_none in APPD. inv APPD. }
      specialize (IHd _ _ APPD). eapply Mem.unchanged_on_trans.
      2:{ eapply Mem.unchanged_on_implies. eapply IHd. intros. simpl. inv H. auto. }
      { eapply Mem.unchanged_on_implies. eapply mem_delta_unchanged_on_storev. eauto.
        intros. simpl. des_ifs. intros; subst. inv H. simpl in H3. specialize (H3 eq_refl). auto.
      }
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

  Lemma mem_delta_wf_unchanged_on
        ge cp d m m'
        (APPD: mem_delta_apply_wf ge cp d (Some m) = Some m')
    :
    Mem.unchanged_on (fun b ofs => mem_delta_unchanged (get_wf_mem_delta ge cp d) b ofs) m m'.
  Proof. eapply mem_delta_unchanged_on; eauto. Qed.

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


  Definition mem_delta_changed_storev (d: mem_delta_storev) (b': block) (ofs': Z): Prop :=
    let '(ch, ptr, v, cp) := d in
    match ptr with
    | Vptr b ofs0 => let ofs := Ptrofs.unsigned ofs0 in (b = b') /\ (ofs <= ofs' < ofs + (size_chunk ch))
    | _ => False
    end.

  Lemma mem_delta_changed_storev_same
        d b ofs
        (CHG: mem_delta_changed_storev d b ofs)
        m1 m1' m2 m2'
        (APPD1: mem_delta_apply_storev (Some m1) d = Some m1')
        (APPD2: mem_delta_apply_storev (Some m2) d = Some m2')
    :
    ZMap.get ofs (Mem.mem_contents m1') !! b = ZMap.get ofs (Mem.mem_contents m2') !! b.
  Proof.
    destruct d as [[[ch0 ptr0] v0] cp0]. unfold mem_delta_changed_storev in CHG. des_ifs.
    destruct CHG as (BLK & OFS). subst b0.
    simpl in *. replace ofs with (ofs + 0) at 2 by lia. eapply mem_store_same_upto_ofs; eauto.
    rewrite Z.add_0_r. eauto.
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
    | mem_delta_kind_storev dd => mem_delta_changed_storev dd b ofs
    | mem_delta_kind_store dd => mem_delta_changed_store dd b ofs
    | mem_delta_kind_bytes dd => mem_delta_changed_bytes dd b ofs
    | mem_delta_kind_alloc dd => mem_delta_changed_alloc dd b ofs
    | mem_delta_kind_free dd => mem_delta_changed_free dd b ofs
    end.

  Definition mem_delta_changed (d: mem_delta) (b: block) (ofs: Z) :=
    Exists (fun k => mem_delta_kind_changed k b ofs) d.


  (** Propperties *)
  Lemma mem_delta_cases_storev
        d b ofs
    :
    mem_delta_unchanged_storev d b ofs \/ mem_delta_changed_storev d b ofs.
  Proof. destruct d as [[[ch0 ptr0] v0] cp0]. ss. des_ifs; auto. lia. Qed.

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
  Proof. destruct d; simpl. apply mem_delta_cases_storev. apply mem_delta_cases_store. apply mem_delta_cases_bytes. apply mem_delta_cases_alloc. apply mem_delta_cases_free. Qed.

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

End PROPS.

Section PROOFS.
  (** Props for proofs *)

  Definition mem_delta_kind_inj_wf (cp0: compartment) (j: meminj): mem_delta_kind -> Prop :=
    fun data =>
      match data with
      | mem_delta_kind_storev (ch, ptr, v, cp) => cp = cp0
      | mem_delta_kind_store (ch, b, ofs, v, cp) => (j b) = None
      | mem_delta_kind_bytes (b, ofs, mvs, cp) => (j b) = None
      | mem_delta_kind_free (b, lo, hi, cp) => (j b) = None
      | _ => True
      end.

  Definition mem_delta_inj_wf cp (j: meminj): mem_delta -> Prop :=
    fun d => Forall (fun data => mem_delta_kind_inj_wf cp j data) d.

  Section VISIBLE.

  (* Memory location has only sequence of bytes *)
  Definition loc_first_order (m: mem) (b: block) (ofs: Z) : Prop :=
    match (ZMap.get ofs (Mem.mem_contents m) !! b) with
    | Byte _ => True
    | _ => False
    end.

  (* Public symbols are visible outside the compilation unit,
     so when interacting via external calls, limit them to first-order (if Readable). *)
  Definition public_first_order (ge: Senv.t) (m: mem) :=
    forall id b ofs
      (PUBLIC: Senv.public_symbol ge id = true)
      (FIND: Senv.find_symbol ge id = Some b)
      (READABLE: Mem.perm m b ofs Cur Readable),
      loc_first_order m b ofs.

  Definition block_public (ge: Senv.t) (b: block): Prop :=
    exists id, Senv.invert_symbol ge b = Some id /\ Senv.public_symbol ge id = true.

  Variant val_public (ge: Senv.t) : typ -> val -> Prop :=
    | val_public_int: forall i, val_public ge Tint (Vint i)
    | val_public_long: forall i, val_public ge Tlong (Vlong i)
    | val_public_float: forall f, val_public ge Tfloat (Vfloat f)
    | val_public_single: forall f, val_public ge Tsingle (Vsingle f)
    | val_public_ptr: forall b ofs, block_public ge b -> val_public ge Tptr (Vptr b ofs).

  Definition vals_public (ge: Senv.t) (ts: list typ) (vs: list val): Prop :=
    Forall2 (val_public ge) ts vs.

  Definition visible_fo (ge: Senv.t) (m: mem) (tys: list typ) (args: list val): Prop :=
    public_first_order ge m /\ vals_public ge tys args.

  Definition EF_memcpy_dest_not_pub (ge: Senv.t) (args: list val) :=
    match args with
    | (Vptr bdst _) :: tl => ~ (block_public ge bdst)
    | _ => True
    end.

  Definition load_whole_chunk (ch: memory_chunk) (v: val) := Val.load_result ch v = v.

  Definition EF_vstore_load_whole_chunk (ch: memory_chunk) (args: list val) :=
    match args with
    | _ :: v :: nil => load_whole_chunk ch v
    | _ => True
    end.

  Definition external_call_conds
             (ef: external_function) (ge: Senv.t) (m: mem) (args: list val) : Prop :=
    match ef with
    | EF_external name sg => visible_fo ge m (sig_args sg) args
    | EF_builtin name sg | EF_runtime name sg =>
                             match Builtins.lookup_builtin_function name sg with
                             | None => visible_fo ge m (sig_args sg) args
                             | _ => True
                             end
    | EF_inline_asm txt sg clb => visible_fo ge m (sig_args sg) args
    | EF_memcpy sz al => EF_memcpy_dest_not_pub ge args
    | EF_vstore ch => EF_vstore_load_whole_chunk ch args
    | _ => True
    end.

  Definition external_call_unknowns
             (ef: external_function) (ge: Senv.t) (m: mem) (args: list val) : Prop :=
    match ef with
    | EF_external name sg => visible_fo ge m (sig_args sg) args
    | EF_builtin name sg | EF_runtime name sg =>
                             match Builtins.lookup_builtin_function name sg with
                             | None => visible_fo ge m (sig_args sg) args
                             | _ => False
                             end
    | EF_inline_asm txt sg clb => visible_fo ge m (sig_args sg) args
    | _ => False
    end.

  Definition external_call_known_observables
             (ef: external_function) (ge: Senv.t) (cp: compartment) (m: mem) (args: list val) tr rv m' : Prop :=
    match ef with
    | EF_external name sg => False
    | EF_builtin name sg | EF_runtime name sg => False
    | EF_inline_asm txt sg clb => False
    | EF_vstore ch =>
        (external_call ef ge cp args m tr rv m') /\ (tr <> E0) /\ (EF_vstore_load_whole_chunk ch args)
    | _ => (external_call ef ge cp args m tr rv m') /\ (tr <> E0)
    end.

  Definition external_call_known_silents
             (ef: external_function) (ge: Senv.t) (cp: compartment) (m: mem) (args: list val) tr rv m': Prop :=
    match ef with
    | EF_external name sg => False
    | EF_builtin name sg | EF_runtime name sg =>
                             match Builtins.lookup_builtin_function name sg with
                             | None => False
                             | _ => True
                             end
    | EF_inline_asm txt sg clb => False
    | EF_memcpy sz al =>
        (external_call ef ge cp args m E0 rv m') /\ (tr = E0) /\ (EF_memcpy_dest_not_pub ge args)
    | _ => (external_call ef ge cp args m E0 rv m') /\ (tr = E0)
    end.



End VISIBLE.
  Definition meminj_first_order (j: meminj) (m: mem) :=
    forall b ofs, (j b <> None) -> (Mem.perm m b ofs Cur Readable) -> loc_first_order m b ofs.

  Definition meminj_not_alloc (j: meminj) (m: mem) := forall b, (Mem.nextblock m <= b)%positive -> j b = None.


  Lemma mem_storev_first_order_wf_chunk_val
        ch m b i v cp m'
        (MEM: Mem.storev ch m (Vptr b i) v cp = Some m')
        ofs
        (FO: loc_first_order m' b ofs)
        (CHG: Ptrofs.unsigned i <= ofs < Ptrofs.unsigned i + size_chunk ch)
    :
    wf_chunk_val_b ch v.
  Proof.
    unfold loc_first_order in FO.
    ss. exploit Mem.store_mem_contents; eauto. intros CNT.
    rewrite CNT in FO.
    remember (Ptrofs.unsigned i) as ofs0.
    rewrite PMap.gss in FO.
    remember ((Mem.mem_contents m) !! b) as mcv. clear - FO CHG.
    assert (IN: In (ZMap.get ofs (Mem.setN (encode_val ch v) ofs0 mcv)) (encode_val ch v)).
    { eapply Mem.setN_in. rewrite encode_val_length. rewrite <- size_chunk_conv. auto. }
    remember (ZMap.get ofs (Mem.setN (encode_val ch v) ofs0 mcv)) as mv.
    clear - FO IN.
    destruct ch; destruct v; ss; des; clarify.
    1,2: des_ifs; ss; des; clarify.
  Qed.

  Lemma list_forall_filter
        A (P: A -> Prop) l B
        (FA: Forall P l)
    :
    Forall P (filter B l).
  Proof. induction FA; ss. des_ifs. econs; eauto. Qed.

  Lemma mem_delta_unchanged_implies_wf_unchanged
        ge cp d b ofs
        (UNCHG: mem_delta_unchanged d b ofs)
    :
    mem_delta_unchanged (get_wf_mem_delta ge cp d) b ofs.
  Proof. eapply list_forall_filter; eauto. Qed.

  Lemma mem_delta_changed_only_by_storev
        ge cp d b ofs
        (WF: mem_delta_inj_wf cp (meminj_public ge) d)
        (INJ: (meminj_public ge) b <> None)
        (CHG: mem_delta_changed d b ofs)
        m1 m1' m2 m2'
        (APPD1: mem_delta_apply d (Some m1) = Some m1')
        (APPD2: mem_delta_apply_wf ge cp d (Some m2) = Some m2')
        (PERM1: Mem.perm m1 b ofs Cur Readable)
        (PERM2: Mem.perm m2 b ofs Cur Readable)
        (FO: loc_first_order m1' b ofs)
    :
    ZMap.get ofs (Mem.mem_contents m1') !! b = ZMap.get ofs (Mem.mem_contents m2') !! b.
  Proof.
    revert WF CHG m1 m1' m2 m2' APPD1 APPD2 PERM1 PERM2 FO. induction d; intros.
    { inv CHG. }
    rewrite mem_delta_apply_cons in APPD1. rewrite mem_delta_apply_wf_cons in APPD2. inv WF. rename H1 into WF1, H2 into WF2. inv CHG.
    (* not chagned by the head *)
    2:{ specialize (IHd WF2 H0). destruct a.
        - destruct d0 as [[[ch0 ptr0] v0] cp0]. des_ifs.
          + exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1.
            exploit mem_delta_apply_wf_some. eapply APPD2. intros (mi2 & MEM2). rewrite MEM2 in APPD2.
            ss. unfold Mem.storev in MEM1. des_ifs. ss. eapply IHd; eauto. 1,2: eapply Mem.perm_store_1; eauto.
          + exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1.
            exploit mem_delta_apply_wf_some. eapply APPD2. intros (mi2 & MEM2). rewrite MEM2 in APPD2.
            ss. unfold Mem.storev in MEM1. destruct ptr0; ss; clarify. eapply IHd; eauto. eapply Mem.perm_store_1; eauto.
        - destruct d0 as [[[[ch0 b0 ]ofs0] v0] cp0]. des_ifs.
          exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1.
          ss. eapply IHd; eauto. eapply Mem.perm_store_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[[w x] y] z]. simpl in *. eapply IHd; eauto.
          eapply Mem.perm_storebytes_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[x y] z]. simpl in *. eapply IHd; eauto.
          destruct (Mem.alloc m1 x y z) eqn: ALLOC. ss. inv MEM1. eapply Mem.perm_alloc_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[[w x] y] z]. simpl in *. eapply IHd; eauto.
          eapply Mem.perm_free_1; eauto. left. ii. subst w. clarify.
    }
    rename H0 into CHG. destruct (mem_delta_unchanged_or_changed d b ofs).
    (* overwrite by the tail *)
    2:{ specialize (IHd WF2 H). destruct a.
        - destruct d0 as [[[ch0 ptr0] v0] cp0]. des_ifs.
          + exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1.
            exploit mem_delta_apply_wf_some. eapply APPD2. intros (mi2 & MEM2). rewrite MEM2 in APPD2.
            ss. unfold Mem.storev in MEM1. des_ifs. ss. eapply IHd; eauto. 1,2: eapply Mem.perm_store_1; eauto.
          + exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1.
            exploit mem_delta_apply_wf_some. eapply APPD2. intros (mi2 & MEM2). rewrite MEM2 in APPD2.
            ss. unfold Mem.storev in MEM1. destruct ptr0; ss; clarify. eapply IHd; eauto. eapply Mem.perm_store_1; eauto.
        - destruct d0 as [[[[ch0 b0 ]ofs0] v0] cp0]. des_ifs.
          exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1.
          ss. eapply IHd; eauto. eapply Mem.perm_store_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[[w x] y] z]. simpl in *. eapply IHd; eauto.
          eapply Mem.perm_storebytes_1; eauto.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[x y] z]. simpl in *. eapply IHd; eauto.
          destruct (Mem.alloc m1 x y z) eqn: ALLOC. ss.
        - exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1. destruct d0 as [[[w x] y] z]. simpl in *. eapply IHd; eauto.
          eapply Mem.perm_free_1; eauto. left. ii. subst w. clarify.
    }
    rename H into UNCHG. clear IHd.
    { destruct a.
      2,3,5: ss; des_ifs; ss; des; clarify.
      2:{ destruct d0 as [[x y] z]. ss. }
      destruct d0 as [[[ch0 ptr0] v0] cp0]. ss. destruct ptr0; ss. des; clarify.
      assert (exists id, Senv.invert_symbol ge b = Some id /\ Senv.public_symbol ge id).
      { clear - INJ. unfold meminj_public in INJ. des_ifs. eauto. }
      des. rename H into INV, H0 into PUB. rewrite INV, PUB in APPD2.
      exploit mem_delta_apply_some. eapply APPD1. intros (mi1 & MEM1). rewrite MEM1 in APPD1.
      eapply mem_delta_unchanged_on in APPD1. exploit (Mem.unchanged_on_contents _ _ _ APPD1 b ofs); auto.
      { eapply Mem.perm_store_1; eauto. }
      intros H. rewrite H.
      ss.
      assert (FO2: loc_first_order mi1 b ofs).
      { unfold loc_first_order in *. rewrite <- H. auto. }
      exploit mem_storev_first_order_wf_chunk_val. 2,3: eauto. ss. eauto.
      intros WFCV. rewrite WFCV in APPD2.
      destruct (cp_eq_dec cp cp); try contradiction.
      ss.
      (* rewrite Pos.eqb_refl in APPD2. *)
      des_ifs.
      exploit mem_delta_apply_wf_some. eapply APPD2. intros (mi2 & MEM2). rewrite MEM2 in APPD2.
      eapply mem_delta_wf_unchanged_on in APPD2; auto. exploit (Mem.unchanged_on_contents _ _ _ APPD2 b ofs); auto.
      { eapply mem_delta_unchanged_implies_wf_unchanged; eauto. }
      { eapply Mem.perm_store_1; eauto. }
      intros H0. rewrite H0. replace ofs with (ofs + 0)%Z at 2 by lia.
      eapply mem_store_same_upto_ofs; eauto. rewrite Z.add_0_r. eauto.
    }
  Qed.

  Lemma store_left_mapped_winj:
    forall f chunk m1 b1 ofs v1 cp n1 m2 b2 delta,
      mem_winj f m1 m2 ->
      Mem.store chunk m1 b1 ofs v1 cp = Some n1 ->
      f b1 = Some (b2, delta) ->
      mem_winj f n1 m2.
  Proof.
    intros.
    inv H. constructor.
    (* perm *)
    intros. eapply mwi_perm; eauto. eapply Mem.perm_store_2; eauto.
    (* own *)
    intros. eapply mwi_own. eauto. apply (proj2 (Mem.store_can_access_block_inj _ _ _ _ _ _ _ H0 _ _)). auto.
    (* align *)
    intros. eapply mwi_align with (ofs := ofs0) (p := p); eauto. red; intros; eauto with mem.
  Qed.

  Lemma store_left_mapped_winject:
    forall f chunk m1 b1 ofs v1 cp n1 m2 b2 delta,
      winject f m1 m2 ->
      Mem.store chunk m1 b1 ofs v1 cp = Some n1 ->
      f b1 = Some (b2, delta) ->
      winject f n1 m2.
  Proof.
    intros. inversion H. exploit store_left_mapped_winj; eauto. intros MI. constructor.
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
    intros. exploit mwi_perm_inv; eauto using Mem.perm_store_2.
    intuition eauto using Mem.perm_store_1, Mem.perm_store_2.
  Qed.

  Lemma store_left_winject:
    forall f chunk m1 b1 ofs v1 cp n1 m2,
      winject f m1 m2 ->
      Mem.store chunk m1 b1 ofs v1 cp = Some n1 ->
      winject f n1 m2.
  Proof.
    intros. destruct (f b1) eqn:FB.
    - destruct p. eapply store_left_mapped_winject; eauto.
    - eapply store_unmapped_winject; eauto.
  Qed.

  Lemma storebytes_left_mapped_winj:
    forall f m1 b1 ofs v1 cp n1 m2 b2 delta,
      mem_winj f m1 m2 ->
      Mem.storebytes m1 b1 ofs v1 cp = Some n1 ->
      f b1 = Some (b2, delta) ->
      mem_winj f n1 m2.
  Proof.
    intros.
    inv H. constructor.
    (* perm *)
    intros. eapply mwi_perm; eauto. eapply Mem.perm_storebytes_2; eauto.
    (* own *)
    intros. eapply mwi_own; eauto. eapply Mem.storebytes_can_access_block_inj_2; eauto.
    (* align *)
    intros. eapply mwi_align with (ofs := ofs0) (p := p); eauto.
    red; intros. eapply Mem.perm_storebytes_2; eauto.
  Qed.

  Lemma storebytes_left_mapped_winject:
    forall f m1 b1 ofs v1 cp n1 m2 b2 delta,
      winject f m1 m2 ->
      Mem.storebytes m1 b1 ofs v1 cp = Some n1 ->
      f b1 = Some (b2, delta) ->
      winject f n1 m2.
  Proof.
    intros. inversion H. exploit storebytes_left_mapped_winj; eauto. intros MI. constructor.
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
    intros. exploit mwi_perm_inv; eauto using Mem.perm_storebytes_2.
    intuition eauto using Mem.perm_storebytes_1, Mem.perm_storebytes_2.
  Qed.

  Lemma storebytes_left_winject:
    forall f m1 b1 ofs v1 cp n1 m2,
      winject f m1 m2 ->
      Mem.storebytes m1 b1 ofs v1 cp = Some n1 ->
      winject f n1 m2.
  Proof.
    intros. destruct (f b1) eqn:FB.
    - destruct p. eapply storebytes_left_mapped_winject; eauto.
    - eapply storebytes_unmapped_winject; eauto.
  Qed.

  Lemma mem_delta_apply_preserves_winject
        ge cp0 m0 m0'
        (WINJ0: winject (meminj_public ge) m0 m0')
        (d: mem_delta)
        m1
        (APPD: mem_delta_apply d (Some m0) = Some m1)
    :
    exists m1', (mem_delta_apply_wf ge cp0 d (Some m0') = Some m1') /\ (winject (meminj_public ge) m1 m1').
  Proof.
    revert m0 m0' WINJ0 m1 APPD. induction d; intros.
    { inv APPD. exists m0'. ss. }
    rewrite mem_delta_apply_cons in APPD. rewrite mem_delta_apply_wf_cons. destruct a.
    - exploit mem_delta_apply_some. eauto. intros (mi & MEM). rewrite MEM in APPD. des_ifs.
      + destruct d0 as (((ch & ptr) & v) & cp). destruct ptr; ss. destruct ((meminj_public ge) b) as [[b' ofs']|] eqn:JB.
        * exploit store_mapped_winject; eauto. instantiate (1:=v). intros (mi0 & MEM' & WINJ1). specialize (IHd _ _ WINJ1 _ APPD). destruct IHd as (m1' & APPD' & WINJ').
          unfold meminj_public in JB. des_ifs. rewrite Z.add_0_r in MEM'. rewrite MEM'. eauto.
        * exploit store_unmapped_winject; eauto. unfold meminj_public in JB. des_ifs.
      + destruct d0 as (((ch & ptr) & v) & cp). destruct ptr; ss. exploit store_left_winject; eauto.
    - destruct d0 as ((((ch & b) & ofs) & v) & cp). ss. exploit mem_delta_apply_some. eauto. intros (mi & MEM). rewrite MEM in APPD.
      exploit store_left_winject; eauto.
    - destruct d0 as (((b & ofs) & mvs) & cp). exploit mem_delta_apply_some. eauto. intros (mi & MEM). rewrite MEM in APPD. ss. exploit storebytes_left_winject; eauto.
    - destruct d0 as ((cp & lo) & hi). exploit mem_delta_apply_some. eauto. intros (mi & MEM). rewrite MEM in APPD.
      ss. destruct (Mem.alloc m0 cp lo hi) eqn:ALLOC; simpl in *. inv MEM. exploit alloc_left_unmapped_winject_keep; eauto.
    - destruct d0 as (((b & lo) & hi) & cp). exploit mem_delta_apply_some. eauto. intros (mi & MEM). rewrite MEM in APPD. ss.
      exploit free_left_winject; eauto.
  Qed.

  Lemma mem_delta_apply_keeps_perm
        cp j d
        (DWF: mem_delta_inj_wf cp j d)
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
    - destruct d0 as (((ch0 & ptr0) & v0) & cp0). ss. clarify. destruct ptr0; ss. eapply Mem.perm_store_2; eauto. eapply IHd. erewrite Mem.nextblock_store; eauto.
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
    unfold loc_first_order in FO.
    destruct (ZMap.get ofs (Mem.mem_contents m) !! b) eqn:MV; try contradiction.
    inv VINJ. intros. constructor.
  Qed.

  Lemma mem_delta_apply_establish_inject
        (ge: Senv.t) (k: meminj) m0 m0'
        (INJ: Mem.inject k m0 m0')
        (INCR: inject_incr (meminj_public ge) k)
        (NALLOC: meminj_not_alloc (meminj_public ge) m0)
        (d: mem_delta) cp
        (DWF: mem_delta_inj_wf cp (meminj_public ge) d)
        m1
        (APPD: mem_delta_apply d (Some m0) = Some m1)
        (FO: meminj_first_order (meminj_public ge) m1)
    :
    exists m1', (mem_delta_apply_wf ge cp d (Some m0') = Some m1') /\ (Mem.inject (meminj_public ge) m1 m1').
  Proof.
    exploit inject_implies_winject; eauto. intros WINJ. exploit winject_inj_incr; eauto. clear WINJ; intro WINJ.
    exploit mem_delta_apply_preserves_winject; eauto. intros (m1' & APPD' & WINJ'). exists m1'. split; eauto.
    apply winject_to_inject; auto. unfold mem_inj_val. intros.
    exploit mem_delta_apply_keeps_perm; eauto. congruence.
    { destruct (Pos.ltb_spec0 b1 (Mem.nextblock m0)); auto. exfalso. assert ((meminj_public ge) b1 = None).
      { eapply NALLOC. lia. }
      congruence.
    }
    intros PERM0. pose proof H as INJPUB. unfold meminj_public in H. des_ifs. rename Heq into INV, Heq0 into ISPUB.
    rename b2 into b1. destruct (mem_delta_unchanged_or_changed d b1 ofs).
    - exploit mem_delta_unchanged_on. eapply APPD. intros UNCHG1. exploit mem_delta_wf_unchanged_on. eapply APPD'. intros UNCHG2.
      erewrite (Mem.unchanged_on_contents _ _ _ UNCHG1). erewrite (Mem.unchanged_on_contents _ _ _ UNCHG2). all: eauto.
      { inv INJ. inv mi_inj. specialize (mi_memval _ _ _ _ (INCR _ _ _ INJPUB) PERM0).
        eapply loc_first_order_always_memval_inject; eauto.
        exploit FO.
        erewrite INJPUB.
        congruence. eauto. unfold loc_first_order; intros.
        destruct (ZMap.get ofs (Mem.mem_contents m1) !! b1) eqn:MEMV1; try contradiction.
        erewrite (Mem.unchanged_on_contents _ _ _ UNCHG1) in MEMV1; eauto. rewrite MEMV1. auto.
      }
      { eapply mem_delta_unchanged_implies_wf_unchanged; eauto. rewrite Z.add_0_r. auto. }
      { inv WINJ. inv mwi_inj. rewrite <- (Z.add_0_r ofs). eapply mwi_perm; eauto. rewrite Z.add_0_r. auto. }
    - rename H into CHG. exploit mem_delta_changed_only_by_storev. eauto. rewrite INJPUB; ss. eauto. eapply APPD. eapply APPD'. auto.
      { inv WINJ. inv mwi_inj. rewrite <- (Z.add_0_r ofs). eapply mwi_perm; eauto. }
      { exploit FO; eauto. rewrite INJPUB. congruence. }
      intros. rewrite Z.add_0_r, <- x0.
      exploit FO; eauto.
      rewrite INJPUB; ss. intros. unfold loc_first_order in x1.
      destruct (ZMap.get ofs (Mem.mem_contents m1) !! b1); try contradiction. constructor.
  Qed.

  Import Mem.

  Lemma mem_delta_apply_establish_inject_preprocess
        (ge: Senv.t) (k: meminj) m0 m0'
        (INJ: Mem.inject k m0 m0')
        pch pb pofs pv pcp m0''
        (PRE: store pch m0' pb pofs pv pcp = Some m0'')
        (PREB: forall b ofs, (meminj_public ge) b <> Some (pb, ofs))
        (INCR: inject_incr (meminj_public ge) k)
        (NALLOC: meminj_not_alloc (meminj_public ge) m0)
        (d: mem_delta) cp
        (DWF: mem_delta_inj_wf cp (meminj_public ge) d)
        m1
        (APPD: mem_delta_apply d (Some m0) = Some m1)
        (FO: meminj_first_order (meminj_public ge) m1)
    :
    exists m1', (mem_delta_apply_wf ge cp d (Some m0'') = Some m1') /\ (Mem.inject (meminj_public ge) m1 m1').
  Proof.
    exploit inject_implies_winject; eauto. intros WINJ. exploit winject_inj_incr; eauto. clear WINJ; intro WINJ.
    hexploit store_outside_winject. eauto.
    { intros. eapply PREB. rewrite H. eauto. }
    eapply PRE. clear WINJ. intros WINJ.
    exploit mem_delta_apply_preserves_winject. eapply WINJ. eauto. intros (m1' & APPD' & WINJ'). exists m1'. split; eauto.
    apply winject_to_inject; auto. unfold mem_inj_val. intros.
    exploit mem_delta_apply_keeps_perm; eauto. congruence.
    { destruct (Pos.ltb_spec0 b1 (Mem.nextblock m0)); auto. exfalso. assert ((meminj_public ge) b1 = None).
      { eapply NALLOC. lia. }
      congruence.
    }
    intros PERM0. pose proof H as INJPUB. unfold meminj_public in H. des_ifs. rename Heq into INV, Heq0 into ISPUB.
    rename b2 into b1.
    assert (NOT_PRE: b1 <> pb).
    { intros EQ. subst b1. eapply PREB. eapply INJPUB. }
    destruct (mem_delta_unchanged_or_changed d b1 ofs).
    - exploit mem_delta_unchanged_on. eapply APPD. intros UNCHG1. exploit mem_delta_wf_unchanged_on. eapply APPD'. intros UNCHG2.
      erewrite (Mem.unchanged_on_contents _ _ _ UNCHG1). erewrite (Mem.unchanged_on_contents _ _ _ UNCHG2). all: eauto.
      { inv INJ. inv mi_inj0. specialize (mi_memval0 _ _ _ _ (INCR _ _ _ INJPUB) PERM0).
        eapply loc_first_order_always_memval_inject; eauto.
        - exploit FO. erewrite INJPUB. congruence. eauto. unfold loc_first_order; intros. destruct (ZMap.get ofs (Mem.mem_contents m1) !! b1) eqn:MEMV1; try contradiction.
          erewrite (Mem.unchanged_on_contents _ _ _ UNCHG1) in MEMV1; eauto. rewrite MEMV1. auto.
        - erewrite (store_mem_contents _ m0' _ _ _ _ m0''). 2: eapply PRE. rewrite PMap.gso. 2: auto. eauto.
      }
      { eapply mem_delta_unchanged_implies_wf_unchanged; eauto. rewrite Z.add_0_r. auto. }
      { inv WINJ. inv mwi_inj. rewrite <- (Z.add_0_r ofs). eapply mwi_perm; eauto. rewrite Z.add_0_r. auto. }
    - rename H into CHG. exploit mem_delta_changed_only_by_storev. eauto. rewrite INJPUB; ss. eauto. eapply APPD. eapply APPD'. auto.
      { inv WINJ. inv mwi_inj. rewrite <- (Z.add_0_r ofs). eapply mwi_perm; eauto. }
      { exploit FO; eauto. rewrite INJPUB. congruence. }
      intros. rewrite Z.add_0_r, <- x0.
      exploit FO; eauto. rewrite INJPUB; ss. intros. unfold loc_first_order in x1.
      destruct (ZMap.get ofs (Mem.mem_contents m1) !! b1); try contradiction. constructor.
  Qed.

  Lemma mem_delta_apply_establish_inject_preprocess_gen
        (ge: Senv.t) (k: meminj) m0 m0'
        (INJ: Mem.inject k m0 m0')
        pch pb pofs pv pcp m0''
        (PRE: store pch m0' pb pofs pv pcp = Some m0'')
        (PREB: forall b ofs, (meminj_public ge) b <> Some (pb, ofs))
        (INCR: inject_incr (meminj_public ge) k)
        (NALLOC: meminj_not_alloc (meminj_public ge) m0)
        (d: mem_delta) cp
        (DWF: mem_delta_inj_wf cp (meminj_public ge) d)
        m1
        (APPD: mem_delta_apply d (Some m0) = Some m1)
    :
    exists m1', (mem_delta_apply_wf ge cp d (Some m0'') = Some m1') /\
             ((meminj_first_order (meminj_public ge) m1) -> Mem.inject (meminj_public ge) m1 m1').
  Proof.
    exploit inject_implies_winject; eauto. intros WINJ. exploit winject_inj_incr; eauto. clear WINJ; intro WINJ.
    hexploit store_outside_winject. eauto.
    { intros. eapply PREB. rewrite H. eauto. }
    eapply PRE. clear WINJ. intros WINJ.
    exploit mem_delta_apply_preserves_winject. eapply WINJ. eauto. intros (m1' & APPD' & WINJ'). exists m1'. split; eauto.
    intros FO.
    apply winject_to_inject; auto. unfold mem_inj_val. intros.
    exploit mem_delta_apply_keeps_perm; eauto. congruence.
    { destruct (Pos.ltb_spec0 b1 (Mem.nextblock m0)); auto. exfalso. assert ((meminj_public ge) b1 = None).
      { eapply NALLOC. lia. }
      congruence.
    }
    intros PERM0. pose proof H as INJPUB. unfold meminj_public in H. des_ifs. rename Heq into INV, Heq0 into ISPUB.
    rename b2 into b1.
    assert (NOT_PRE: b1 <> pb).
    { intros EQ. subst b1. eapply PREB. eapply INJPUB. }
    destruct (mem_delta_unchanged_or_changed d b1 ofs).
    - exploit mem_delta_unchanged_on. eapply APPD. intros UNCHG1. exploit mem_delta_wf_unchanged_on. eapply APPD'. intros UNCHG2.
      erewrite (Mem.unchanged_on_contents _ _ _ UNCHG1). erewrite (Mem.unchanged_on_contents _ _ _ UNCHG2). all: eauto.
      { inv INJ. inv mi_inj0. specialize (mi_memval0 _ _ _ _ (INCR _ _ _ INJPUB) PERM0).
        eapply loc_first_order_always_memval_inject; eauto.
        - exploit FO. erewrite INJPUB. congruence. eauto. unfold loc_first_order; intros. destruct (ZMap.get ofs (Mem.mem_contents m1) !! b1) eqn:MEMV1; try contradiction.
          erewrite (Mem.unchanged_on_contents _ _ _ UNCHG1) in MEMV1; eauto. rewrite MEMV1. auto.
        - erewrite (store_mem_contents _ m0' _ _ _ _ m0''). 2: eapply PRE. rewrite PMap.gso. 2: auto. eauto.
      }
      { eapply mem_delta_unchanged_implies_wf_unchanged; eauto. rewrite Z.add_0_r. auto. }
      { inv WINJ. inv mwi_inj. rewrite <- (Z.add_0_r ofs). eapply mwi_perm; eauto. rewrite Z.add_0_r. auto. }
    - rename H into CHG. exploit mem_delta_changed_only_by_storev. eauto. rewrite INJPUB; ss. eauto. eapply APPD. eapply APPD'. auto.
      { inv WINJ. inv mwi_inj. rewrite <- (Z.add_0_r ofs). eapply mwi_perm; eauto. }
      { exploit FO; eauto. rewrite INJPUB. congruence. }
      intros. rewrite Z.add_0_r, <- x0.
      exploit FO; eauto. rewrite INJPUB; ss. intros. unfold loc_first_order in x1.
      destruct (ZMap.get ofs (Mem.mem_contents m1) !! b1); try contradiction. constructor.
  Qed.

End PROOFS.
