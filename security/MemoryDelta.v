Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.
Require Import MemoryWeak.

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

  (* Definition mem_delta_apply (d: mem_delta) (m0: mem) : option mem := *)
  (*   fold_right (fun data om => *)
  (*                 match data with *)
  (*                 | mem_delta_kind_store d => mem_delta_apply_store om d *)
  (*                 | mem_delta_kind_bytes d => mem_delta_apply_bytes om d *)
  (*                 | mem_delta_kind_alloc d => mem_delta_apply_alloc om d *)
  (*                 | mem_delta_kind_free d => mem_delta_apply_free om d *)
  (*                 end *)
  (*              ) (Some m0) d. *)

  (* Lemma mem_delta_apply_cons *)
  (*       d m0 m k *)
  (*       (MEM: mem_delta_apply d m0 = Some m) *)
  (*   : *)
  (*   mem_delta_apply (k :: d) m0 =  *)
  (*     match k with *)
  (*     | mem_delta_kind_store dd => mem_delta_apply_store (Some m) dd *)
  (*     | mem_delta_kind_bytes dd => mem_delta_apply_bytes (Some m) dd *)
  (*     | mem_delta_kind_alloc dd => mem_delta_apply_alloc (Some m) dd *)
  (*     | mem_delta_kind_free dd => mem_delta_apply_free (Some m) dd *)
  (*     end. *)
  (* Proof. simpl. rewrite MEM. auto. Qed. *)

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

  (* Lemma mem_delta_apply_eq *)
  (*       d m0 *)
  (*   : *)
  (*   mem_delta_apply d m0 = mem_delta_apply_left (rev d) (Some m0). *)
  (* Proof. *)
  (*   rewrite <- (rev_involutive d) at 1. unfold mem_delta_apply, mem_delta_apply_left. rewrite fold_left_rev_right. f_equal. *)
  (* Qed. *)

  (* Definition mem_delta_apply_inj (j: meminj) (d: mem_delta) (m0: mem) : option mem := *)
  (*   fold_right (fun data om => *)
  (*                 match data with *)
  (*                 | mem_delta_kind_store (ch, b, ofs, v, cp) => *)
  (*                     match j b with *)
  (*                     | Some (b', ofsd) => *)
  (*                         mem_delta_apply_store om (ch, b', (ofs + ofsd)%Z, v, cp) *)
  (*                     | None => om *)
  (*                     end *)
  (*                 | _ => om *)
  (*                 end) (Some m0) d. *)

  (* Lemma mem_delta_apply_inj_cons *)
  (*       j d m0 m k *)
  (*       (MEM: mem_delta_apply_inj j d m0 = Some m) *)
  (*   : *)
  (*   mem_delta_apply_inj j (k :: d) m0 =  *)
  (*     match k with *)
  (*     | mem_delta_kind_store (ch, b, ofs, v, cp) => *)
  (*         match j b with Some (b', ofsd) => mem_delta_apply_store (Some m) (ch, b', (ofs + ofsd)%Z, v, cp) | None => (Some m) end *)
  (*     | mem_delta_kind_bytes dd *)
  (*     | mem_delta_kind_alloc dd *)
  (*     | mem_delta_kind_free dd => Some m *)
  (*     end. *)
  (* Proof. simpl. rewrite MEM. auto. Qed. *)

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

  (* Lemma mem_delta_apply_inj_eq *)
  (*       j d m0 *)
  (*   : *)
  (*   mem_delta_apply_inj j d m0 = mem_delta_apply_inj_left j (rev d) (Some m0). *)
  (* Proof. *)
  (*   rewrite <- (rev_involutive d) at 1. unfold mem_delta_apply_inj, mem_delta_apply_inj_left. rewrite fold_left_rev_right. f_equal. *)
  (* Qed. *)


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

  (* Definition mem_delta_inj_store_fo (j: meminj) (data: mem_delta_store): Prop := *)
  (*   let '(ch, b, ofs, v, cp) := data in *)
  (*   match j b with *)
  (*   | Some _ => Forall (fun mv => match mv with | Byte bt => True | _ => False end) (encode_val ch v) *)
  (*   | None => True *)
  (*   end. *)

  (* Definition mem_delta_inj_fo (j: meminj) (d: mem_delta): Prop := *)
  (*   Forall (fun data => *)
  (*             match data with *)
  (*             | mem_delta_kind_store d => mem_delta_inj_store_fo j d *)
  (*             | _ => True *)
  (*             end) d. *)


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








  Mem.unchanged_on_contents:
  forall (P : block -> Z -> Prop) (m_before m_after : mem),
  Mem.unchanged_on P m_before m_after ->
  forall (b : block) (ofs : Z), P b ofs -> Mem.perm m_before b ofs Cur Readable -> ZMap.get ofs (Mem.mem_contents m_after) !! b = ZMap.get ofs (Mem.mem_contents m_before) !! b

    mi_memval : forall (b1 : block) (ofs : Z) (b2 : block) (delta : Z),
                f b1 = Some (b2, delta) -> Mem.perm m1 b1 ofs Cur Readable -> memval_inject f (ZMap.get ofs (Mem.mem_contents m1) !! b1) (ZMap.get (ofs + delta) (Mem.mem_contents m2) !! b2) }.


Mem.load_store_overlap:
  forall (chunk : memory_chunk) (m1 : mem) (b : block) (ofs : Z) (v : val) (cp : compartment) (m2 : mem) (chunk' : memory_chunk) (ofs' : Z) (cp' : option compartment) (v' : val),
  Mem.store chunk m1 b ofs v cp = Some m2 ->
  Mem.load chunk' m2 b ofs' cp' = Some v' ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  exists (mv1 : memval) (mvl : list memval) (mv1' : memval) (mvl' : list memval),
    shape_encoding chunk v (mv1 :: mvl) /\ shape_decoding chunk' (mv1' :: mvl') v' /\ (ofs' = ofs /\ mv1' = mv1 \/ ofs' > ofs /\ In mv1' mvl \/ ofs' < ofs /\ In mv1 mvl')



  (* Properties *)
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

  Lemma mem_delta_apply_preserves_full
        (k j: meminj) m_i m0'
        (INJ0: Mem.inject k m_i m0')
        (INCR: inject_incr j k)
        (d_pre d_post: mem_delta)
        (DWFPRE: mem_delta_inj_wf j d_pre)
        (DWFPOST: mem_delta_inj_wf j d_post)
        m_m
        (APPDPRE: mem_delta_apply_left d_pre (Some m_i) = Some m_m)
        (WINJ: mem_weak_inject j m_m m0')
        m_f
        (APPDPOST: mem_delta_apply_left d_post (Some m_m) = Some m_f)
        (MFO: meminj_first_order j m_f)
    :
    exists m1', (mem_delta_apply_inj j (d_pre ++ d_post) m0' = Some m1') /\ (Mem.inject j m_f m1').
  Proof.



    rewrite mem_delta_apply_eq in APPD. rewrite mem_delta_apply_inj_eq. rewrite mem_delta_inj_wf_rev in DWF. remember (rev d) as rd. clear d Heqrd. rename rd into d.
    revert m0 m0' INJ0 DWF APPD. induction d; intros.
    { unfold mem_delta_apply_inj_left. simpl. exists m0'. split; auto. unfold mem_delta_apply_left in APPD. simpl in APPD. inv APPD. auto. }
    inv DWF. rename H1 into DWF1, H2 into DWF0.
    rewrite mem_delta_apply_left_cons in APPD. rewrite mem_delta_apply_inj_left_cons.

    


    
    revert DWF DFO m1 APPD. induction d; simpl; intros.
    { inv APPD. exists m0'. split; auto. }
    inv DWF. rename H1 into DWF1, H2 into DWF0. inv DFO. rename H1 into DFO1, H2 into DFO0.
    destruct (mem_delta_apply d m0) eqn:DAM.
    2:{ destruct a;
        [rewrite mem_delta_apply_store_none in APPD; inv APPD
        | rewrite mem_delta_apply_bytes_none in APPD; inv APPD
        | rewrite mem_delta_apply_alloc_none in APPD; inv APPD
        | rewrite mem_delta_apply_free_none in APPD; inv APPD].
    }
    rename m into m_i.
    specialize (IHd DWF0 DFO0 _ (eq_refl)). destruct IHd as (m_i' & DAM' & INJ_I).
    rewrite DAM'.
    destruct a.
    - destruct d0 as ((((ch & b) & ofs) & v) & cp). simpl in *.
      destruct (j b) eqn:JB.
      + destruct p as (b' & ofs'). eapply Mem.store_mapped_inject; eauto.
        clear - DFO1. destruct v; auto. exfalso. simpl in *. destruct Archi.ptr64.
        * destruct ch; simpl in *; try (inv DFO1; contradiction).
        * destruct ch; simpl in *; try (inv DFO1; contradiction).
      + exists m_i'; split; auto. eapply Mem.store_unmapped_inject; eauto.
    - destruct d0 as (((b & ofs) & mvs) & cp). simpl in *.
      exists m_i'; split; auto. eapply Mem.storebytes_unmapped_inject; eauto.
    - destruct d0 as ((cp & lo) & hi). simpl in *.
      exists m_i'; split; auto. destruct (Mem.alloc m_i cp lo hi) eqn:ALLOC. simpl in *. inv APPD.
      eapply alloc_left_unmapped_inject_keep; eauto.
    - destruct d0 as (((b & lo) & hi) & cp). simpl in *.
      exists m_i'; split; auto. eapply Mem.free_left_inject; eauto.
  Qed.

  Lemma val_inject_incr_inv
        f f' v v'
        (INCR: inject_incr f f')
        (INJ: Val.inject f' v v')
    :
    Val.inject f v v'.
  Proof.
    inv INJ; auto. eapply Val.inject_ptr; auto.
val_inject_incr: forall (f1 f2 : meminj) (v v' : val), inject_incr f1 f2 -> Val.inject f1 v v' -> Val.inject f2 v v'

  Lemma mem_inject_incr
        f f' m m'
        (INCR: inject_incr f f')
        (INJ: Mem.inject f' m m')
    :
    Mem.inject f m m'.
  Proof.
    unfold Mem.inject in *. inv INJ. split; eauto.
    2:{ intros. specialize (mi_freeblocks _ H). unfold inject_incr in INCR.
        destruct (f b) eqn:FB; auto. destruct p. specialize (INCR _ _ _ FB).
        rewrite INCR in mi_freeblocks. inv mi_freeblocks.
    }
    2:{ clear - INCR mi_no_overlap. unfold Mem.meminj_no_overlap in *. intros.
        exploit mi_no_overlap; eauto.
    }
    clear - INCR mi_inj. inv mi_inj. split; eauto. intros. exploit mi_memval; eauto. intros.
    eapply memval_inject_incr; eauto.
    `
    
val_inject_incr: forall (f1 f2 : meminj) (v v' : val), inject_incr f1 f2 -> Val.inject f1 v v' -> Val.inject f2 v v'
Unusedglobproof.regset_inject_incr: forall (f f' : meminj) (rs rs' : RTL.regset), Unusedglobproof.regset_inject f rs rs' -> inject_incr f f' -> Unusedglobproof.regset_inject f' rs rs'
memval_inject_incr: forall (f f' : meminj) (v1 v2 : memval), memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2
Stackingproof.agree_regs_inject_incr: forall (j : meminj) (ls : Linear.locset) (rs : Mach.regset) (j' : meminj), Stackingproof.agree_regs j ls rs -> inject_incr j j' -> Stackingproof.agree_regs j' ls rs
Cminorgenproof.match_temps_invariant: forall (f f' : meminj) (le : Csharpminor.temp_env) (te : Cminor.env), Cminorgenproof.match_temps f le te -> inject_incr f f' -> Cminorgenproof.match_temps f' le te
val_inject_list_incr: forall (f1 f2 : meminj) (vl vl' : list val), inject_incr f1 f2 -> Val.inject_list f1 vl vl' -> Val.inject_list f2 vl vl'

  Lemma mem_delta_apply_preserves_inj
        (j: meminj) m0 m0'
        (INJ0: Mem.inject j m0 m0')
        (d: mem_delta)
        (DWF: mem_delta_inj_wf j d)
        (DFO: mem_delta_inj_fo j d)
        m1
        (APPD: mem_delta_apply d m0 = Some m1)
    :
    exists m1', (mem_delta_apply_inj j d m0' = Some m1') /\ (Mem.inject j m1 m1').
  Proof.
    revert DWF DFO m1 APPD. induction d; simpl; intros.
    { inv APPD. exists m0'. split; auto. }
    inv DWF. rename H1 into DWF1, H2 into DWF0. inv DFO. rename H1 into DFO1, H2 into DFO0.
    destruct (mem_delta_apply d m0) eqn:DAM.
    2:{ destruct a;
        [rewrite mem_delta_apply_store_none in APPD; inv APPD
        | rewrite mem_delta_apply_bytes_none in APPD; inv APPD
        | rewrite mem_delta_apply_alloc_none in APPD; inv APPD
        | rewrite mem_delta_apply_free_none in APPD; inv APPD].
    }
    rename m into m_i.
    specialize (IHd DWF0 DFO0 _ (eq_refl)). destruct IHd as (m_i' & DAM' & INJ_I).
    rewrite DAM'.
    destruct a.
    - destruct d0 as ((((ch & b) & ofs) & v) & cp). simpl in *.
      destruct (j b) eqn:JB.
      + destruct p as (b' & ofs'). eapply Mem.store_mapped_inject; eauto.
        clear - DFO1. destruct v; auto. exfalso. simpl in *. destruct Archi.ptr64.
        * destruct ch; simpl in *; try (inv DFO1; contradiction).
        * destruct ch; simpl in *; try (inv DFO1; contradiction).
      + exists m_i'; split; auto. eapply Mem.store_unmapped_inject; eauto.
    - destruct d0 as (((b & ofs) & mvs) & cp). simpl in *.
      exists m_i'; split; auto. eapply Mem.storebytes_unmapped_inject; eauto.
    - destruct d0 as ((cp & lo) & hi). simpl in *.
      exists m_i'; split; auto. destruct (Mem.alloc m_i cp lo hi) eqn:ALLOC. simpl in *. inv APPD.
      eapply alloc_left_unmapped_inject_keep; eauto.
    - destruct d0 as (((b & lo) & hi) & cp). simpl in *.
      exists m_i'; split; auto. eapply Mem.free_left_inject; eauto.
  Qed.

  Definition meminj_first_order (j: meminj) (m: mem) :=
    forall b ofs, (j b <> None) -> (Mem.perm m b ofs Cur Readable) -> loc_first_order m b ofs.

  Lemma mem_delta_apply_preserves_inj_incr
        (j k: meminj) m0 m0'
        (INCR: inject_incr j k)
        (INJ0: Mem.inject k m0 m0')
        (d: mem_delta)
        (DWF: mem_delta_inj_wf j d)
        (DFO: mem_delta_inj_fo j d)
        m1
        (APPD: mem_delta_apply d m0 = Some m1)
        (MIFO: meminj_first_order j m1)
    :
    exists m1', (mem_delta_apply_inj j d m0' = Some m1') /\ (Mem.inject j m1 m1').
  Proof.
    revert DWF DFO m1 APPD MIFO. induction d; simpl; intros.
    { inv APPD. exists m0'. split; auto. admit. (* MIFO *) }
    inv DWF. rename H1 into DWF1, H2 into DWF0. inv DFO. rename H1 into DFO1, H2 into DFO0.
    destruct (mem_delta_apply d m0) eqn:DAM.
    2:{ destruct a;
        [rewrite mem_delta_apply_store_none in APPD; inv APPD
        | rewrite mem_delta_apply_bytes_none in APPD; inv APPD
        | rewrite mem_delta_apply_alloc_none in APPD; inv APPD
        | rewrite mem_delta_apply_free_none in APPD; inv APPD].
    }
    rename m into m_i.
    specialize (IHd DWF0 DFO0 _ (eq_refl)). destruct IHd as (m_i' & DAM' & INJ_I).
    { unfold meminj_first_order in *. intros. rename d into deltas.
      specialize (MIFO _ ofs H). exploit MIFO; clear MIFO.
      { destruct a; simpl in *.
        - unfold mem_delta_apply_store in APPD. destruct d as [[[[ch0 b0] ofs0] v0] cp0].
          eapply Mem.perm_store_1; eauto.
        - unfold mem_delta_apply_bytes in APPD. destruct d as [[[b0 ofs0] mvs0] cp0].
          eapply Mem.perm_storebytes_1; eauto.
        - unfold mem_delta_apply_alloc in APPD. destruct d as [[cp0 lo0] hi0].
          destruct (Mem.alloc m_i cp0 lo0 hi0) eqn:CASES. inv APPD.
          eapply Mem.perm_alloc_1; eauto. 
        - unfold mem_delta_apply_free in APPD. destruct d as [[[b0 lo0] hi0] cp0].
          eapply Mem.perm_free_1; eauto. left. intros EQ. subst. rewrite DWF1 in H. congruence.
      }
      intros MIFO. clear H0.
      { destruct a; simpl in *.
        - unfold mem_delta_apply_store in APPD. destruct d as [[[[ch0 b0] ofs0] v0] cp0].
          destruct (Pos.eqb_spec b b0).
          + subst b0. unfold mem_delta_inj_store_fo in DFO1.
            destruct (j b) eqn:JB. 2: congruence. clear H. destruct p.
            unfold loc_first_order in *. clear MIFO APPD.
            

            
Mem.store_mem_contents:
  forall (chunk : memory_chunk) (m1 : mem) (b : block) (ofs : Z) (v : val) 
    (cp : compartment) (m2 : mem),
  Mem.store chunk m1 b ofs v cp = Some m2 ->
  Mem.mem_contents m2 =
  PMap.set b (Mem.setN (encode_val chunk v) ofs (Mem.mem_contents m1) !! b) (Mem.mem_contents m1)


          
          eapply Mem.perm_store_1; eauto.
        - unfold mem_delta_apply_bytes in APPD. destruct d as [[[b0 ofs0] mvs0] cp0].
          eapply Mem.perm_storebytes_1; eauto.
        - unfold mem_delta_apply_alloc in APPD. destruct d as [[cp0 lo0] hi0].
          destruct (Mem.alloc m_i cp0 lo0 hi0) eqn:CASES. inv APPD.
          eapply Mem.perm_alloc_1; eauto. 
        - unfold mem_delta_apply_free in APPD. destruct d as [[[b0 lo0] hi0] cp0].
          eapply Mem.perm_free_1; eauto. left. intros EQ. subst. rewrite DWF1 in H. congruence.
      }



      
    rewrite DAM'.
    destruct a.
    - destruct d0 as ((((ch & b) & ofs) & v) & cp). simpl in *.
      destruct (j b) eqn:JB.
      + destruct p as (b' & ofs'). eapply Mem.store_mapped_inject; eauto.
        clear - DFO1. destruct v; auto. exfalso. simpl in *. destruct Archi.ptr64.
        * destruct ch; simpl in *; try (inv DFO1; contradiction).
        * destruct ch; simpl in *; try (inv DFO1; contradiction).
      + exists m_i'; split; auto. eapply Mem.store_unmapped_inject; eauto.
    - destruct d0 as (((b & ofs) & mvs) & cp). simpl in *.
      exists m_i'; split; auto. eapply Mem.storebytes_unmapped_inject; eauto.
    - destruct d0 as ((cp & lo) & hi). simpl in *.
      exists m_i'; split; auto. destruct (Mem.alloc m_i cp lo hi) eqn:ALLOC. simpl in *. inv APPD.
      eapply alloc_left_unmapped_inject_keep; eauto.
    - destruct d0 as (((b & lo) & hi) & cp). simpl in *.
      exists m_i'; split; auto. eapply Mem.free_left_inject; eauto.
  Qed.

  (* Memory injection for public global symbols: visible for external calls *)
  Definition meminj_public (ge: Senv.t): meminj :=
    fun b => match Senv.invert_symbol ge b with
          | Some id => if Senv.public_symbol ge id then Some (b, 0%Z) else None
          | None => None
          end.


        (DFO: mem_delta_inj_fo j d)
                            visible_fo_if_unknown ef ge m vargs ->
    | None => visible_fo ge m (sig_args sg) args
visible_fo =
fun (ge : Senv.t) (m : mem) (tys : list typ) (args : list val) =>
public_first_order ge m /\ vals_public ge tys args
     : Senv.t -> mem -> list typ -> list val -> Prop
public_first_order =
fun (ge : Senv.t) (m : mem) =>
forall (id : ident) (b : block) (ofs : Z),
Senv.public_symbol ge id = true ->
Senv.find_symbol ge id = Some b -> Mem.perm m b ofs Cur Readable -> loc_first_order m b ofs
     : Senv.t -> mem -> Prop

  (* TODO: this is false --- pointers can mess around *)
(*   Lemma val_inject_incr_inv *)
(*         f f' v v' *)
(*         (INCR: inject_incr f f') *)
(*         (INJ: Val.inject f' v v') *)
(*     : *)
(*     Val.inject f v v'. *)
(*   Proof. *)
(*     inv INJ; auto. eapply Val.inject_ptr; auto. *)
(* val_inject_incr: forall (f1 f2 : meminj) (v v' : val), inject_incr f1 f2 -> Val.inject f1 v v' -> Val.inject f2 v v' *)

  Lemma mem_inject_incr
        f f' m m'
        (INCR: inject_incr f f')
        (INJ: Mem.inject f' m m')
    :
    Mem.inject f m m'.
  Proof.
    unfold Mem.inject in *. inv INJ. split; eauto.
    2:{ intros. specialize (mi_freeblocks _ H). unfold inject_incr in INCR.
        destruct (f b) eqn:FB; auto. destruct p. specialize (INCR _ _ _ FB).
        rewrite INCR in mi_freeblocks. inv mi_freeblocks.
    }
    2:{ clear - INCR mi_no_overlap. unfold Mem.meminj_no_overlap in *. intros.
        exploit mi_no_overlap; eauto.
    }
    clear - INCR mi_inj. inv mi_inj. split; eauto. intros. exploit mi_memval; eauto. intros.
    eapply memval_inject_incr; eauto.
    `
    
val_inject_incr: forall (f1 f2 : meminj) (v v' : val), inject_incr f1 f2 -> Val.inject f1 v v' -> Val.inject f2 v v'
Unusedglobproof.regset_inject_incr: forall (f f' : meminj) (rs rs' : RTL.regset), Unusedglobproof.regset_inject f rs rs' -> inject_incr f f' -> Unusedglobproof.regset_inject f' rs rs'
memval_inject_incr: forall (f f' : meminj) (v1 v2 : memval), memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2
Stackingproof.agree_regs_inject_incr: forall (j : meminj) (ls : Linear.locset) (rs : Mach.regset) (j' : meminj), Stackingproof.agree_regs j ls rs -> inject_incr j j' -> Stackingproof.agree_regs j' ls rs
Cminorgenproof.match_temps_invariant: forall (f f' : meminj) (le : Csharpminor.temp_env) (te : Cminor.env), Cminorgenproof.match_temps f le te -> inject_incr f f' -> Cminorgenproof.match_temps f' le te
val_inject_list_incr: forall (f1 f2 : meminj) (vl vl' : list val), inject_incr f1 f2 -> Val.inject_list f1 vl vl' -> Val.inject_list f2 vl vl'


End MEMDELTA.
