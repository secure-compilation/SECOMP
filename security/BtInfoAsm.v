Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import riscV.Machregs.
Require Import riscV.Asm.
Require Import Complements.
Require Import MemoryWeak MemoryDelta.
Require Import BtBasics.


(* Section MEMDELTA. *)

(*   (* Data to get injection by invoking correct Mem.store: inj + (apply delta) = inj *) *)
(*   Definition mem_delta_store := (memory_chunk * block * Z * val * compartment)%type. *)
(*   Definition mem_delta_bytes := (block * Z * (list memval) * compartment)%type. *)
(*   Definition mem_delta_alloc := (compartment * Z * Z)%type. *)
(*   Definition mem_delta_free := (block * Z * Z * compartment)%type. *)

(*   Inductive mem_delta_kind := *)
(*   | mem_delta_kind_store (d: mem_delta_store) *)
(*   | mem_delta_kind_bytes (d: mem_delta_bytes) *)
(*   | mem_delta_kind_alloc (d: mem_delta_alloc) *)
(*   | mem_delta_kind_free (d: mem_delta_free) *)
(*   . *)

(*   (* Definition mem_delta_key := (block * Z)%type. *) *)
(*   (* Definition mem_delta := list (mem_delta_key * mem_delta_kind). *) *)
(*   Definition mem_delta := list mem_delta_kind. *)

(*   (* Definition mem_delta_key_eqb (k1 k2: mem_delta_key): bool := *) *)
(*   (*   let (b1, ofs1) := k1 in let (b2, ofs2) := k2 in andb (Pos.eqb b1 b2) (Z.eqb ofs1 ofs2). *) *)

(*   (* Definition mem_delta_get (d: mem_delta) (b: block) (ofs: Z): option mem_delta_kind := *) *)
(*   (*   match find (fun '(k, data) => mem_delta_key_eqb k (b, ofs)) d with | Some (k, data) => Some data | None => None end. *) *)

(*   Definition mem_delta_apply_store (om: option mem) (d: mem_delta_store): option mem := *)
(*     let '(ch, b, ofs, v, cp) := d in *)
(*     match om with *)
(*     | Some m => Mem.store ch m b ofs v cp *)
(*     | None => None *)
(*     end. *)

(*   Lemma mem_delta_apply_store_none *)
(*         d *)
(*     : *)
(*     mem_delta_apply_store None d = None. *)
(*   Proof. unfold mem_delta_apply_store. destruct d as [[[[d0 d1] d2] d3] d4]. auto. Qed. *)

(*   Definition mem_delta_apply_bytes (om: option mem) (d: mem_delta_bytes): option mem := *)
(*     let '(b, ofs, mvs, cp) := d in *)
(*     match om with *)
(*     | Some m => Mem.storebytes m b ofs mvs cp *)
(*     | None => None *)
(*     end. *)

(*   Lemma mem_delta_apply_bytes_none *)
(*         d *)
(*     : *)
(*     mem_delta_apply_bytes None d = None. *)
(*   Proof. unfold mem_delta_apply_bytes. destruct d as [[[d0 d1] d2] d3]. auto. Qed. *)

(*   Definition mem_delta_apply_alloc (om: option mem) (d: mem_delta_alloc): option mem := *)
(*     let '(cp, lo, hi) := d in *)
(*     match om with *)
(*     | Some m => Some (fst (Mem.alloc m cp lo hi)) *)
(*     | None => None *)
(*     end. *)

(*   Lemma mem_delta_apply_alloc_none *)
(*         d *)
(*     : *)
(*     mem_delta_apply_alloc None d = None. *)
(*   Proof. unfold mem_delta_apply_alloc. destruct d as [[d0 d1] d2]. auto. Qed. *)

(*   Definition mem_delta_apply_free (om: option mem) (d: mem_delta_free): option mem := *)
(*     let '(b, lo, hi, cp) := d in *)
(*     match om with *)
(*     | Some m => Mem.free m b lo hi cp *)
(*     | None => None *)
(*     end. *)

(*   Lemma mem_delta_apply_free_none *)
(*         d *)
(*     : *)
(*     mem_delta_apply_free None d = None. *)
(*   Proof. unfold mem_delta_apply_free. destruct d as [[[d0 d1] d2] d3]. auto. Qed. *)

(*   Definition mem_delta_apply (d: mem_delta) (m0: mem) : option mem := *)
(*     fold_right (fun data om => *)
(*                   match data with *)
(*                   | mem_delta_kind_store d => mem_delta_apply_store om d *)
(*                   | mem_delta_kind_bytes d => mem_delta_apply_bytes om d *)
(*                   | mem_delta_kind_alloc d => mem_delta_apply_alloc om d *)
(*                   | mem_delta_kind_free d => mem_delta_apply_free om d *)
(*                   end *)
(*                ) (Some m0) d. *)

(*   Lemma mem_delta_apply_cons *)
(*         d m0 m k *)
(*         (MEM: mem_delta_apply d m0 = Some m) *)
(*     : *)
(*     mem_delta_apply (k :: d) m0 =  *)
(*       match k with *)
(*       | mem_delta_kind_store dd => mem_delta_apply_store (Some m) dd *)
(*       | mem_delta_kind_bytes dd => mem_delta_apply_bytes (Some m) dd *)
(*       | mem_delta_kind_alloc dd => mem_delta_apply_alloc (Some m) dd *)
(*       | mem_delta_kind_free dd => mem_delta_apply_free (Some m) dd *)
(*       end. *)
(*   Proof. simpl. rewrite MEM. auto. Qed. *)

(*   Definition mem_delta_apply_left (d: mem_delta) (om0: option mem) : option mem := *)
(*     fold_left (fun om data => *)
(*                  match data with *)
(*                  | mem_delta_kind_store d => mem_delta_apply_store om d *)
(*                  | mem_delta_kind_bytes d => mem_delta_apply_bytes om d *)
(*                  | mem_delta_kind_alloc d => mem_delta_apply_alloc om d *)
(*                  | mem_delta_kind_free d => mem_delta_apply_free om d *)
(*                  end *)
(*               ) d om0. *)

(*   Lemma mem_delta_apply_left_cons *)
(*         d m0 k *)
(*     : *)
(*     mem_delta_apply_left (k :: d) m0 = *)
(*       match k with *)
(*       | mem_delta_kind_store dd => mem_delta_apply_left d (mem_delta_apply_store (m0) dd) *)
(*       | mem_delta_kind_bytes dd => mem_delta_apply_left d (mem_delta_apply_bytes (m0) dd) *)
(*       | mem_delta_kind_alloc dd => mem_delta_apply_left d (mem_delta_apply_alloc (m0) dd) *)
(*       | mem_delta_kind_free dd => mem_delta_apply_left d (mem_delta_apply_free (m0) dd) *)
(*       end. *)
(*   Proof. simpl. destruct k; auto. Qed. *)

(*   Lemma mem_delta_apply_left_app *)
(*         d0 d1 m0 *)
(*     : *)
(*     mem_delta_apply_left (d0 ++ d1) m0 = mem_delta_apply_left d1 (mem_delta_apply_left d0 m0). *)
(*   Proof. *)
(*     revert d1 m0. induction d0; intros. *)
(*     { simpl. auto. } *)
(*     rewrite <- app_comm_cons. rewrite ! mem_delta_apply_left_cons. destruct a; auto. *)
(*   Qed. *)

(*   Lemma mem_delta_apply_eq *)
(*         d m0 *)
(*     : *)
(*     mem_delta_apply d m0 = mem_delta_apply_left (rev d) (Some m0). *)
(*   Proof. *)
(*     rewrite <- (rev_involutive d) at 1. unfold mem_delta_apply, mem_delta_apply_left. rewrite fold_left_rev_right. f_equal. *)
(*   Qed. *)

(*   (* Delta and injection relation *) *)
(*   Definition mem_delta_kind_inj_wf (j: meminj): mem_delta_kind -> Prop := *)
(*     fun data => *)
(*       match data with *)
(*       | mem_delta_kind_bytes (b, ofs, mvs, cp) => (j b) = None *)
(*       | mem_delta_kind_free (b, lo, hi, cp) => (j b) = None *)
(*       | _ => True *)
(*       end. *)

(*   Definition mem_delta_inj_wf (j: meminj): mem_delta -> Prop := *)
(*     fun d => Forall (fun data => mem_delta_kind_inj_wf j data) d. *)

(*   Lemma mem_delta_inj_wf_rev *)
(*         j d *)
(*     : *)
(*     mem_delta_inj_wf j d <-> mem_delta_inj_wf j (rev d). *)
(*   Proof. *)
(*     unfold mem_delta_inj_wf. split; intros. apply Forall_rev; auto. rewrite <- rev_involutive. apply Forall_rev. auto. *)
(*   Qed. *)

(*   Definition meminj_first_order (j: meminj) (m: mem) := *)
(*     forall b ofs, (j b <> None) -> (Mem.perm m b ofs Cur Readable) -> loc_first_order m b ofs. *)

(*   (* Definition mem_delta_inj_store_fo (j: meminj) (data: mem_delta_store): Prop := *) *)
(*   (*   let '(ch, b, ofs, v, cp) := data in *) *)
(*   (*   match j b with *) *)
(*   (*   | Some _ => Forall (fun mv => match mv with | Byte bt => True | _ => False end) (encode_val ch v) *) *)
(*   (*   | None => True *) *)
(*   (*   end. *) *)

(*   (* Definition mem_delta_inj_fo (j: meminj) (d: mem_delta): Prop := *) *)
(*   (*   Forall (fun data => *) *)
(*   (*             match data with *) *)
(*   (*             | mem_delta_kind_store d => mem_delta_inj_store_fo j d *) *)
(*   (*             | _ => True *) *)
(*   (*             end) d. *) *)

(*   Definition mem_delta_apply_inj (j: meminj) (d: mem_delta) (m0: mem) : option mem := *)
(*     fold_right (fun data om => *)
(*                   match data with *)
(*                   | mem_delta_kind_store (ch, b, ofs, v, cp) => *)
(*                       match j b with *)
(*                       | Some (b', ofsd) => *)
(*                           mem_delta_apply_store om (ch, b', (ofs + ofsd)%Z, v, cp) *)
(*                       | None => om *)
(*                       end *)
(*                   | _ => om *)
(*                   end) (Some m0) d. *)

(*   Lemma mem_delta_apply_inj_cons *)
(*         j d m0 m k *)
(*         (MEM: mem_delta_apply_inj j d m0 = Some m) *)
(*     : *)
(*     mem_delta_apply_inj j (k :: d) m0 =  *)
(*       match k with *)
(*       | mem_delta_kind_store (ch, b, ofs, v, cp) => *)
(*           match j b with Some (b', ofsd) => mem_delta_apply_store (Some m) (ch, b', (ofs + ofsd)%Z, v, cp) | None => (Some m) end *)
(*       | mem_delta_kind_bytes dd *)
(*       | mem_delta_kind_alloc dd *)
(*       | mem_delta_kind_free dd => Some m *)
(*       end. *)
(*   Proof. simpl. rewrite MEM. auto. Qed. *)

(*   Definition mem_delta_apply_inj_left (j: meminj) (d: mem_delta) (om0: option mem) : option mem := *)
(*     fold_left (fun om data => *)
(*                  match data with *)
(*                  | mem_delta_kind_store (ch, b, ofs, v, cp) => *)
(*                      match j b with *)
(*                      | Some (b', ofsd) => *)
(*                          mem_delta_apply_store om (ch, b', (ofs + ofsd)%Z, v, cp) *)
(*                      | None => om *)
(*                      end *)
(*                  | _ => om *)
(*                  end) d (om0). *)

(*   Lemma mem_delta_apply_inj_left_cons *)
(*         j d m0 k *)
(*     : *)
(*     mem_delta_apply_inj_left j (k :: d) m0 = *)
(*       match k with *)
(*       | mem_delta_kind_store (ch, b, ofs, v, cp) => *)
(*           match j b with *)
(*           | Some (b', ofsd) => *)
(*               mem_delta_apply_inj_left j d (mem_delta_apply_store m0 (ch, b', (ofs + ofsd)%Z, v, cp)) *)
(*           | None => mem_delta_apply_inj_left j d m0 *)
(*           end *)
(*       | mem_delta_kind_bytes dd *)
(*       | mem_delta_kind_alloc dd *)
(*       | mem_delta_kind_free dd => mem_delta_apply_inj_left j d m0 *)
(*       end. *)
(*   Proof. simpl. destruct k; auto. destruct d0 as [[[[a0 a1] a2] a3] a4]. destruct (j a1); auto. destruct p. auto. Qed. *)

(*   Lemma mem_delta_apply_inj_left_app *)
(*         j d0 d1 m0 *)
(*     : *)
(*     mem_delta_apply_inj_left j (d0 ++ d1) m0 = mem_delta_apply_inj_left j d1 (mem_delta_apply_inj_left j d0 m0). *)
(*   Proof. *)
(*     revert j d1 m0. induction d0; intros. *)
(*     { simpl. auto. } *)
(*     rewrite <- app_comm_cons. rewrite ! mem_delta_apply_inj_left_cons. destruct a; auto. *)
(*     { destruct d as [[[[a0 a1] a2] a3] a4]. destruct (j a1); auto. destruct p; auto. } *)
(*   Qed. *)

(*   Lemma mem_delta_apply_inj_eq *)
(*         j d m0 *)
(*     : *)
(*     mem_delta_apply_inj j d m0 = mem_delta_apply_inj_left j (rev d) (Some m0). *)
(*   Proof. *)
(*     rewrite <- (rev_involutive d) at 1. unfold mem_delta_apply_inj, mem_delta_apply_inj_left. rewrite fold_left_rev_right. f_equal. *)
(*   Qed. *)

(*   Lemma alloc_left_unmapped_inject_keep: *)
(*     forall f m1 m2 c lo hi m1' b1, *)
(*       Mem.inject f m1 m2 -> *)
(*       Mem.alloc m1 c lo hi = (m1', b1) -> *)
(*       Mem.inject f m1' m2. *)
(*   Proof. *)
(*     intros. set (f' := fun b => if eq_block b b1 then None else f b). *)
(*     cut (Mem.inject f' m1' m2 /\ inject_incr f f' /\ f' b1 = None /\ (forall b, b <> b1 -> f' b = f b)). *)
(*     { clear - f'. intros (INJ & INCR & _ & _). unfold inject_incr in INCR. *)
(*       assert (f' = f). *)
(*       { eapply Axioms.functional_extensionality. intros x. destruct (eq_block x b1). *)
(*         - subst x. destruct (f b1) eqn:FB. *)
(*           + destruct p. specialize (INCR _ _ _ FB). auto. *)
(*           + subst f'. simpl. rewrite pred_dec_true; auto. *)
(*         - subst f'. simpl. rewrite pred_dec_false; auto. *)
(*       } *)
(*       rewrite <- H. apply INJ. *)
(*     } *)
(*     inversion H. assert (inject_incr f f'). *)
(*     red; unfold f'; intros. destruct (eq_block b b1). subst b. *)
(*     assert (f b1 = None). eauto with mem. congruence. *)
(*     auto. *)
(*     assert (Mem.mem_inj f' m1 m2). *)
(*     inversion mi_inj; constructor; eauto with mem. *)
(*     unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto. *)
(*     unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto. *)
(*     unfold f'; intros. destruct (eq_block b0 b1). congruence. *)
(*     unfold f'; intros. destruct (eq_block b0 b1). congruence. *)
(*     eapply mi_align; eauto. *)
(*     unfold f'; intros. destruct (eq_block b0 b1). congruence. *)
(*     apply memval_inject_incr with f; auto. *)
(*     split. constructor. *)
(*     (* inj *) *)
(*     eapply Mem.alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true. *)
(*     (* freeblocks *) *)
(*     intros. unfold f'. destruct (eq_block b b1). auto. *)
(*     apply mi_freeblocks. red; intro; elim H3. eauto with mem. *)
(*     (* mappedblocks *) *)
(*     unfold f'; intros. destruct (eq_block b b1). congruence. eauto. *)
(*     (* no overlap *) *)
(*     unfold f'; red; intros. *)
(*     destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence. *)
(*     eapply mi_no_overlap. eexact H3. eauto. eauto. *)
(*     exploit Mem.perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto. *)
(*     exploit Mem.perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto. *)
(*     (* representable *) *)
(*     unfold f'; intros. *)
(*     destruct (eq_block b b1); try discriminate. *)
(*     eapply mi_representable; try eassumption. *)
(*     destruct H4; eauto using Mem.perm_alloc_4. *)
(*     (* perm inv *) *)
(*     intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate. *)
(*     exploit mi_perm_inv; eauto. *)
(*     intuition eauto using Mem.perm_alloc_1, Mem.perm_alloc_4. *)
(*     (* incr *) *)
(*     split. auto. *)
(*     (* image *) *)
(*     split. unfold f'; apply dec_eq_true. *)
(*     (* incr *) *)
(*     intros; unfold f'; apply dec_eq_false; auto. *)
(*   Qed. *)

(*   Lemma mem_delta_apply_preserves_full *)
(*         (k j: meminj) m_i m0' *)
(*         (INJ0: Mem.inject k m_i m0') *)
(*         (INCR: inject_incr j k) *)
(*         (d_pre d_post: mem_delta) *)
(*         (DWFPRE: mem_delta_inj_wf j d_pre) *)
(*         (DWFPOST: mem_delta_inj_wf j d_post) *)
(*         m_m *)
(*         (APPDPRE: mem_delta_apply_left d_pre (Some m_i) = Some m_m) *)
(*         (WINJ: mem_weak_inject j m_m m0') *)
(*         m_f *)
(*         (APPDPOST: mem_delta_apply_left d_post (Some m_m) = Some m_f) *)
(*         (MFO: meminj_first_order j m_f) *)
(*     : *)
(*     exists m1', (mem_delta_apply_inj j (d_pre ++ d_post) m0' = Some m1') /\ (Mem.inject j m_f m1'). *)
(*   Proof. *)



(*     rewrite mem_delta_apply_eq in APPD. rewrite mem_delta_apply_inj_eq. rewrite mem_delta_inj_wf_rev in DWF. remember (rev d) as rd. clear d Heqrd. rename rd into d. *)
(*     revert m0 m0' INJ0 DWF APPD. induction d; intros. *)
(*     { unfold mem_delta_apply_inj_left. simpl. exists m0'. split; auto. unfold mem_delta_apply_left in APPD. simpl in APPD. inv APPD. auto. } *)
(*     inv DWF. rename H1 into DWF1, H2 into DWF0. *)
(*     rewrite mem_delta_apply_left_cons in APPD. rewrite mem_delta_apply_inj_left_cons. *)

    


    
(*     revert DWF DFO m1 APPD. induction d; simpl; intros. *)
(*     { inv APPD. exists m0'. split; auto. } *)
(*     inv DWF. rename H1 into DWF1, H2 into DWF0. inv DFO. rename H1 into DFO1, H2 into DFO0. *)
(*     destruct (mem_delta_apply d m0) eqn:DAM. *)
(*     2:{ destruct a; *)
(*         [rewrite mem_delta_apply_store_none in APPD; inv APPD *)
(*         | rewrite mem_delta_apply_bytes_none in APPD; inv APPD *)
(*         | rewrite mem_delta_apply_alloc_none in APPD; inv APPD *)
(*         | rewrite mem_delta_apply_free_none in APPD; inv APPD]. *)
(*     } *)
(*     rename m into m_i. *)
(*     specialize (IHd DWF0 DFO0 _ (eq_refl)). destruct IHd as (m_i' & DAM' & INJ_I). *)
(*     rewrite DAM'. *)
(*     destruct a. *)
(*     - destruct d0 as ((((ch & b) & ofs) & v) & cp). simpl in *. *)
(*       destruct (j b) eqn:JB. *)
(*       + destruct p as (b' & ofs'). eapply Mem.store_mapped_inject; eauto. *)
(*         clear - DFO1. destruct v; auto. exfalso. simpl in *. destruct Archi.ptr64. *)
(*         * destruct ch; simpl in *; try (inv DFO1; contradiction). *)
(*         * destruct ch; simpl in *; try (inv DFO1; contradiction). *)
(*       + exists m_i'; split; auto. eapply Mem.store_unmapped_inject; eauto. *)
(*     - destruct d0 as (((b & ofs) & mvs) & cp). simpl in *. *)
(*       exists m_i'; split; auto. eapply Mem.storebytes_unmapped_inject; eauto. *)
(*     - destruct d0 as ((cp & lo) & hi). simpl in *. *)
(*       exists m_i'; split; auto. destruct (Mem.alloc m_i cp lo hi) eqn:ALLOC. simpl in *. inv APPD. *)
(*       eapply alloc_left_unmapped_inject_keep; eauto. *)
(*     - destruct d0 as (((b & lo) & hi) & cp). simpl in *. *)
(*       exists m_i'; split; auto. eapply Mem.free_left_inject; eauto. *)
(*   Qed. *)

(*   Lemma val_inject_incr_inv *)
(*         f f' v v' *)
(*         (INCR: inject_incr f f') *)
(*         (INJ: Val.inject f' v v') *)
(*     : *)
(*     Val.inject f v v'. *)
(*   Proof. *)
(*     inv INJ; auto. eapply Val.inject_ptr; auto. *)
(* val_inject_incr: forall (f1 f2 : meminj) (v v' : val), inject_incr f1 f2 -> Val.inject f1 v v' -> Val.inject f2 v v' *)

(*   Lemma mem_inject_incr *)
(*         f f' m m' *)
(*         (INCR: inject_incr f f') *)
(*         (INJ: Mem.inject f' m m') *)
(*     : *)
(*     Mem.inject f m m'. *)
(*   Proof. *)
(*     unfold Mem.inject in *. inv INJ. split; eauto. *)
(*     2:{ intros. specialize (mi_freeblocks _ H). unfold inject_incr in INCR. *)
(*         destruct (f b) eqn:FB; auto. destruct p. specialize (INCR _ _ _ FB). *)
(*         rewrite INCR in mi_freeblocks. inv mi_freeblocks. *)
(*     } *)
(*     2:{ clear - INCR mi_no_overlap. unfold Mem.meminj_no_overlap in *. intros. *)
(*         exploit mi_no_overlap; eauto. *)
(*     } *)
(*     clear - INCR mi_inj. inv mi_inj. split; eauto. intros. exploit mi_memval; eauto. intros. *)
(*     eapply memval_inject_incr; eauto. *)
(*     ` *)
    
(* val_inject_incr: forall (f1 f2 : meminj) (v v' : val), inject_incr f1 f2 -> Val.inject f1 v v' -> Val.inject f2 v v' *)
(* Unusedglobproof.regset_inject_incr: forall (f f' : meminj) (rs rs' : RTL.regset), Unusedglobproof.regset_inject f rs rs' -> inject_incr f f' -> Unusedglobproof.regset_inject f' rs rs' *)
(* memval_inject_incr: forall (f f' : meminj) (v1 v2 : memval), memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2 *)
(* Stackingproof.agree_regs_inject_incr: forall (j : meminj) (ls : Linear.locset) (rs : Mach.regset) (j' : meminj), Stackingproof.agree_regs j ls rs -> inject_incr j j' -> Stackingproof.agree_regs j' ls rs *)
(* Cminorgenproof.match_temps_invariant: forall (f f' : meminj) (le : Csharpminor.temp_env) (te : Cminor.env), Cminorgenproof.match_temps f le te -> inject_incr f f' -> Cminorgenproof.match_temps f' le te *)
(* val_inject_list_incr: forall (f1 f2 : meminj) (vl vl' : list val), inject_incr f1 f2 -> Val.inject_list f1 vl vl' -> Val.inject_list f2 vl vl' *)

(*   Lemma mem_delta_apply_preserves_inj *)
(*         (j: meminj) m0 m0' *)
(*         (INJ0: Mem.inject j m0 m0') *)
(*         (d: mem_delta) *)
(*         (DWF: mem_delta_inj_wf j d) *)
(*         (DFO: mem_delta_inj_fo j d) *)
(*         m1 *)
(*         (APPD: mem_delta_apply d m0 = Some m1) *)
(*     : *)
(*     exists m1', (mem_delta_apply_inj j d m0' = Some m1') /\ (Mem.inject j m1 m1'). *)
(*   Proof. *)
(*     revert DWF DFO m1 APPD. induction d; simpl; intros. *)
(*     { inv APPD. exists m0'. split; auto. } *)
(*     inv DWF. rename H1 into DWF1, H2 into DWF0. inv DFO. rename H1 into DFO1, H2 into DFO0. *)
(*     destruct (mem_delta_apply d m0) eqn:DAM. *)
(*     2:{ destruct a; *)
(*         [rewrite mem_delta_apply_store_none in APPD; inv APPD *)
(*         | rewrite mem_delta_apply_bytes_none in APPD; inv APPD *)
(*         | rewrite mem_delta_apply_alloc_none in APPD; inv APPD *)
(*         | rewrite mem_delta_apply_free_none in APPD; inv APPD]. *)
(*     } *)
(*     rename m into m_i. *)
(*     specialize (IHd DWF0 DFO0 _ (eq_refl)). destruct IHd as (m_i' & DAM' & INJ_I). *)
(*     rewrite DAM'. *)
(*     destruct a. *)
(*     - destruct d0 as ((((ch & b) & ofs) & v) & cp). simpl in *. *)
(*       destruct (j b) eqn:JB. *)
(*       + destruct p as (b' & ofs'). eapply Mem.store_mapped_inject; eauto. *)
(*         clear - DFO1. destruct v; auto. exfalso. simpl in *. destruct Archi.ptr64. *)
(*         * destruct ch; simpl in *; try (inv DFO1; contradiction). *)
(*         * destruct ch; simpl in *; try (inv DFO1; contradiction). *)
(*       + exists m_i'; split; auto. eapply Mem.store_unmapped_inject; eauto. *)
(*     - destruct d0 as (((b & ofs) & mvs) & cp). simpl in *. *)
(*       exists m_i'; split; auto. eapply Mem.storebytes_unmapped_inject; eauto. *)
(*     - destruct d0 as ((cp & lo) & hi). simpl in *. *)
(*       exists m_i'; split; auto. destruct (Mem.alloc m_i cp lo hi) eqn:ALLOC. simpl in *. inv APPD. *)
(*       eapply alloc_left_unmapped_inject_keep; eauto. *)
(*     - destruct d0 as (((b & lo) & hi) & cp). simpl in *. *)
(*       exists m_i'; split; auto. eapply Mem.free_left_inject; eauto. *)
(*   Qed. *)

(*   Definition meminj_first_order (j: meminj) (m: mem) := *)
(*     forall b ofs, (j b <> None) -> (Mem.perm m b ofs Cur Readable) -> loc_first_order m b ofs. *)

(*   Lemma mem_delta_apply_preserves_inj_incr *)
(*         (j k: meminj) m0 m0' *)
(*         (INCR: inject_incr j k) *)
(*         (INJ0: Mem.inject k m0 m0') *)
(*         (d: mem_delta) *)
(*         (DWF: mem_delta_inj_wf j d) *)
(*         (DFO: mem_delta_inj_fo j d) *)
(*         m1 *)
(*         (APPD: mem_delta_apply d m0 = Some m1) *)
(*         (MIFO: meminj_first_order j m1) *)
(*     : *)
(*     exists m1', (mem_delta_apply_inj j d m0' = Some m1') /\ (Mem.inject j m1 m1'). *)
(*   Proof. *)
(*     revert DWF DFO m1 APPD MIFO. induction d; simpl; intros. *)
(*     { inv APPD. exists m0'. split; auto. admit. (* MIFO *) } *)
(*     inv DWF. rename H1 into DWF1, H2 into DWF0. inv DFO. rename H1 into DFO1, H2 into DFO0. *)
(*     destruct (mem_delta_apply d m0) eqn:DAM. *)
(*     2:{ destruct a; *)
(*         [rewrite mem_delta_apply_store_none in APPD; inv APPD *)
(*         | rewrite mem_delta_apply_bytes_none in APPD; inv APPD *)
(*         | rewrite mem_delta_apply_alloc_none in APPD; inv APPD *)
(*         | rewrite mem_delta_apply_free_none in APPD; inv APPD]. *)
(*     } *)
(*     rename m into m_i. *)
(*     specialize (IHd DWF0 DFO0 _ (eq_refl)). destruct IHd as (m_i' & DAM' & INJ_I). *)
(*     { unfold meminj_first_order in *. intros. rename d into deltas. *)
(*       specialize (MIFO _ ofs H). exploit MIFO; clear MIFO. *)
(*       { destruct a; simpl in *. *)
(*         - unfold mem_delta_apply_store in APPD. destruct d as [[[[ch0 b0] ofs0] v0] cp0]. *)
(*           eapply Mem.perm_store_1; eauto. *)
(*         - unfold mem_delta_apply_bytes in APPD. destruct d as [[[b0 ofs0] mvs0] cp0]. *)
(*           eapply Mem.perm_storebytes_1; eauto. *)
(*         - unfold mem_delta_apply_alloc in APPD. destruct d as [[cp0 lo0] hi0]. *)
(*           destruct (Mem.alloc m_i cp0 lo0 hi0) eqn:CASES. inv APPD. *)
(*           eapply Mem.perm_alloc_1; eauto.  *)
(*         - unfold mem_delta_apply_free in APPD. destruct d as [[[b0 lo0] hi0] cp0]. *)
(*           eapply Mem.perm_free_1; eauto. left. intros EQ. subst. rewrite DWF1 in H. congruence. *)
(*       } *)
(*       intros MIFO. clear H0. *)
(*       { destruct a; simpl in *. *)
(*         - unfold mem_delta_apply_store in APPD. destruct d as [[[[ch0 b0] ofs0] v0] cp0]. *)
(*           destruct (Pos.eqb_spec b b0). *)
(*           + subst b0. unfold mem_delta_inj_store_fo in DFO1. *)
(*             destruct (j b) eqn:JB. 2: congruence. clear H. destruct p. *)
(*             unfold loc_first_order in *. clear MIFO APPD. *)
            

            
(* Mem.store_mem_contents: *)
(*   forall (chunk : memory_chunk) (m1 : mem) (b : block) (ofs : Z) (v : val)  *)
(*     (cp : compartment) (m2 : mem), *)
(*   Mem.store chunk m1 b ofs v cp = Some m2 -> *)
(*   Mem.mem_contents m2 = *)
(*   PMap.set b (Mem.setN (encode_val chunk v) ofs (Mem.mem_contents m1) !! b) (Mem.mem_contents m1) *)


          
(*           eapply Mem.perm_store_1; eauto. *)
(*         - unfold mem_delta_apply_bytes in APPD. destruct d as [[[b0 ofs0] mvs0] cp0]. *)
(*           eapply Mem.perm_storebytes_1; eauto. *)
(*         - unfold mem_delta_apply_alloc in APPD. destruct d as [[cp0 lo0] hi0]. *)
(*           destruct (Mem.alloc m_i cp0 lo0 hi0) eqn:CASES. inv APPD. *)
(*           eapply Mem.perm_alloc_1; eauto.  *)
(*         - unfold mem_delta_apply_free in APPD. destruct d as [[[b0 lo0] hi0] cp0]. *)
(*           eapply Mem.perm_free_1; eauto. left. intros EQ. subst. rewrite DWF1 in H. congruence. *)
(*       } *)



      
(*     rewrite DAM'. *)
(*     destruct a. *)
(*     - destruct d0 as ((((ch & b) & ofs) & v) & cp). simpl in *. *)
(*       destruct (j b) eqn:JB. *)
(*       + destruct p as (b' & ofs'). eapply Mem.store_mapped_inject; eauto. *)
(*         clear - DFO1. destruct v; auto. exfalso. simpl in *. destruct Archi.ptr64. *)
(*         * destruct ch; simpl in *; try (inv DFO1; contradiction). *)
(*         * destruct ch; simpl in *; try (inv DFO1; contradiction). *)
(*       + exists m_i'; split; auto. eapply Mem.store_unmapped_inject; eauto. *)
(*     - destruct d0 as (((b & ofs) & mvs) & cp). simpl in *. *)
(*       exists m_i'; split; auto. eapply Mem.storebytes_unmapped_inject; eauto. *)
(*     - destruct d0 as ((cp & lo) & hi). simpl in *. *)
(*       exists m_i'; split; auto. destruct (Mem.alloc m_i cp lo hi) eqn:ALLOC. simpl in *. inv APPD. *)
(*       eapply alloc_left_unmapped_inject_keep; eauto. *)
(*     - destruct d0 as (((b & lo) & hi) & cp). simpl in *. *)
(*       exists m_i'; split; auto. eapply Mem.free_left_inject; eauto. *)
(*   Qed. *)

(*   (* Memory injection for public global symbols: visible for external calls *) *)
(*   Definition meminj_public (ge: Senv.t): meminj := *)
(*     fun b => match Senv.invert_symbol ge b with *)
(*           | Some id => if Senv.public_symbol ge id then Some (b, 0%Z) else None *)
(*           | None => None *)
(*           end. *)


(*         (DFO: mem_delta_inj_fo j d) *)
(*                             visible_fo_if_unknown ef ge m vargs -> *)
(*     | None => visible_fo ge m (sig_args sg) args *)
(* visible_fo = *)
(* fun (ge : Senv.t) (m : mem) (tys : list typ) (args : list val) => *)
(* public_first_order ge m /\ vals_public ge tys args *)
(*      : Senv.t -> mem -> list typ -> list val -> Prop *)
(* public_first_order = *)
(* fun (ge : Senv.t) (m : mem) => *)
(* forall (id : ident) (b : block) (ofs : Z), *)
(* Senv.public_symbol ge id = true -> *)
(* Senv.find_symbol ge id = Some b -> Mem.perm m b ofs Cur Readable -> loc_first_order m b ofs *)
(*      : Senv.t -> mem -> Prop *)

(*   (* TODO: this is false --- pointers can mess around *) *)
(* (*   Lemma val_inject_incr_inv *) *)
(* (*         f f' v v' *) *)
(* (*         (INCR: inject_incr f f') *) *)
(* (*         (INJ: Val.inject f' v v') *) *)
(* (*     : *) *)
(* (*     Val.inject f v v'. *) *)
(* (*   Proof. *) *)
(* (*     inv INJ; auto. eapply Val.inject_ptr; auto. *) *)
(* (* val_inject_incr: forall (f1 f2 : meminj) (v v' : val), inject_incr f1 f2 -> Val.inject f1 v v' -> Val.inject f2 v v' *) *)

(*   Lemma mem_inject_incr *)
(*         f f' m m' *)
(*         (INCR: inject_incr f f') *)
(*         (INJ: Mem.inject f' m m') *)
(*     : *)
(*     Mem.inject f m m'. *)
(*   Proof. *)
(*     unfold Mem.inject in *. inv INJ. split; eauto. *)
(*     2:{ intros. specialize (mi_freeblocks _ H). unfold inject_incr in INCR. *)
(*         destruct (f b) eqn:FB; auto. destruct p. specialize (INCR _ _ _ FB). *)
(*         rewrite INCR in mi_freeblocks. inv mi_freeblocks. *)
(*     } *)
(*     2:{ clear - INCR mi_no_overlap. unfold Mem.meminj_no_overlap in *. intros. *)
(*         exploit mi_no_overlap; eauto. *)
(*     } *)
(*     clear - INCR mi_inj. inv mi_inj. split; eauto. intros. exploit mi_memval; eauto. intros. *)
(*     eapply memval_inject_incr; eauto. *)
(*     ` *)
    
(* val_inject_incr: forall (f1 f2 : meminj) (v v' : val), inject_incr f1 f2 -> Val.inject f1 v v' -> Val.inject f2 v v' *)
(* Unusedglobproof.regset_inject_incr: forall (f f' : meminj) (rs rs' : RTL.regset), Unusedglobproof.regset_inject f rs rs' -> inject_incr f f' -> Unusedglobproof.regset_inject f' rs rs' *)
(* memval_inject_incr: forall (f f' : meminj) (v1 v2 : memval), memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2 *)
(* Stackingproof.agree_regs_inject_incr: forall (j : meminj) (ls : Linear.locset) (rs : Mach.regset) (j' : meminj), Stackingproof.agree_regs j ls rs -> inject_incr j j' -> Stackingproof.agree_regs j' ls rs *)
(* Cminorgenproof.match_temps_invariant: forall (f f' : meminj) (le : Csharpminor.temp_env) (te : Cminor.env), Cminorgenproof.match_temps f le te -> inject_incr f f' -> Cminorgenproof.match_temps f' le te *)
(* val_inject_list_incr: forall (f1 f2 : meminj) (vl vl' : list val), inject_incr f1 f2 -> Val.inject_list f1 vl vl' -> Val.inject_list f2 vl vl' *)


(* End MEMDELTA. *)


Section BUNDLE.

  (* (* ()-no event, {}-may event, when len(tr) > 1, need to consider cuts *) *)
  (* (* intra/cross/virtual(default), internal/external *) *)
  (* Variant bundle_event : Type := *)
  (* (* generate a call code + other followup events *) *)
  (*   | Bundle_call_ci (tr: trace) (id: ident) (args: list eventval) (sg: signature) (* call *) *)
  (*   | Bundle_call_ce (tr: trace) (id: ident) (args: list eventval) (sg: signature) (* call-{ext}-ret - cut at {1, 2, 3} *) *)
  (*   | Bundle_call_vi (tr: trace) (id: ident) (args: list eventval) (sg: signature) (* (call) - compartment changes *) *)
  (*   | Bundle_call_ve (tr: trace) (id: ident) (args: list eventval) (sg: signature) (* (call)-ext-(ret) - also cut *) *)
  (*   | Bundle_call_ie (tr: trace) (id: ident) (args: list eventval) (sg: signature) (* (call)-ext-(ret) *) *)
  (* (* generate a return code *) *)
  (*   | Bundle_return_ci (tr: trace) (sg: signature) (* ret *) *)
  (*   | Bundle_return_vi (tr: trace) (sg: signature) (* (ret) - compartment change *) *)
  (* (* generate a builtin code *) *)
  (*   | Bundle_builtin (tr: trace) (ef: external_function) (* ext *) *)
  (* . *)

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

  Inductive istar {genv state : Type} (step : genv -> state -> bundle_event -> state -> Prop) (ge : genv) : state -> bundle_trace -> state -> Prop :=
    istar_refl : forall s : state, istar step ge s nil s
  | istar_step : forall (s1 : state) (ev : bundle_event) (s2 : state) (t2 : bundle_trace) (s3 : state) (t : bundle_trace),
      step ge s1 ev s2 -> istar step ge s2 t2 s3 -> t = ev :: t2 -> istar step ge s1 t s3.

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

  (* Definition genv_invert_symbol_total {F V : Type} (ge : Genv.t F V) : block -> ident := *)
  (*   fun b => match Genv.invert_symbol ge b with | Some i => i | None => xH end. *)

  (* only virtual (default) or real (cross) cases *)
  Inductive call_trace_vr {F V : Type} (ge : Genv.t F V) : compartment -> compartment -> block -> list val -> list typ -> trace -> ident -> list eventval -> Prop :=
  | call_trace_vr_cross : forall (cp cp' : compartment) (b : block) (vargs : list val) (vl : list eventval) (ty : list typ) (i : ident),
      Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall ->
      Genv.invert_symbol ge b = Some i -> eventval_list_match ge vl ty vargs -> call_trace_vr ge cp cp' b vargs ty (Event_call cp cp' i vl :: nil) i vl.

  Inductive return_trace_vr {F V : Type} (ge : Genv.t F V) : compartment -> compartment -> val -> rettype -> trace -> eventval -> Prop :=
  | return_trace_vr_cross : forall (cp cp' : compartment) (res : eventval) (v : val) (ty : rettype),
      Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall -> eventval_match ge res (proj_rettype ty) v -> return_trace_vr ge cp cp' v ty (Event_return cp cp' res :: nil) res.

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

End EVENT.


Section IR.

  Variant ir_cont_type : Type := | ir_cont: block -> ir_cont_type.
  Definition ir_conts := list ir_cont_type.

  Definition crossing_comp {F V} (ge: Genv.t F V) (cp cp': compartment) :=
    Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall.

  Definition ir_state := option (block * mem * ir_conts)%type.

  Variant ir_step (ge: Asm.genv) : ir_state -> bundle_event -> ir_state -> Prop :=
    | ir_step_vr_call_internal
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
        (TR: call_trace_vr ge cp cp' b vargs (sig_args sg) tr id evargs)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_call tr id evargs sg None) (Some (b, m1, (ir_cont cur) :: ik))
    | ir_step_vr_return_internal
        cur m1 next ik_tl
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
        (TR: return_trace_vr ge cp_next cp_cur vretv (sig_res sg) tr evretv)
      :
      ir_step ge (Some (cur, m1, ((ir_cont next) :: ik_tl))) (Bundle_return tr evretv) (Some (next, m1, ik_tl))
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
        (MEM: mem_delta_apply_inj (meminj_public ge) d m1 = Some m1')
        vargs vretv
        (EC: external_call ef ge vargs m1' tr vretv m2)
        (VISFO: visible_fo_and_unknown ef ge m1 vargs)
        (ARGS: evargs = vals_to_eventvals ge vargs)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_call tr id evargs sg (Some d)) (Some (cur, m2, ik))
    | ir_step_builtin
        cur m1 m2 ik
        tr ef evargs
        cp_cur
        (CURCP: cp_cur = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        d m1'
        (MEM: mem_delta_apply_inj (meminj_public ge) d m1 = Some m1')
        vargs vretv
        (EC: external_call ef ge vargs m1' tr vretv m2)
        (VISFO: visible_fo_and_unknown ef ge m1 vargs)
        (ARGS: evargs = vals_to_eventvals ge vargs)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_builtin tr ef evargs d) (Some (cur, m2, ik))
    | ir_step_vr_call_external1
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
        (TR: call_trace_vr ge cp cp' b vargs (sig_args sg) tr id evargs)
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
        (TR: call_trace_vr ge cp cp' b vargs (sig_args sg) tr1 id evargs)
        (* external function part *)
        d m1'
        (MEM: mem_delta_apply_inj (meminj_public ge) d m1 = Some m1')
        tr2 m2 vretv
        (EC: external_call ef ge vargs m1' tr2 vretv m2)
        (VISFO: visible_fo_and_unknown ef ge m1 vargs)
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
        (TR1: call_trace_vr ge cp cp' b vargs (sig_args sg) tr1 id evargs)
        (* external function part *)
        d m1'
        (MEM: mem_delta_apply_inj (meminj_public ge) d m1 = Some m1')
        tr2 m2 vretv
        (TR2: external_call ef ge vargs m1' tr2 vretv m2)
        (VISFO: visible_fo_and_unknown ef ge m1 vargs)
        (ARGS: evargs = vals_to_eventvals ge vargs)
        (* return part *)
        tr3 evretv
        (NPTR: crossing_comp ge cp cp' -> not_ptr vretv)
        f_cur
        (INTERNAL: Genv.find_funct_ptr ge cur = Some (AST.Internal f_cur))
        (TR3: return_trace_vr ge cp cp' vretv (sig_res sg) tr3 evretv)
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


Section INVS.

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


  Definition match_cur_stack (cur: block) (ge: Asm.genv) (sk: stack) :=
    match Genv.find_funct_ptr ge cur with
    | Some fd => Asm.funsig fd = sig_of_call sk
    | _ => False
    end.

  Definition match_cur_regset (cur: block) (ge: Asm.genv) (rs: regset) :=
    Genv.find_comp ge (Vptr cur Ptrofs.zero) = Genv.find_comp_ignore_offset ge (rs PC).

  Variant match_stackframe (ge: Asm.genv) : ir_cont_type -> stackframe -> Prop :=
    | match_stackframe_intro
        b1 b2 cp sg v ofs
        (COMP: Genv.find_comp ge (Vptr b1 Ptrofs.zero) = Genv.find_comp ge (Vptr b2 Ptrofs.zero))
      :
      match_stackframe ge (ir_cont b1) (Stackframe b2 cp sg v ofs).
  Definition match_stack (ge: Asm.genv) (ik: ir_conts) (st: stack) :=
    Forall2 (match_stackframe ge) ik st.

  Definition match_mem (ge: Senv.t) (d: mem_delta) (m0 m_i m_a: mem): Prop :=
    let j := meminj_public ge in
    (Mem.inject j m0 m_i) /\ (mem_delta_inj_wf j d) /\
      (mem_delta_apply d m0 = Some m_a).

  Definition match_state (ge: Asm.genv) (m0: mem) (d: mem_delta)
             (ast: Asm.state) (ist: ir_state): Prop :=
    match ast, ist with
    | State sk rs m_a, Some (cur, m_i, ik) =>
        (match_cur_stack cur ge sk) /\ (match_cur_regset cur ge rs) /\
          (match_stack ge ik sk) /\ (match_mem ge d m0 m_i m_a)
    | _, _ => False
    end.

End INVS.


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

  Lemma mem_delta_exec_instr
        ge f i rs m cp rs' m'
        (* comp_of f ? *)
        (EXEC: exec_instr ge f i rs m cp = Next rs' m')
        m0 d
        (DELTA0: mem_delta_inj_wf (meminj_public ge) d)
        (DELTA1: mem_delta_apply d m0 = Some m)
    :
    exists d', (mem_delta_inj_wf (meminj_public ge) d') /\ (mem_delta_apply d' m0 = Some m').
  Proof.
    (* TODO *)
  Admitted.

End FROMASM.


Section PROOF.

  Ltac empty_case := do 2 eexists; split; [|constructor 1]; auto.

  (* If main is External, treat it in a different case - 
     the trace can start with Event_syscall, without a preceding Event_call *)
  Lemma asm_to_ir
        cpm ge m0
        ast ast' tr
        (WFGE: wf_ge ge)
        (WFASM: wf_asm ge ast)
        (STAR: star (Asm.step_fix cpm) ge ast tr ast')
        ist d
        (MTST: match_state ge m0 d ast ist)
    :
    exists btr ist', (unbundle_trace btr = tr) /\ (istar (ir_step) ge ist btr ist').
  Proof.
    apply measure_star in STAR. destruct STAR as (n & STAR).
    move n before m0. revert ast ast' tr WFGE WFASM STAR ist d MTST.
    pattern n. apply (well_founded_induction Nat.lt_wf_0). intros n1 IH. intros.
    inv STAR; subst.
    (* empty case *)
    { empty_case. }
    rename H0 into STAR. inv H; simpl.
    - destruct (Genv.find_funct_ptr ge b') eqn:NEXTF.
      (* no next function *)
      2:{ move STAR after NEXTF. inv STAR.
          (* empty case *)
          { empty_case. }
          (* take a step *)
          { inv H.
            (* invalid *)
            all: exfalso; rewrite NEXTPC in H10; inv H10; rewrite NEXTF in H11; inv H11.
          }
      }
      unfold match_state in MTST. destruct ist as [[[cur m_i] ik] |].
      2:{ inv MTST. }
      destruct MTST as (MTST0 & MTST1 & MTST2 & MTST3). destruct MTST3 as (MEM0 & MEM1 & MEM2).
      exploit mem_delta_exec_instr. eapply H3. eapply MEM1. eapply MEM2. intros (d' & MEM1' & MEM2').
      destruct f0.
      (* has next function --- internal *)
      { assert (WFASM': wf_asm ge (State st rs' m')).
        { clear IH. unfold wf_asm in *. destruct WFASM as [WFASM0 WFASM1]. split; [auto|].
          unfold wf_regset in *. rewrite H0, H1 in WFASM1. rewrite NEXTPC, NEXTF. auto.
        }
        assert (MTST': match_state ge m0 d' (State st rs' m') (Some (cur, m_i, ik))).
        { clear IH. split. auto. split.
          { unfold match_cur_regset in *. rewrite NEXTPC. rewrite <- ALLOWED. rewrite MTST1.
            unfold Genv.find_comp_ignore_offset. rewrite H0. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr.
            rewrite H1. auto.
          }
          split. auto.
          { unfold match_mem; auto. }
        }
        exploit IH. 4: eapply STAR. all: auto. eapply MTST'.
        intros (btr & ist' & UNTR & ISTAR).
        exists btr, ist'. split; auto.
      }
      (* has next function --- external *)
      { move STAR after NEXTF. inv STAR.
        (* empty case *)
        { empty_case. }
        (* take a step *)
        inv H.
        (* invalid *)
        1,2,3,4: rewrite NEXTPC in H10; inv H10; rewrite NEXTF in H11; inv H11.
        (* external call & InternalCall *)
        { rewrite NEXTPC in H10; inv H10. rewrite NEXTF in H11; inv H11.
          exploit Genv.find_funct_ptr_iff. intros (TEMP & _). specialize (TEMP NEXTF). exploit wf_ge_block_to_id; eauto. intros (ef_id & INVSYMB).
          exploit Genv.invert_find_symbol; eauto. intros FINDSYMB.
          (* reestablish meminj *)
          exploit mem_delta_apply_preserves_inj. eapply MEM0. eapply MEM1'.
          { admit. (* from VISFO *) }
          eapply MEM2'.
          intros (m1' & MEMAPPIR & MEMINJ').
          exploit external_call_mem_inject.
          { admit. }
          { eapply H12. }
          { eapply MEMINJ'. }
          { instantiate (1:=args). admit. }
          intros (f' & vres' & m2' & EXTCALL' & VALINJ' & MEMINJ'2 & _ & _ & INCRINJ & _).
          (* take a step *)
          rename H6 into STEP1; move STEP1 after REC_CURCOMP. inv STEP1.
          (* terminates *)
          { exists ((Bundle_call t1 ef_id (vals_to_eventvals ge args) (ef_sig ef) (Some d')) :: nil). eexists. simpl. split; auto.
            econstructor 2. 2: econstructor 1. 2: auto.
            eapply ir_step_intra_call_external. 2: eapply FINDSYMB. 2: eapply NEXTF. 6: eapply EXTCALL'. all: eauto.
            { unfold match_cur_regset in MTST1. rewrite MTST1. rewrite H0. simpl. unfold Genv.find_comp. simpl. rewrite pred_dec_true; auto.
              rewrite H1. setoid_rewrite ALLOWED. simpl. unfold Genv.find_comp. simpl. rewrite pred_dec_true; auto. rewrite NEXTF.
              unfold Genv.type_of_call. rewrite Pos.eqb_refl. auto.
            }
            { admit. (* VISFO --- maybe case analysis first on unknowns? *) }
          }
          (* steps --- ReturnState *)


        

  H1 : Genv.find_funct_ptr ge b = Some (Internal f)
  ALLOWED : comp_of f = Genv.find_comp_ignore_offset ge (Vptr b0 Ptrofs.zero)
  NEXTPC : rs' PC = Vptr b0 Ptrofs.zero
  NEXTF : Genv.find_funct_ptr ge b0 = Some (External ef)


external_call_mem_inject:
  forall (ef : external_function) [F V : Type] [ge : Genv.t F V] [vargs : list val] [m1 : mem] (t : trace) (vres : val) (m2 : mem) [f : block -> option (block * Z)] [m1' : mem] [vargs' : list val],
  meminj_preserves_globals ge f ->
  external_call ef ge vargs m1 t vres m2 ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists (f' : meminj) (vres' : val) (m2' : mem),
    external_call ef ge vargs' m1' t vres' m2' /\
    Val.inject f' vres vres' /\ Mem.inject f' m2 m2' /\ Mem.unchanged_on (loc_unmapped f) m1 m2 /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' /\ inject_incr f f' /\ inject_separated f f' m1 m1'


  | ir_step_intra_call_external : forall (cur : block) (m1 m2 : mem) (ik : ir_conts) (tr : trace) (id : ident) (evargs : list eventval) (sg : signature) (cp_cur : compartment),
                                  cp_cur = Genv.find_comp ge (Vptr cur Ptrofs.zero) ->
                                  forall (b_ext : block) (ef : external_function) (cp_ext : compartment),
                                  Genv.find_symbol ge id = Some b_ext ->
                                  Genv.find_funct ge (Vptr b_ext Ptrofs.zero) = Some (External ef) ->
                                  cp_ext = comp_of ef ->
                                  Genv.type_of_call ge cp_cur cp_ext = Genv.InternalCall ->
                                  sg = ef_sig ef ->
                                  forall (d : mem_delta) (m1' : mem),
                                  mem_delta_apply d m1 = Some m1' ->
                                  forall (vargs : list val) (vretv : val),
                                  external_call ef ge vargs m1' tr vretv m2 ->
                                  visible_fo_and_unknown ef ge m1 vargs -> evargs = vals_to_eventvals ge vargs -> ir_step ge (Some (cur, m1, ik)) (Bundle_call tr id evargs sg (Some d)) (Some (cur, m2, ik))


          
          (* TODO *)



            (*   OLD   *)
      unfold wf_asm in WFASM. unfold match_state in MTST. 
      assert (INTRA: Genv.find_comp ge (Vptr cur Ptrofs.zero) = Genv.find_comp_ignore_offset ge (rs' PC)).
      { rewrite MC. rewrite NEXTPC, <- ALLOWED. unfold Genv.find_comp_ignore_offset. rewrite H3. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr. rewrite H4. auto. }
      destruct (Genv.find_funct_ptr ge b') eqn:NEXTFUN. destruct f0.
      + eapply IH; try reflexivity. 3: eauto. all: auto.
        { unfold wf_regset_stack. rewrite NEXTPC, NEXTFUN. auto. }
        { admit. (* mem *) }
      + (* intra -> external *)
        inv STAR.
        { constructor 1. }
        inv H. all: rewrite NEXTPC in H8; inv H8; rewrite NEXTFUN in H11; inv H11.
        inv H0.
        { (* trace ends *)
          exploit external_call_trace_length. eauto. intros EVLEN. destruct t.
          - simpl. constructor 1.
          - destruct t; simpl in EVLEN. 2: lia. clear EVLEN.
            simpl. pose proof NEXTFUN as NF0. unfold Genv.find_funct_ptr in NF0. destruct (Genv.find_def ge b0) eqn:FDB0; [|inv NF0]. destruct g; inv NF0.
            exploit wf_ge_block_to_id; eauto. intros (fid & INV).
            econstructor 4; try reflexivity; auto.
            { admit. (* ext call sem *) }
            { eauto. }
            { unfold Genv.allowed_call. right; left. rewrite <- NEXTPC. rewrite INTRA. unfold Genv.find_comp_ignore_offset, Genv.find_comp. rewrite NEXTPC. auto. }
            { unfold Genv.type_of_call. rewrite INTRA. unfold Genv.find_comp_ignore_offset, Genv.find_comp. rewrite NEXTPC. rewrite Pos.eqb_refl. auto. }
            { constructor 1. }
        }
        inv H.
        (* replace ((set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs')) # PC <- (rs' X1) PC) with (rs' X1) in *. *)
        (* 2:{ rewrite Pregmap.gss. auto. } *)
        destruct (Pos.eqb_spec (callee_comp cpm sk) (Genv.find_comp_ignore_offset ge ((set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs')) # PC <- (rs' X1) PC))).
        { (* intra-return *)
          clear PC_RA RESTORE_SP NO_CROSS_PTR. pose proof EV as RETEV. inv RETEV; simpl.
          2:{ exfalso. unfold Genv.type_of_call in H. rewrite <- e in H. rewrite Pos.eqb_refl in H. inv H. }
          2:{ exfalso. unfold Genv.type_of_call in H. rewrite <- e in H. rewrite Pos.eqb_refl in H. inv H. }
          assert (STK: st' = sk).
          { unfold update_stack_return in STUPD. rewrite <- e in STUPD. rewrite Pos.eqb_refl in STUPD. inv STUPD. auto. }
          subst st'. simpl in INFO; subst. simpl.
          pose proof H1 as IH_ISTAR. move IH_ISTAR after H1. inv H1.
          { (* trace ends *)
            exploit external_call_trace_length. eauto. intros EVLEN. destruct t.
            { simpl. clear EVLEN. constructor 1. }
            destruct t; simpl in EVLEN. 2: lia. clear EVLEN.
            pose proof NEXTFUN as NF0. unfold Genv.find_funct_ptr in NF0. destruct (Genv.find_def ge b0) eqn:FDB0; [|inv NF0]. destruct g; inv NF0.
            exploit wf_ge_block_to_id. eauto. eapply FDB0. intros (fid & INV).
            eapply info_asm_sem_wf_intra_call_external; eauto.
            { admit. (* ext call sem *) }
            { unfold Genv.allowed_call. right; left. rewrite <- NEXTPC. rewrite INTRA. unfold Genv.find_comp_ignore_offset, Genv.find_comp. rewrite NEXTPC. auto. }
            { unfold Genv.type_of_call. rewrite INTRA. unfold Genv.find_comp_ignore_offset, Genv.find_comp. rewrite NEXTPC. rewrite Pos.eqb_refl. auto. }
            { constructor 1. }
          }
          (* now we case-analysis new PC = (rs' X1) *)
          destruct (val_is_ptr_or_not (rs' X1)).
          { (* not a Vptr, so booms for every step *)
            rename H1 into NP. clear - H0 NP. inv H0; exfalso. all: rewrite Pregmap.gss in H3; eapply NP; eauto.
          }
          destruct H1 as (b2 & ofs2 & NEXTPC2). destruct (Genv.find_funct_ptr ge b2) eqn:NEXTFUN2. destruct f0.
          { (* next fun is internal - done by induction *)
            exploit external_call_trace_length. eauto. intros EVLEN. destruct t; simpl.
            { clear EVLEN.
              eapply IH. 3: eapply IH_ISTAR. all: auto.
              - red. rewrite Pregmap.gss. rewrite NEXTPC2. rewrite NEXTFUN2. auto.
              - rewrite Pregmap.gss in *. rewrite <- e. rewrite <- REC_CURCOMP. auto.
              - admit. (* mem -> need to execute external call to maintain injection? *)
            }
            destruct t; simpl in *. 2:lia. clear EVLEN.
            pose proof NEXTFUN as NF0. unfold Genv.find_funct_ptr in NF0. destruct (Genv.find_def ge b0) eqn:FDB0; [|inv NF0]. destruct g; inv NF0.
            exploit wf_ge_block_to_id. eauto. eapply FDB0. intros (fid & INV).
            eapply info_asm_sem_wf_intra_call_external; eauto.
            { admit. (* ext call sem *) }
            { unfold Genv.allowed_call. right; left. rewrite <- NEXTPC. rewrite INTRA. unfold Genv.find_comp_ignore_offset, Genv.find_comp. rewrite NEXTPC. auto. }
            { unfold Genv.type_of_call. rewrite INTRA. unfold Genv.find_comp_ignore_offset, Genv.find_comp. rewrite NEXTPC. rewrite Pos.eqb_refl. auto. }
            eapply IH. 3: eapply IH_ISTAR. all: auto.
            - red. rewrite Pregmap.gss. rewrite NEXTPC2. rewrite NEXTFUN2. auto.
            - rewrite Pregmap.gss in *. rewrite <- e. rewrite <- REC_CURCOMP. auto.
            - admit. (* mem *)
          }
          { (* next fun is external; undef_caller_save_regs sets RA=Vundef, so we take extcall-step, which sets PC=RA, and after the return step, we have PC=Vundef. *)
            (* TODO *)

            Abort.


End PROOF.


Section INFORMATIVE.
  Import Smallstep.

  (* At CROSS-COMP calls, if fundef is ext, set to is_cross_ext. Otherwise is_not_ext. *)
  (* When a Event_call is is_cross_ext, do not back-translate the following (possible Event_syscall and) Event_return. *)
  Variant cross_ext := | is_cross_ext | not_cross_ext.

  Variant real_virtual := | is_real | is_virtual.

  (* Additional information *)
  Variant info_kind :=
    (* Get information for cross-comp calls and returns *)
    | info_call (ce: cross_ext) (sg: signature) (vr: real_virtual)
    | info_return (sg: signature) (vr: real_virtual)
    (* Get information for inter-comp external calls or builtins *)
    | info_external (b: block) (sg: signature)
    | info_builtin (ef: external_function)
    (* | info_default *)
  .

  (* Informative events *)
  Definition ievent := (event * info_kind)%type.
  Definition itrace := list ievent.

  Definition iE0: itrace := nil.

  (* Informative to original *)
  Definition iev_to_ev (ie: ievent) : event := (fst ie).
  (* Definition itr_to_tr (ies: itrace) : trace := map iev_to_ev ies. *)

  Definition filter_virtual (iev: ievent): bool :=
    match iev with
    | (ev, info_call _ _ is_virtual) | (ev, info_return _ is_virtual) => false
    | _ => true
    end.

  Definition itr_to_tr (itr: itrace) : trace := map iev_to_ev (filter filter_virtual itr).

  Lemma itr_to_tr_cons
        ev tr
    :
    itr_to_tr (ev :: tr) = if (filter_virtual ev) then (fst ev) :: (itr_to_tr tr) else (itr_to_tr tr).
  Proof. unfold itr_to_tr. destruct ev. destruct i; simpl; auto. 1,2: destruct vr; simpl; auto. Qed.

  Lemma itr_to_tr_app
        t1 t2
    :
    itr_to_tr (t1 ++ t2) = (itr_to_tr t1) ++ (itr_to_tr t2).
  Proof. unfold itr_to_tr. rewrite filter_app. rewrite map_app. auto. Qed.

  Lemma filter_map
        A B f (m: A -> B)
        (l: list A)
        (FA: forall a, f (m a) = true)
    :
    filter f (map m l) = map m l.
  Proof. induction l; simpl; auto. rewrite FA. rewrite IHl. auto. Qed.

  (* Informative behavior *)
  (* CoInductive itraceinf : Type :=  iEconsinf : ievent -> itraceinf -> itraceinf. *)
  (* CoFixpoint itri_to_tri (itri: itraceinf): traceinf := *)
  (*   match itri with iEconsinf hd tl => Econsinf (iev_to_ev hd) (itri_to_tri tl) end. *)

  (* Definition itri_to_tri_obs (itri: itraceinf) := *)
  (*   match itri with iEconsinf hd tl => iEconsinf hd tl end. *)

  (* Lemma itri_to_tri_obs_eq: forall itri, itri_to_tri_obs itri = itri. *)
  (* Proof. destruct itri; reflexivity. Qed. *)

  (* Fixpoint iEappinf (t: itrace) (T: itraceinf) {struct t} : itraceinf := *)
  (*   match t with *)
  (*   | nil => T *)
  (*   | ev :: t' => iEconsinf ev (iEappinf t' T) *)
  (*   end. *)


  (* Inductive iprogram_behavior : Type := *)
  (*   iTerminates : itrace -> int -> iprogram_behavior *)
  (* | iDiverges : itrace -> iprogram_behavior *)
  (* | iReacts : itraceinf -> iprogram_behavior *)
  (* | iGoes_wrong : itrace -> iprogram_behavior. *)

  (* Definition iph_to_pb (ipb: iprogram_behavior): program_behavior := *)
  (*   match ipb with *)
  (*   | iTerminates itr r => Terminates (itr_to_tr itr) r *)
  (*   | iDiverges itr => Diverges (itr_to_tr itr) *)
  (*   | iReacts itri => Reacts (itri_to_tri itri) *)
  (*   | iGoes_wrong itr => Goes_wrong (itr_to_tr itr) *)
  (*   end. *)

  Inductive istar {genv state : Type} (step : genv -> state -> itrace -> state -> Prop) (ge : genv) : state -> itrace -> state -> Prop :=
    istar_refl : forall s : state, istar step ge s nil s
  | istar_step : forall (s1 : state) (t1 : itrace) (s2 : state) (t2 : itrace) (s3 : state) (t : itrace),
      step ge s1 t1 s2 -> istar step ge s2 t2 s3 -> t = t1 ++ t2 -> istar step ge s1 t s3.

  Inductive istar_measure {genv state : Type} (step : genv -> state -> itrace -> state -> Prop) (ge : genv) : nat -> state -> itrace -> state -> Prop :=
    istar_measure_refl : forall s : state, istar_measure step ge O s nil s
  | istar_measure_step : forall (n: nat) (s1 : state) (t1 : itrace) (s2 : state) (t2 : itrace) (s3 : state) (t : itrace),
      step ge s1 t1 s2 -> istar_measure step ge n s2 t2 s3 -> t = t1 ++ t2 -> istar_measure step ge (S n) s1 t s3.

  Lemma measure_istar
        genv state
        (step : genv -> state -> itrace -> state -> Prop)
        (ge : genv)
        s0 tr s1
        (STAR: istar step ge s0 tr s1)
    :
    exists n, istar_measure step ge n s0 tr s1.
  Proof.
    induction STAR.
    { exists O. constructor 1. }
    destruct IHSTAR as (n & NEXT). exists (S n). econstructor 2. eapply H. eapply NEXT. auto.
  Qed.


  (* Record isemantics : Type := *)
  (*   iSemantics_gen *)
  (*     { istate : Type; *)
  (*       igenvtype : Type; *)
  (*       istep : igenvtype -> istate -> itrace -> istate -> Prop; *)
  (*       iinitial_state : istate -> Prop; *)
  (*       ifinal_state : istate -> int -> Prop; *)
  (*       iglobalenv : igenvtype; *)
  (*       isymbolenv : Senv.t *)
  (*     }. *)

  (* Definition sem_to_isem (L: Smallstep.semantics) (istep: (genvtype L) -> (state L) -> itrace -> (state L) -> Prop) : isemantics := *)
  (*   iSemantics_gen _ _ istep (initial_state L) (final_state L) (globalenv L) (symbolenv L). *)

  (* CoInductive iforever_silent (genv state : Type) (step : genv -> state -> itrace -> state -> Prop) (ge : genv) : state -> Prop := *)
  (*   iforever_silent_intro : forall s1 s2 : state, step ge s1 nil s2 -> iforever_silent _ _ step ge s2 -> iforever_silent _ _ step ge s1. *)

  (* CoInductive iforever_reactive (genv state : Type) (step : genv -> state -> itrace -> state -> Prop) (ge : genv) : state -> itraceinf -> Prop := *)
  (*   iforever_reactive_intro : forall (s1 s2 : state) (t : itrace) (T : itraceinf), *)
  (*       istar step ge s1 t s2 -> t <> nil -> iforever_reactive _ _ step ge s2 T -> iforever_reactive _ _ step ge s1 (iEappinf t T). *)

  (* Definition inostep := fun (genv state : Type) (step : genv -> state -> itrace -> state -> Prop) (ge : genv) (s : state) => forall (t : itrace) (s' : state), ~ step ge s t s'. *)

  (* Inductive istate_behaves (L : semantics) (istep: (genvtype L) -> (state L) -> itrace -> (state L) -> Prop) (s : state L): itrace -> program_behavior -> Prop := *)
  (*   istate_terminates : forall (t : itrace) (s' : state L) (r : int), *)
  (*       (istar istep (globalenv L)) s t s' -> final_state L s' r -> istate_behaves L istep s t (Terminates (itr_to_tr t) r) *)
  (* | istate_diverges : forall (t : itrace) (s' : state L), *)
  (*     (istar (istep) (globalenv L)) s t s' -> (forever_silent _ _ (step L) (globalenv L)) s' -> istate_behaves L istep s t (Diverges (itr_to_tr t)) *)
  (* | istate_reacts : forall (t: itrace) (T : traceinf), *)
  (*     (iforever_reactive _ _ (istep L) (iglobalenv L)) s T -> istate_behaves L istep s t (Reacts T) *)
  (* | istate_goes_wrong : forall (t : itrace) (s' : istate L), *)
  (*     (istar (istep L) (iglobalenv L)) s t s' -> (inostep _ _ (istep L) (iglobalenv L)) s' -> (forall r : int, ~ ifinal_state L s' r) -> istate_behaves L s (iGoes_wrong t). *)

  (* Inductive iprogram_behaves (L : semantics) (istep: (genvtype L) -> (state L) -> itrace -> (state L) -> Prop): itrace -> program_behavior -> Prop := *)
  (*   iprogram_runs : forall (s : state L) (t: itrace) (beh : iprogram_behavior), *)
  (*       initial_state L s -> istate_behaves L istep s t beh -> iprogram_behaves L t beh *)
  (* | iprogram_goes_initially_wrong : (forall s : state L, ~ initial_state L s) -> iprogram_behaves L nil (Goes_wrong nil). *)

  Definition istep (L: Smallstep.semantics) := (genvtype L) -> (state L) -> itrace -> (state L) -> Prop.

  Definition state_has_trace_informative (L: Smallstep.semantics) (s: state L) (step: istep L) (t: itrace): Prop :=
    (exists s', (istar step (globalenv L)) s t s').

  Variant semantics_has_initial_trace_informative (L: Smallstep.semantics) (step: istep L) (t: itrace) : Prop :=
    | semantics_info_runs :
      forall s, (initial_state L s) -> (state_has_trace_informative L s step t) -> semantics_has_initial_trace_informative _ _ t
    | semantics_info_goes_initially_wrong : (forall s : state L, ~ initial_state L s) -> (t = nil) -> semantics_has_initial_trace_informative _ _ t.

End INFORMATIVE.


Lemma iE0_left: forall t, iE0 ++ t = t.
Proof. auto. Qed.

Lemma iE0_right: forall t, t ++ iE0 = t.
Proof. intros. unfold iE0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma iEapp_assoc: forall (t1 t2 t3: itrace), (t1 ++ t2) ++ t3 = t1 ++ (t2 ++ t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma iEapp_E0_inv: forall t1 t2, t1 ++ t2 = iE0 -> t1 = iE0 /\ t2 = iE0.
Proof. eapply (@app_eq_nil ievent). Qed.

(* Lemma iE0_left_inf: forall T, iEappinf iE0 T = T. *)
(* Proof. auto. Qed. *)

(* Lemma iEappinf_assoc: forall t1 t2 T, iEappinf (t1 ++ t2) T = iEappinf t1 (iEappinf t2 T). *)
(* Proof. *)
(*   induction t1; intros; simpl. auto. decEq; auto. *)
(* Qed. *)

#[global]
Hint Rewrite iE0_left iE0_right iEapp_assoc: itrace_rewrite.
(* Hint Rewrite iE0_left iE0_right iEapp_assoc *)
(*              iE0_left_inf iEappinf_assoc: itrace_rewrite. *)

Ltac isubstTraceHyp :=
  match goal with
  | [ H: (@eq itrace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac idecomposeTraceEq :=
  match goal with
  | [ |- (_ ++ _) = (_ ++ _) ] =>
      apply (f_equal2 app); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac itraceEq :=
  repeat isubstTraceHyp; autorewrite with itrace_rewrite; idecomposeTraceEq.


(* Section AUX. *)

(*   Definition ibehavior_app (t: itrace) (beh: iprogram_behavior): iprogram_behavior := *)
(*     match beh with *)
(*     | iTerminates t1 r => iTerminates (t ++ t1) r *)
(*     | iDiverges t1 => iDiverges (t ++ t1) *)
(*     | iReacts T => iReacts (iEappinf t T) *)
(*     | iGoes_wrong t1 => iGoes_wrong (t ++ t1) *)
(*     end. *)

(*   Lemma ibehavior_app_assoc: *)
(*     forall t1 t2 beh, *)
(*       ibehavior_app (t1 ++ t2) beh = ibehavior_app t1 (ibehavior_app t2 beh). *)
(*   Proof. *)
(*     intros. destruct beh; simpl; f_equal; itraceEq. *)
(*   Qed. *)

(*   Lemma ibehavior_app_E0: *)
(*     forall beh, ibehavior_app iE0 beh = beh. *)
(*   Proof. *)
(*     destruct beh; auto. *)
(*   Qed. *)

(*   Definition ibehavior_prefix (t: itrace) (beh: iprogram_behavior) : Prop := *)
(*     exists beh', beh = ibehavior_app t beh'. *)

(* End AUX. *)


Section AUX.

  Definition block_first_order (m: mem) (b: block): Prop :=
    forall (ofs: Z),
      match (ZMap.get ofs (Mem.mem_contents m) !! b) with
      | Fragment vv _ _ => not_ptr vv
      | _ => True
      end.

  (* Definition val_first_order (m: mem) (v: val): Prop := *)
  (*   match v with *)
  (*   | Vptr b _ => block_first_order m b *)
  (*   | _ => True *)
  (*   end. *)

  (* Redundant - we enforce Event_syscall to respect eventval_list_match on args,
     which enforce pointers to be public - which are first-order by the semantics *)
  (* Definition syscall_args_first_order (m: mem) (args: list val) := *)
  (*   Forall (val_first_order m) args. *)

  (* Public symbols are visible outside the compilation unit, 
     so when interacting via external calls, limit them to first-order. *)
  Definition public_first_order (ge: Senv.t) (m: mem) :=
    forall id b (PUBLIC: Senv.public_symbol ge id = true) (FIND: Senv.find_symbol ge id = Some b),
      block_first_order m b.

End AUX.

Section ASMISTEP.

  Variable cpm: compartment.
  Variable ge: genv.

  (* Parameter low_half: genv -> ident -> ptrofs -> ptrofs. *)
  (* Parameter high_half: genv -> ident -> ptrofs -> val. *)

  (* Axiom low_high_half: *)
  (*   forall id ofs, *)
  (*   Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs. *)

  Definition typ_to_eventval (ty: typ): eventval :=
    match ty with
    | Tint => EVint Int.zero
    | Tfloat => EVfloat Floats.Float.zero
    | Tlong => EVlong Int64.zero
    | Tsingle => EVsingle Floats.Float32.zero
    | Tany32 => EVint Int.zero
    | Tany64 => EVfloat Floats.Float.zero
    end.

  Definition typ_to_eventvals (ty: list typ): list eventval := map typ_to_eventval ty.

  Definition genv_invert_symbol_total {F V : Type} (ge : Genv.t F V) : block -> ident :=
    fun b => match Genv.invert_symbol ge b with | Some i => i | None => xH end.

  Inductive call_trace_vr {F V : Type} (ge : Genv.t F V) : compartment -> compartment -> val -> list val -> list typ -> trace -> Prop :=
    call_trace_vr_intra : forall (cp cp' : compartment) (vf : val) (vargs : list val) (ty : list typ),
        Genv.type_of_call ge cp cp' = Genv.InternalCall -> call_trace_vr ge cp cp' vf vargs ty E0
  | call_trace_vr_virtual : forall (cp cp' : compartment) (vf : val) (vargs : list val) (vl : list eventval) (ty : list typ) (b : block) (ofs : ptrofs) (i : ident),
      Genv.type_of_call ge cp cp' = Genv.DefaultCompartmentCall ->
      vf = Vptr b ofs -> genv_invert_symbol_total ge b = i -> (vl = typ_to_eventvals ty) -> call_trace_vr ge cp cp' vf vargs ty (Event_call cp cp' i vl :: nil)
  | call_trace_vr_cross : forall (cp cp' : compartment) (vf : val) (vargs : list val) (vl : list eventval) (ty : list typ) (b : block) (ofs : ptrofs) (i : ident),
      Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall ->
      vf = Vptr b ofs -> Genv.invert_symbol ge b = Some i -> eventval_list_match ge vl ty vargs -> call_trace_vr ge cp cp' vf vargs ty (Event_call cp cp' i vl :: nil).

  Inductive return_trace_vr {F V : Type} (ge : Genv.t F V) : compartment -> compartment -> val -> rettype -> trace -> Prop :=
    return_trace_vr_intra : forall (cp cp' : compartment) (v : val) (ty : rettype),
        Genv.type_of_call ge cp cp' = Genv.InternalCall -> return_trace_vr ge cp cp' v ty E0
  | return_trace_vr_virtual : forall (cp cp' : compartment) (res : eventval) (v : val) (ty : rettype),
      Genv.type_of_call ge cp cp' = Genv.DefaultCompartmentCall -> (res = typ_to_eventval (proj_rettype ty)) -> return_trace_vr ge cp cp' v ty (Event_return cp cp' res :: nil)
  | return_trace_vr_cross : forall (cp cp' : compartment) (res : eventval) (v : val) (ty : rettype),
      Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall -> eventval_match ge res (proj_rettype ty) v -> return_trace_vr ge cp cp' v ty (Event_return cp cp' res :: nil).

  Variant asm_istep: state -> itrace -> state -> Prop :=
  | exec_asm_istep_internal:
    forall b ofs f i rs m rs' m' b' ofs' st cp,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      forall (COMP: comp_of f = cp),
        exec_instr ge f i rs m cp = Next rs' m' ->
        sig_call i = None ->
        is_return i = false ->
        forall (NEXTPC: rs' PC = Vptr b' ofs'),
        forall (ALLOWED: cp = Genv.find_comp_ignore_offset ge (Vptr b' ofs')),
          asm_istep (State st rs m) nil (State st rs' m')
  | exec_asm_istep_internal_call:
    forall b ofs f i sig rs m rs' m' b' ofs' cp st st' args t it,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f i rs m cp = Next rs' m' ->
      sig_call i = Some sig ->
      forall (NEXTPC: rs' PC = Vptr b' ofs'),
      forall (ALLOWED: Genv.allowed_call ge (comp_of f) (Vptr b' ofs')),
      forall (CURCOMP: Genv.find_comp_ignore_offset ge (Vptr b Ptrofs.zero) = cp),
      (* Is a call, we update the stack *)
      forall (STUPD: update_stack_call ge st sig cp rs' = Some st'),
      forall (ARGS: call_arguments rs' m' sig args),
      (* Is a call, we check whether we are allowed to pass pointers *)
      forall (NO_CROSS_PTR:
          Genv.type_of_call ge (comp_of f) (Genv.find_comp_ignore_offset ge (Vptr b' ofs')) = Genv.CrossCompartmentCall ->
          List.Forall not_ptr args),
      forall (EV: call_trace_vr ge (comp_of f) (Genv.find_comp_ignore_offset ge (Vptr b' ofs')) (Vptr b' ofs')
                           args (sig_args sig) t),
      forall (INFO: let ce := match (Genv.find_funct_ptr ge b', (comp_of f) =? (Genv.find_comp_ignore_offset ge (Vptr b' ofs'))) with
                         | (Some (External ef), false) => is_cross_ext
                         | _ => not_cross_ext
                         end in
               let vr := match Genv.type_of_call ge (comp_of f) (Genv.find_comp_ignore_offset ge (Vptr b' ofs')) with
                         | Genv.DefaultCompartmentCall => is_virtual
                         | _ => is_real
                         end in
               it = map (fun e => (e, info_call ce sig vr)) t),
      forall (CALLSIG: Genv.type_of_call ge (comp_of f) (Genv.find_comp_ignore_offset ge (Vptr b' ofs')) <> Genv.InternalCall ->
                    (exists fd, Genv.find_funct_ptr ge b' = Some fd /\ sig = Asm.funsig fd)),
      forall (CPEQ: cp = (comp_of f)),
        asm_istep (State st rs m) it (State st' rs' m')
  | exec_asm_istep_internal_return:
    forall b ofs f i rs m rs' cp m' st,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f i rs m cp = Next rs' m' ->
      is_return i = true ->
      forall (CURCOMP: Genv.find_comp_ignore_offset ge (rs PC) = cp),
      (* We attempt a return, so we go to a ReturnState*)
      (* The only condition is the following: we are currently in the compartment stored in the callee compartment field *)
      (*      of the top stack frame*)
      forall (REC_CURCOMP: Genv.find_comp_ignore_offset ge (rs PC) = callee_comp cpm st),
        (* forall (NEXTCOMP: Genv.find_comp_ignore_offset ge (rs' PC) = cp'), *)
        asm_istep (State st rs m) nil (ReturnState st rs' m')
  | exec_asm_istep_return:
    forall st st' rs m sg t rec_cp rec_cp' cp' it,
      rs PC <> Vnullptr -> (* this condition is there to stop the execution 1 asm_istep earlier, to make the proof easier *)
      forall (REC_CURCOMP: callee_comp cpm st = rec_cp),
      forall (REC_NEXTCOMP: call_comp ge st = rec_cp'),
      forall (NEXTCOMP: Genv.find_comp_ignore_offset ge (rs PC) = cp'),
      (* We only impose conditions on when returns can be executed for cross-compartment *)
      (*          returns. These conditions are that we restore the previous RA and SP *)
      forall (PC_RA: rec_cp <> cp' -> rs PC = asm_parent_ra st),
      forall (RESTORE_SP: rec_cp <> cp' -> rs SP = asm_parent_sp st),
      (* forall (RETURN_FROM_CP: cp <> cp' -> cp = callee_comp st), *)
      (* Note that in the same manner, this definition only updates the stack when doing *)
      (*        cross-compartment returns *)
      forall (STUPD: update_stack_return ge st rec_cp rs = Some st'),
      (* We do not return a pointer *)
      forall (SIG_STACK: sig_of_call st = sg),
      forall (NO_CROSS_PTR:
          (Genv.type_of_call ge cp' rec_cp = Genv.CrossCompartmentCall ->
           not_ptr (return_value rs sg))),
      forall (EV: return_trace_vr ge cp' rec_cp (return_value rs sg) (sig_res sg) t),
      forall (INFO: let vr := match Genv.type_of_call ge cp' rec_cp with
                         | Genv.DefaultCompartmentCall => is_virtual
                         | _ => is_real
                         end in
               it = map (fun e => (e, info_return sg vr)) t),
        asm_istep (ReturnState st rs m) it (State st' rs m)
    | exec_asm_istep_builtin:
    forall b ofs f ef args res rs m vargs t vres rs' m' st it,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge (comp_of f) vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                       (undef_regs (map preg_of (destroyed_by_builtin ef))
                                   (rs #X1 <- Vundef #X31 <- Vundef))) ->
      forall (INFO: it = map (fun e => (e, info_builtin ef)) t),
        asm_istep (State st rs m) it (State st rs' m')
  | exec_asm_istep_external:
    forall b ef args res rs m t rs' m' cp st it,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      forall COMP: Genv.find_comp_ignore_offset ge (rs RA) = cp, (* compartment that is calling the external function *)
        external_call ef ge cp args m t res m' ->
        extcall_arguments rs m (ef_sig ef) args ->
        rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
        (* These steps behave like returns. So we do the same as in the [exec_asm_istep_internal_return] case. *)
        forall (REC_CURCOMP: Genv.find_comp_ignore_offset ge (rs PC) = callee_comp cpm st),
        forall (INFO: it = map (fun e => (e, info_external b (ef_sig ef))) t),
        forall (PFO: public_first_order ge m),
          asm_istep (State st rs m) it (ReturnState st rs' m').

  (* TODO: fix all the semantics, add CALLSIG and PFO *)

End ASMISTEP.


Section ASMITR.

  Definition asm_has_initial_trace_informative (p: Asm.program) (t: itrace) :=
    semantics_has_initial_trace_informative (semantics p) (asm_istep (comp_of_main p)) t.

  Definition asm_has_initial_trace (p: Asm.program) (t: trace): Prop := semantics_has_initial_trace_prefix (Asm.semantics p) t.


  (* TODO: fix Asm sem *)
  Lemma asm_star_tr_implies_istar_info_tr
        (p: Asm.program) (t: trace)
        (s s': Asm.state)
        (STAR: Star (semantics p) s t s')
    :
    exists it, (state_has_trace_informative (semantics p) s (asm_istep (comp_of_main p)) it) /\ (itr_to_tr it = t).
  Proof.
    simpl in STAR. induction STAR.
    { exists nil. simpl; split; auto. exists s. econstructor 1. }
    destruct IHSTAR as (it & (s2' & ISTAR) & ITR). subst.
    move H after ISTAR. inv H.
    - exists (it). simpl. split; [|auto]. exists s2'. econstructor 2. 2: eapply ISTAR.
      { econstructor 1; eauto. simpl. rewrite ALLOWED in H3. unfold Genv.find_comp_ignore_offset in H3. auto. }
      auto.
    - pose proof EV as EV0.
      destruct (Genv.type_of_call (Genv.globalenv p) (comp_of f) (Genv.find_comp_ignore_offset (Genv.globalenv p) (Vptr b' ofs'))) eqn:CCASES.
      + inv EV0. 2: rewrite CCASES in H; inv H.
        exists (it). simpl. split; [|auto]. exists s2'. econstructor 2. 2: eapply ISTAR.
        { econstructor 2; eauto.
          - simpl. setoid_rewrite CCASES. intros F; inv F.
          - econstructor 1. auto.
          - simpl. setoid_rewrite CCASES. intros F; contradiction F. auto.
          - simpl. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr. rewrite H1. auto.
        }
        auto.
      + inv EV0. rewrite CCASES in H. congruence with H.
        assert (CASES: (exists ef, Genv.find_funct_ptr (Genv.globalenv p) b' = Some (External ef)) \/
                         ((exists intf, Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal intf)) \/ (Genv.find_funct_ptr (Genv.globalenv p) b' = None))).
        { destruct (Genv.find_funct_ptr (Genv.globalenv p) b') eqn:CASES; [|auto]. destruct f0; eauto. }
        destruct CASES as [EXT | ELSE].
        * exists ((Event_call (comp_of f) (Genv.find_comp_ignore_offset (Genv.globalenv p) (Vptr b' ofs')) i0 vl, info_call is_cross_ext sig is_real) :: it). simpl. split; [|auto].
          exists s2'. econstructor 2. 2: eapply ISTAR.
          { econstructor 2; eauto.
            - simpl. econstructor 3; eauto.
            - admit. (* signature *)
            - simpl. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr. rewrite H1. auto.
          }
          simpl. destruct EXT. rewrite H8. unfold Genv.find_comp_ignore_offset in H. rewrite H.
          clear - H. unfold Genv.type_of_call in H. destruct (comp_of f =? Genv.find_comp (Genv.globalenv p) (Vptr b' Ptrofs.zero)). inv H. auto.
        * exists ((Event_call (comp_of f) (Genv.find_comp_ignore_offset (Genv.globalenv p) (Vptr b' ofs')) i0 vl, info_call not_cross_ext sig is_real) :: it). simpl. split; [|auto].
          exists s2'. econstructor 2. 2: eapply ISTAR.
          { econstructor 2; eauto.
            - simpl. econstructor 3; eauto.
            - admit. (* signature *)
            - simpl. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr. rewrite H1. auto.
          }
          simpl. unfold Genv.find_comp_ignore_offset in H. rewrite H. destruct ELSE. destruct H8. rewrite H8. auto. rewrite H8. auto.
      + inv EV0.
        2:{ rewrite CCASES in H. inv H. }
        assert (CASES: (exists ef, Genv.find_funct_ptr (Genv.globalenv p) b' = Some (External ef)) \/
                         ((exists intf, Genv.find_funct_ptr (Genv.globalenv p) b' = Some (Internal intf)) \/ (Genv.find_funct_ptr (Genv.globalenv p) b' = None))).
        { destruct (Genv.find_funct_ptr (Genv.globalenv p) b') eqn:CASES; [|auto]. destruct f0; eauto. }
        destruct (Genv.invert_symbol (Genv.globalenv p) b') eqn:SYMB.
        2:{ destruct CASES as [EXT | ELSE].
            * exists ((Event_call (comp_of f) (Genv.find_comp_ignore_offset (Genv.globalenv p) (Vptr b' ofs')) xH (typ_to_eventvals (sig_args sig)), info_call is_cross_ext sig is_virtual) :: it). simpl. split; [|auto].
              exists s2'. econstructor 2. 2: eapply ISTAR.
              { econstructor 2; eauto.
                - setoid_rewrite CCASES. intros F; inv F.
                - simpl. econstructor 2; eauto.
                - admit. (* signature *)
                - simpl. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr. rewrite H1. auto.
              }
              simpl. destruct EXT. rewrite H5. unfold Genv.find_comp_ignore_offset in CCASES. rewrite CCASES.
              unfold genv_invert_symbol_total. rewrite SYMB.
              clear - CCASES. unfold Genv.type_of_call in CCASES. destruct (comp_of f =? Genv.find_comp (Genv.globalenv p) (Vptr b' Ptrofs.zero)); auto. inv CCASES.
            * exists ((Event_call (comp_of f) (Genv.find_comp_ignore_offset (Genv.globalenv p) (Vptr b' ofs')) xH (typ_to_eventvals (sig_args sig)), info_call not_cross_ext sig is_virtual) :: it). simpl. split; [|auto].
              exists s2'. econstructor 2. 2: eapply ISTAR.
              { econstructor 2; eauto.
                - setoid_rewrite CCASES. intros F; inv F.
                - simpl. econstructor 2; eauto.
                - admit. (* signature *)
                - simpl. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr. rewrite H1. auto.
              }
              simpl. unfold Genv.find_comp_ignore_offset in CCASES. rewrite CCASES. unfold genv_invert_symbol_total. rewrite SYMB. destruct ELSE.
              destruct H5; rewrite H5. auto. rewrite H5. auto.
        }
        destruct CASES as [EXT | ELSE].
        * exists ((Event_call (comp_of f) (Genv.find_comp_ignore_offset (Genv.globalenv p) (Vptr b' ofs')) i0 (typ_to_eventvals (sig_args sig)), info_call is_cross_ext sig is_virtual) :: it). simpl. split; [|auto].
          exists s2'. econstructor 2. 2: eapply ISTAR.
          { econstructor 2; eauto.
            - setoid_rewrite CCASES. intros F; inv F.
            - simpl. econstructor 2; eauto.
            - admit. (* signature *)
            - simpl. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr. rewrite H1. auto.
          }
          simpl. destruct EXT. rewrite H5. unfold Genv.find_comp_ignore_offset in CCASES. rewrite CCASES.
          unfold genv_invert_symbol_total. rewrite SYMB.
          clear - CCASES. unfold Genv.type_of_call in CCASES. destruct (comp_of f =? Genv.find_comp (Genv.globalenv p) (Vptr b' Ptrofs.zero)); auto. inv CCASES.
        * exists ((Event_call (comp_of f) (Genv.find_comp_ignore_offset (Genv.globalenv p) (Vptr b' ofs')) i0 (typ_to_eventvals (sig_args sig)), info_call not_cross_ext sig is_virtual) :: it). simpl. split; [|auto].
          exists s2'. econstructor 2. 2: eapply ISTAR.
          { econstructor 2; eauto.
            - setoid_rewrite CCASES. intros F; inv F.
            - simpl. econstructor 2; eauto.
            - admit. (* signature *)
            - simpl. unfold Genv.find_comp. rewrite Genv.find_funct_find_funct_ptr. rewrite H1. auto.
          }
          simpl. unfold Genv.find_comp_ignore_offset in CCASES. rewrite CCASES. unfold genv_invert_symbol_total. rewrite SYMB. destruct ELSE.
          destruct H5; rewrite H5. auto. rewrite H5. auto.
    - exists (it). simpl. split; [|auto]. exists s2'. econstructor 2. 2: eapply ISTAR.
      { econstructor 3; eauto. }
      auto.
    - pose proof EV as EV0.
      destruct (Genv.type_of_call (Genv.globalenv p) (Genv.find_comp_ignore_offset (Genv.globalenv p) (rs PC)) (callee_comp (comp_of_main p) st)) eqn:CCASES.
      + inv EV0.
        2:{ rewrite CCASES in H. inv H. }
        exists (it). simpl. split; [|auto]. exists s2'. econstructor 2. 2: eapply ISTAR.
        { econstructor 4; eauto.
          - simpl. rewrite CCASES. intros F; inv F.
          - econstructor 1; auto.
        }
        auto.
      + inv EV0. rewrite CCASES in H. congruence with H.
        exists ((Event_return (Genv.find_comp_ignore_offset (Genv.globalenv p) (rs PC)) (callee_comp (comp_of_main p) st) res, info_return (sig_of_call st) is_real) :: it).
        simpl. split; [|auto]. exists s2'. econstructor 2. 2: eapply ISTAR.
        { econstructor 4; eauto. econstructor 3; eauto. }
        simpl. rewrite CCASES. auto.
      + inv EV0.
        2:{ rewrite CCASES in H. inv H. }
        exists ((Event_return (Genv.find_comp_ignore_offset (Genv.globalenv p) (rs PC)) (callee_comp (comp_of_main p) st) (typ_to_eventval (proj_rettype (sig_res (sig_of_call st)))), info_return (sig_of_call st) is_virtual) :: it).
        simpl. split; [|auto]. exists s2'. econstructor 2. 2: eapply ISTAR.
        { econstructor 4; eauto.
          - simpl. rewrite CCASES. intros F; inv F.
          - econstructor 2; eauto.
        }
        simpl. rewrite CCASES. auto.
    - exists ((map (fun e => (e, info_builtin ef)) t1) ++ it). simpl; split.
      2:{ rewrite itr_to_tr_app. unfold Eapp. f_equal. unfold itr_to_tr. rewrite filter_map; simpl; auto. rewrite map_map. simpl. apply map_id. }
      exists s2'. econstructor 2. 2: eapply ISTAR.
      { econstructor 5; eauto. }
      auto.
    - exists ((map (fun e => (e, info_external b (ef_sig ef))) t1) ++ it). simpl; split.
      2:{ rewrite itr_to_tr_app. unfold Eapp. f_equal. unfold itr_to_tr. rewrite filter_map; simpl; auto. rewrite map_map. simpl. apply map_id. }
      exists s2'. econstructor 2. 2: eapply ISTAR.
      { econstructor 6; eauto.
        admit. (* public first order *)
      }
      auto.
  Admitted.

  Lemma asm_tr_implies_info_tr
        (p: Asm.program) (t: trace)
        (HAS: asm_has_initial_trace p t)
    :
    exists (it: itrace), (asm_has_initial_trace_informative p it) /\ (itr_to_tr it = t).
  Proof.
    apply semantics_has_initial_trace_prefix_implies_cut in HAS. 2: apply sd_traces; apply Asm.semantics_determinate.
    unfold asm_has_initial_trace_informative. inv HAS.
    2:{ exists nil. simpl; split; auto. econstructor 2; auto. }
    destruct H0 as (s' & beh & STAR & BEH). exploit asm_star_tr_implies_istar_info_tr; eauto. intros (it & STTRIF & ITRTR).
    exists it. split; [|auto]. econstructor 1; eauto.
  Qed.

End ASMITR.
