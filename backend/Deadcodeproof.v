(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Elimination of unneeded computations over RTL: correctness proof. *)

Require Import FunInd.
Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import ValueDomain ValueAnalysis NeedDomain NeedOp Deadcode.

Definition match_prog (prog tprog: RTL.program) :=
  match_program (fun cu f tf => transf_fundef (romem_for cu) f = OK tf) eq prog tprog.

#[global]
Instance comp_transf_function rm: has_comp_transl_partial (transf_function rm).
Proof.
  unfold transf_function.
  intros f ? H.
  destruct analyze; try easy.
  now inv H.
Qed.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(** * Relating the memory states *)

(** The [magree] predicate is a variant of [Mem.extends] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [lessdef] relation. *)

Definition locset := block -> Z -> Prop.

Record magree (m1 m2: mem) (P: locset) : Prop := mk_magree {
  ma_perm:
    forall b ofs k p,
      Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p;
  ma_access:
    forall b cp,
      Mem.can_access_block m1 b cp -> Mem.can_access_block m2 b cp;
  ma_perm_inv:
    forall b ofs k p,
    Mem.perm m2 b ofs k p -> Mem.perm m1 b ofs k p \/ ~Mem.perm m1 b ofs Max Nonempty;
  ma_memval:
    forall b ofs,
    Mem.perm m1 b ofs Cur Readable ->
    P b ofs ->
    memval_lessdef (ZMap.get ofs (PMap.get b (Mem.mem_contents m1)))
                   (ZMap.get ofs (PMap.get b (Mem.mem_contents m2)));
  ma_nextblock:
    Mem.nextblock m2 = Mem.nextblock m1
}.

Lemma magree_monotone:
  forall m1 m2 (P Q: locset),
  magree m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree m1 m2 Q.
Proof.
  intros. destruct H. constructor; auto.
Qed.

Lemma mextends_agree:
  forall m1 m2 P, Mem.extends m1 m2 -> magree m1 m2 P.
Proof.
  intros. destruct H. destruct mext_inj. constructor; intros.
- replace ofs with (ofs + 0) by lia. eapply mi_perm; eauto. auto.
- eapply mi_own; eauto. unfold inject_id; reflexivity.
- eauto.
- exploit mi_memval; eauto. unfold inject_id; eauto.
  rewrite Z.add_0_r. auto.
- auto.
Qed.

Lemma magree_extends:
  forall m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree m1 m2 P -> Mem.extends m1 m2.
Proof.
  intros. destruct H0. constructor; auto. constructor; unfold inject_id; intros.
- inv H0. rewrite Z.add_0_r. eauto.
- inv H0. eapply ma_access0; eauto.
- inv H0. apply Z.divide_0_r.
- inv H0. rewrite Z.add_0_r. eapply ma_memval0; eauto.
Qed.

Lemma magree_loadbytes:
  forall m1 m2 P b ofs n cp bytes,
  magree m1 m2 P ->
  Mem.loadbytes m1 b ofs n cp = Some bytes ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  exists bytes', Mem.loadbytes m2 b ofs n cp = Some bytes' /\ list_forall2 memval_lessdef bytes bytes'.
Proof.
  assert (GETN: forall c1 c2 n ofs,
    (forall i, ofs <= i < ofs + Z.of_nat n -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    list_forall2 memval_lessdef (Mem.getN n ofs c1) (Mem.getN n ofs c2)).
  {
    induction n; intros; simpl.
    constructor.
    rewrite Nat2Z.inj_succ in H. constructor.
    apply H. lia.
    apply IHn. intros; apply H; lia.
  }
Local Transparent Mem.loadbytes.
  unfold Mem.loadbytes; intros. destruct H.
  destruct (Mem.range_perm_dec m1 b ofs (ofs + n) Cur Readable);
    destruct (Mem.can_access_block_dec m1 b cp);
    inv H0.
  setoid_rewrite pred_dec_true. simpl. econstructor; split; eauto.
  apply GETN. intros. rewrite Z_to_nat_max in H.
  assert (ofs <= i < ofs + n) by extlia.
  apply ma_memval0; auto.
  red; intros; eauto.
  eapply ma_access0; eauto.
Qed.

Lemma magree_load:
  forall m1 m2 P chunk b ofs cp v,
  magree m1 m2 P ->
  Mem.load chunk m1 b ofs cp = Some v ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  exists v', Mem.load chunk m2 b ofs cp = Some v' /\ Val.lessdef v v'.
Proof.
  intros. exploit Mem.load_valid_access; eauto. intros [A [B B']].
  exploit Mem.load_loadbytes; eauto. intros [bytes [C D]].
  exploit magree_loadbytes; eauto. intros [bytes' [E F]].
  exists (decode_val chunk bytes'); split.
  apply Mem.loadbytes_load; auto.
  apply val_inject_id. subst v. apply decode_val_inject; auto.
Qed.

Lemma magree_storebytes_parallel:
  forall m1 m2 (P Q: locset) b ofs bytes1 cp m1' bytes2,
  magree m1 m2 P ->
  Mem.storebytes m1 b ofs bytes1 cp = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + Z.of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2', Mem.storebytes m2 b ofs bytes2 cp = Some m2' /\ magree m1' m2' Q.
Proof.
  assert (SETN: forall (access: Z -> Prop) bytes1 bytes2,
    list_forall2 memval_lessdef bytes1 bytes2 ->
    forall p c1 c2,
    (forall i, access i -> i < p \/ p + Z.of_nat (length bytes1) <= i -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    forall q, access q ->
    memval_lessdef (ZMap.get q (Mem.setN bytes1 p c1))
                   (ZMap.get q (Mem.setN bytes2 p c2))).
  {
    induction 1; intros; simpl.
  - apply H; auto. simpl. lia.
  - simpl length in H1; rewrite Nat2Z.inj_succ in H1.
    apply IHlist_forall2; auto.
    intros. rewrite ! ZMap.gsspec. destruct (ZIndexed.eq i p). auto.
    apply H1; auto. unfold ZIndexed.t in *; lia.
  }
  intros.
  destruct (Mem.range_perm_storebytes m2 b ofs bytes2 cp) as [m2' ST2].
  { erewrite <- list_forall2_length by eauto. red; intros.
    eapply ma_perm; eauto.
    eapply Mem.storebytes_range_perm; eauto. }
  { eapply ma_access; eauto.
    eapply Mem.storebytes_can_access_block_1; eauto. }
  exists m2'; split; auto.
  constructor; intros.
- eapply Mem.perm_storebytes_1; eauto. eapply ma_perm; eauto.
  eapply Mem.perm_storebytes_2; eauto.
- eapply Mem.storebytes_can_access_block_inj_1; eauto. eapply ma_access; eauto.
  eapply Mem.storebytes_can_access_block_inj_2; eauto.
- exploit ma_perm_inv; eauto using Mem.perm_storebytes_2.
  intuition eauto using Mem.perm_storebytes_1, Mem.perm_storebytes_2.
- rewrite (Mem.storebytes_mem_contents _ _ _ _ _ _ H0).
  rewrite (Mem.storebytes_mem_contents _ _ _ _ _ _ ST2).
  rewrite ! PMap.gsspec. destruct (peq b0 b).
+ subst b0. apply SETN with (access := fun ofs => Mem.perm m1' b ofs Cur Readable /\ Q b ofs); auto.
  intros. destruct H5. eapply ma_memval; eauto.
  eapply Mem.perm_storebytes_2; eauto.
+ eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
- rewrite (Mem.nextblock_storebytes _ _ _ _ _ _ H0).
  rewrite (Mem.nextblock_storebytes _ _ _ _ _ _ ST2).
  eapply ma_nextblock; eauto.
Qed.

Lemma magree_store_parallel:
  forall m1 m2 (P Q: locset) chunk b ofs v1 cp m1' v2,
  magree m1 m2 P ->
  Mem.store chunk m1 b ofs v1 cp = Some m1' ->
  vagree v1 v2 (store_argument chunk) ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + size_chunk chunk <= i ->
                P b' i) ->
  exists m2', Mem.store chunk m2 b ofs v2 cp = Some m2' /\ magree m1' m2' Q.
Proof.
  intros.
  exploit Mem.store_valid_access_3; eauto. intros [A [B C]].
  exploit Mem.store_storebytes; eauto. intros SB1.
  exploit magree_storebytes_parallel. eauto. eauto.
  instantiate (1 := Q). intros. rewrite encode_val_length in H4.
  rewrite <- size_chunk_conv in H4. apply H2; auto.
  eapply store_argument_sound; eauto.
  intros [m2' [SB2 AG]].
  exists m2'; split; auto.
  apply Mem.storebytes_store; auto.
Qed.

Lemma magree_storebytes_left:
  forall m1 m2 P b ofs bytes1 cp m1',
  magree m1 m2 P ->
  Mem.storebytes m1 b ofs bytes1 cp = Some m1' ->
  (forall i, ofs <= i < ofs + Z.of_nat (length bytes1) -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. constructor; intros.
- eapply ma_perm; eauto. eapply Mem.perm_storebytes_2; eauto.
- eapply ma_access; eauto. eapply Mem.storebytes_can_access_block_inj_2; eauto.
- exploit ma_perm_inv; eauto.
  intuition eauto using Mem.perm_storebytes_1, Mem.perm_storebytes_2.
- rewrite (Mem.storebytes_mem_contents _ _ _ _ _ _ H0).
  rewrite PMap.gsspec. destruct (peq b0 b).
+ subst b0. rewrite Mem.setN_outside. eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
  destruct (zlt ofs0 ofs); auto. destruct (zle (ofs + Z.of_nat (length bytes1)) ofs0); try lia.
  elim (H1 ofs0). lia. auto.
+ eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
- rewrite (Mem.nextblock_storebytes _ _ _ _ _ _ H0).
  eapply ma_nextblock; eauto.
Qed.

Lemma magree_store_left:
  forall m1 m2 P chunk b ofs v1 cp m1',
  magree m1 m2 P ->
  Mem.store chunk m1 b ofs v1 cp = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. eapply magree_storebytes_left; eauto.
  eapply Mem.store_storebytes; eauto.
  intros. rewrite encode_val_length in H2.
  rewrite <- size_chunk_conv in H2. apply H1; auto.
Qed.

Lemma magree_free:
  forall m1 m2 (P Q: locset) b lo hi cp m1',
  magree m1 m2 P ->
  Mem.free m1 b lo hi cp = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ ~(lo <= i < hi) ->
                P b' i) ->
  exists m2', Mem.free m2 b lo hi cp = Some m2' /\ magree m1' m2' Q.
Proof.
  intros.
  destruct (Mem.range_perm_free m2 b lo hi cp) as [m2' FREE].
  red; intros. eapply ma_perm; eauto. eapply Mem.free_range_perm; eauto.
  eapply ma_access; eauto. eapply Mem.free_can_access_block_1; eauto.
  exists m2'; split; auto.
  constructor; intros.
- (* permissions *)
  assert (Mem.perm m2 b0 ofs k p). { eapply ma_perm; eauto. eapply Mem.perm_free_3; eauto. }
  exploit Mem.perm_free_inv; eauto. intros [[A B] | A]; auto.
  subst b0. eelim Mem.perm_free_2. eexact H0. eauto. eauto.
- (* access *)
  eapply Mem.free_can_access_block_inj_1; eauto. eapply ma_access; eauto.
  eapply Mem.free_can_access_block_inj_2; eauto.
- (* inverse permissions *)
  exploit ma_perm_inv; eauto using Mem.perm_free_3. intros [A|A].
  eapply Mem.perm_free_inv in A; eauto. destruct A as [[A B] | A]; auto.
  subst b0; right; eapply Mem.perm_free_2; eauto.
  right; intuition eauto using Mem.perm_free_3.
- (* contents *)
  rewrite (Mem.free_result _ _ _ _ _ _ H0).
  rewrite (Mem.free_result _ _ _ _ _ _ FREE).
  destruct (zle hi lo) eqn:R; unfold Mem.unchecked_free; rewrite R; eauto.
  + eapply ma_memval; eauto.
    eapply Mem.perm_free_3; eauto.
    apply H1; auto. destruct (eq_block b0 b); auto.
    subst b0. right. red; intros. eelim Mem.perm_free_2. eexact H0. eauto. eauto.
  + simpl. eapply ma_memval; eauto.
    eapply Mem.perm_free_3; eauto.
    apply H1; auto. destruct (eq_block b0 b); auto.
    subst b0. right. red; intros. eelim Mem.perm_free_2. eexact H0. eauto. eauto.
- (* nextblock *)
  rewrite (Mem.free_result _ _ _ _ _ _ H0).
  rewrite (Mem.free_result _ _ _ _ _ _ FREE).
  unfold Mem.unchecked_free; destruct (zle hi lo); simpl; eapply ma_nextblock; eauto.
Qed.

Lemma magree_valid_access:
  forall m1 m2 (P: locset) chunk b ofs p cp,
  magree m1 m2 P ->
  Mem.valid_access m1 chunk b ofs p cp ->
  Mem.valid_access m2 chunk b ofs p cp.
Proof.
  intros. destruct H0 as [? [? ?]]; split; auto.
  red; intros. eapply ma_perm; eauto.
  split; auto.
  eapply ma_access; eauto.
Qed.

(** * Properties of the need environment *)

Lemma add_need_all_eagree:
  forall e e' r ne,
  eagree e e' (add_need_all r ne) -> eagree e e' ne.
Proof.
  intros; red; intros. generalize (H r0). unfold add_need_all.
  rewrite NE.gsspec. destruct (peq r0 r); auto with na.
Qed.

Lemma add_need_all_lessdef:
  forall e e' r ne,
  eagree e e' (add_need_all r ne) -> Val.lessdef e#r e'#r.
Proof.
  intros. generalize (H r); unfold add_need_all.
  rewrite NE.gsspec, peq_true. auto with na.
Qed.

Lemma add_need_eagree:
  forall e e' r nv ne,
  eagree e e' (add_need r nv ne) -> eagree e e' ne.
Proof.
  intros; red; intros. generalize (H r0); unfold add_need.
  rewrite NE.gsspec. destruct (peq r0 r); auto.
  subst r0. intros. eapply nge_agree; eauto. apply nge_lub_r.
Qed.

Lemma add_need_vagree:
  forall e e' r nv ne,
  eagree e e' (add_need r nv ne) -> vagree e#r e'#r nv.
Proof.
  intros. generalize (H r); unfold add_need.
  rewrite NE.gsspec, peq_true. intros. eapply nge_agree; eauto. apply nge_lub_l.
Qed.

Lemma add_needs_all_eagree:
  forall rl e e' ne,
  eagree e e' (add_needs_all rl ne) -> eagree e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  apply IHrl. eapply add_need_all_eagree; eauto.
Qed.

Lemma add_needs_all_lessdef:
  forall rl e e' ne,
  eagree e e' (add_needs_all rl ne) -> Val.lessdef_list e##rl e'##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. eapply add_need_all_lessdef; eauto.
  eapply IHrl. eapply add_need_all_eagree; eauto.
Qed.

Lemma add_needs_eagree:
  forall rl nvl e e' ne,
  eagree e e' (add_needs rl nvl ne) -> eagree e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  destruct nvl. apply add_needs_all_eagree with (a :: rl); auto.
  eapply IHrl. eapply add_need_eagree; eauto.
Qed.

Lemma add_needs_vagree:
  forall rl nvl e e' ne,
  eagree e e' (add_needs rl nvl ne) -> vagree_list e##rl e'##rl nvl.
Proof.
  induction rl; simpl; intros.
  constructor.
  destruct nvl.
  apply vagree_lessdef_list. eapply add_needs_all_lessdef with (rl := a :: rl); eauto.
  constructor. eapply add_need_vagree; eauto.
  eapply IHrl. eapply add_need_eagree; eauto.
Qed.

Lemma add_ros_need_eagree:
  forall e e' ros ne, eagree e e' (add_ros_need_all ros ne) -> eagree e e' ne.
Proof.
  intros. destruct ros; simpl in *. eapply add_need_all_eagree; eauto. auto.
Qed.

Global Hint Resolve add_need_all_eagree add_need_all_lessdef
             add_need_eagree add_need_vagree
             add_needs_all_eagree add_needs_all_lessdef
             add_needs_eagree add_needs_vagree
             add_ros_need_eagree: na.

Lemma eagree_init_regs:
  forall rl vl1 vl2 ne,
  Val.lessdef_list vl1 vl2 ->
  eagree (init_regs vl1 rl) (init_regs vl2 rl) ne.
Proof.
  induction rl; intros until ne; intros LD; simpl.
- red; auto with na.
- inv LD.
  + red; auto with na.
  + apply eagree_update; auto with na.
Qed.

(** * Basic properties of the translation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists cu tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma allowed_call_translated:
  forall cp vf,
    Genv.allowed_call ge cp vf ->
    Genv.allowed_call tge cp vf.
Proof.
  intros cp vf H.
  eapply (Genv.match_genvs_allowed_calls TRANSF). eauto.
Qed.

Lemma find_comp_translated:
  forall vf,
    Genv.find_comp ge vf = Genv.find_comp tge vf.
Proof.
  intros vf.
  eapply (Genv.match_genvs_find_comp TRANSF).
Qed.

Lemma sig_function_translated:
  forall rm f tf,
  transf_fundef rm f = OK tf ->
  funsig tf = funsig f.
Proof.
  intros; destruct f; monadInv H.
  unfold transf_function in EQ.
  destruct (analyze (ValueAnalysis.analyze rm f) f); inv EQ; auto.
  auto.
Qed.

Lemma stacksize_translated:
  forall rm f tf,
  transf_function rm f = OK tf -> tf.(fn_stacksize) = f.(fn_stacksize).
Proof.
  unfold transf_function; intros. destruct (analyze (ValueAnalysis.analyze rm f) f); inv H; auto.
Qed.

Definition vanalyze (cu: program) (f: function) :=
  ValueAnalysis.analyze (romem_for cu) f.

Lemma transf_function_at:
  forall cu f tf an pc instr,
  transf_function (romem_for cu) f = OK tf ->
  analyze (vanalyze cu f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  tf.(fn_code)!pc = Some(transf_instr (vanalyze cu f) an pc instr).
Proof.
  intros. unfold transf_function in H. unfold vanalyze in H0. rewrite H0 in H. inv H; simpl.
  rewrite PTree.gmap. rewrite H1; auto.
Qed.

Lemma is_dead_sound_1:
  forall nv, is_dead nv = true -> nv = Nothing.
Proof.
  destruct nv; simpl; congruence.
Qed.

Lemma is_dead_sound_2:
  forall nv, is_dead nv = false -> nv <> Nothing.
Proof.
  intros; red; intros. subst nv; discriminate.
Qed.

Hint Resolve is_dead_sound_1 is_dead_sound_2: na.

Lemma is_int_zero_sound:
  forall nv, is_int_zero nv = true -> nv = I Int.zero.
Proof.
  unfold is_int_zero; destruct nv; try discriminate.
  predSpec Int.eq Int.eq_spec m Int.zero; congruence.
Qed.

Lemma find_function_translated:
  forall ros rs fd trs ne,
  find_function ge ros rs = Some fd ->
  eagree rs trs (add_ros_need_all ros ne) ->
  exists cu tfd,
     find_function tge ros trs = Some tfd
  /\ transf_fundef (romem_for cu) fd = OK tfd
  /\ linkorder cu prog.
Proof.
  unfold find_function.
  intros. destruct ros as [r|id]; simpl in *.
- assert (LD: Val.lessdef rs#r trs#r) by eauto with na. inv LD.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma find_function_ptr_translated:
  forall ros rs te ne fd vf,
    eagree rs te (add_ros_need_all ros ne) ->
    find_function ge ros rs = Some fd ->
    find_function_ptr ge ros rs = Some vf ->
    find_function_ptr tge ros te = Some vf.
Proof.
  unfold find_function.
  intros. destruct ros as [r|id]; simpl in *.
  - assert (LD: Val.lessdef rs#r te#r) by eauto with na. inv LD.
    congruence.
    rewrite <- H3 in H0; discriminate.
  - rewrite symbols_preserved. eauto.
Qed.

Lemma call_trace_translated:
  forall cp cp' vf ros res ne rs te args tyargs t,
    eagree rs te (add_needs_all args (add_ros_need_all ros (kill res ne))) ->
    (Genv.type_of_call cp cp' = Genv.CrossCompartmentCall -> Forall not_ptr (rs##args)) ->
    call_trace ge cp cp' vf (rs##args) tyargs t ->
    call_trace tge cp cp' vf (te##args) tyargs t.
Proof.
  intros cp cp' vf ros res ne rs te args tyargs t Hregs Hnoptr H.
  inv H.
  - constructor; eauto.
  - specialize (Hnoptr H0).
    econstructor; eauto.
    apply Genv.find_invert_symbol.
    rewrite symbols_preserved.
    apply Genv.invert_find_symbol; eauto.
    apply add_needs_all_lessdef with (rl := args) in Hregs.
    remember (rs ## args) as vargs.
    remember (te ## args) as vargs'.
    clear -vargs vargs' Hregs Hnoptr H3.
    revert vargs' tyargs vl Hregs Hnoptr H3.
    induction vargs; intros tvargs tyargs vl Hinj Hnoptr Hmatch.
    + inv Hinj; inv Hmatch; constructor.
    + inv Hinj; inv Hnoptr; inv Hmatch.
      constructor; eauto.
      inv H1; try contradiction;
        inv H7; econstructor; eauto.
      contradiction.
Qed.

(** * Semantic invariant *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall res ty f sp pc e tf te cu an
        (LINK: linkorder cu prog)
        (FUN: transf_function (romem_for cu) f = OK tf)
        (ANL: analyze (vanalyze cu f) f = Some an)
        (RES: forall v tv,
              Val.lessdef v tv ->
              eagree (e#res <- v) (te#res<- tv)
                     (fst (transfer f (vanalyze cu f) pc an!!pc))),
      match_stackframes (Stackframe res ty f (Vptr sp Ptrofs.zero) pc e)
                        (Stackframe res ty tf (Vptr sp Ptrofs.zero) pc te).

Lemma match_stacks_call_comp:
  forall s s',
  list_forall2 match_stackframes s s' ->
  call_comp s = call_comp s'.
Proof.
  intros ?? H.
  destruct H; trivial.
  match goal with
  | H : match_stackframes _ _ |- _ => destruct H
  end.
  simpl.
  now rewrite (comp_transl_partial _ FUN).
Qed.

Inductive match_states: state -> state -> Prop :=
  | match_regular_states:
      forall s f sp pc e m ts tf te tm cu an
        (STACKS: list_forall2 match_stackframes s ts)
        (LINK: linkorder cu prog)
        (FUN: transf_function (romem_for cu) f = OK tf)
        (ANL: analyze (vanalyze cu f) f = Some an)
        (ENV: eagree e te (fst (transfer f (vanalyze cu f) pc an!!pc)))
        (MEM: magree m tm (nlive ge sp (snd (transfer f (vanalyze cu f) pc an!!pc)))),
      match_states (State s f (Vptr sp Ptrofs.zero) pc e m)
                   (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
  | match_call_states:
      forall s f args m ts tf targs tm cu
        (STACKS: list_forall2 match_stackframes s ts)
        (LINK: linkorder cu prog)
        (FUN: transf_fundef (romem_for cu) f = OK tf)
        (ARGS: Val.lessdef_list args targs)
        (MEM: Mem.extends m tm),
      match_states (Callstate s f args m)
                   (Callstate ts tf targs tm)
  | match_return_states:
      forall s v m cp ts tv tm
        (STACKS: list_forall2 match_stackframes s ts)
        (RES: Val.lessdef v tv)
        (MEM: Mem.extends m tm),
      match_states (Returnstate s v m cp)
                   (Returnstate ts tv tm cp).

(** [match_states] and CFG successors *)

Lemma analyze_successors:
  forall cu f an pc instr pc',
  analyze (vanalyze cu f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  NA.ge an!!pc (transfer f (vanalyze cu f) pc' an!!pc').
Proof.
  intros. eapply DS.fixpoint_solution; eauto.
  intros. unfold transfer; rewrite H2. destruct a. apply DS.L.eq_refl.
Qed.

Lemma match_succ_states:
  forall s f sp pc e m ts tf te tm an pc' cu instr ne nm
    (LINK: linkorder cu prog)
    (STACKS: list_forall2 match_stackframes s ts)
    (FUN: transf_function (romem_for cu) f = OK tf)
    (ANL: analyze (vanalyze cu f) f = Some an)
    (INSTR: f.(fn_code)!pc = Some instr)
    (SUCC: In pc' (successors_instr instr))
    (ANPC: an!!pc = (ne, nm))
    (ENV: eagree e te ne)
    (MEM: magree m tm (nlive ge sp nm)),
  match_states (State s f (Vptr sp Ptrofs.zero) pc' e m)
               (State ts tf (Vptr sp Ptrofs.zero) pc' te tm).
Proof.
  intros. exploit analyze_successors; eauto. rewrite ANPC; simpl. intros [A B].
  econstructor; eauto.
  eapply eagree_ge; eauto.
  eapply magree_monotone; eauto.
Qed.

(** Builtin arguments and results *)

Lemma eagree_set_res:
  forall e1 e2 v1 v2 res ne,
  Val.lessdef v1 v2 ->
  eagree e1 e2 (kill_builtin_res res ne) ->
  eagree (regmap_setres res v1 e1) (regmap_setres res v2 e2) ne.
Proof.
  intros. destruct res; simpl in *; auto.
  apply eagree_update; eauto. apply vagree_lessdef; auto.
Qed.

Lemma transfer_builtin_arg_sound:
  forall cp bc e e' sp m m' a v,
  eval_builtin_arg ge (fun r => e#r) cp (Vptr sp Ptrofs.zero) m a v ->
  forall nv ne1 nm1 ne2 nm2,
  transfer_builtin_arg nv (ne1, nm1) a = (ne2, nm2) ->
  eagree e e' ne2 ->
  magree m m' (nlive ge sp nm2) ->
  genv_match bc ge ->
  bc sp = BCstack ->
  exists v',
     eval_builtin_arg ge (fun r => e'#r) cp (Vptr sp Ptrofs.zero) m' a  v'
  /\ vagree v v' nv
  /\ eagree e e' ne1
  /\ magree m m' (nlive ge sp nm1).
Proof.
  induction 1; simpl; intros until nm2; intros TR EA MA GM SPM; inv TR.
- exists e'#x; intuition auto. constructor. eauto 2 with na. eauto 2 with na.
- exists (Vint n); intuition auto. constructor. apply vagree_same.
- exists (Vlong n); intuition auto. constructor. apply vagree_same.
- exists (Vfloat n); intuition auto. constructor. apply vagree_same.
- exists (Vsingle n); intuition auto. constructor. apply vagree_same.
- simpl in H. exploit magree_load; eauto.
  intros. eapply nlive_add; eauto with va. rewrite Ptrofs.add_zero_l in H0; auto.
  intros (v' & A & B).
  exists v'; intuition auto. eapply eval_BA_loadstack. simpl. eauto.
  apply vagree_lessdef; auto.
  eapply magree_monotone; eauto. intros; eapply incl_nmem_add; eauto.
- exists (Vptr sp (Ptrofs.add Ptrofs.zero ofs)); intuition auto with na. constructor.
- unfold Genv.symbol_address in H; simpl in H.
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; simpl in H; try discriminate.
  exploit magree_load; eauto.
  intros. eapply nlive_add; eauto. constructor. auto. admit. (* left *)
  apply GM; auto.
  intros (v' & A & B).
  exists v'; intuition auto.
  econstructor. simpl. unfold Genv.symbol_address; simpl; rewrite FS; eauto.
  apply vagree_lessdef; auto.
  eapply magree_monotone; eauto. intros; eapply incl_nmem_add; eauto.
- eexists; intuition auto with na. constructor. reflexivity.
  (* exists (Genv.symbol_address ge id ofs); intuition auto with na. constructor. *)
- destruct (transfer_builtin_arg All (ne1, nm1) hi) as [ne' nm'] eqn:TR.
  exploit IHeval_builtin_arg2; eauto. intros (vlo' & A & B & C & D).
  exploit IHeval_builtin_arg1; eauto. intros (vhi' & P & Q & R & S).
  exists (Val.longofwords vhi' vlo'); intuition auto.
  constructor; auto.
  apply vagree_lessdef.
  apply Val.longofwords_lessdef; apply lessdef_vagree; auto.
- destruct (transfer_builtin_arg All (ne1, nm1) a1) as [ne' nm'] eqn:TR.
  exploit IHeval_builtin_arg2; eauto. intros (v2' & A & B & C & D).
  exploit IHeval_builtin_arg1; eauto. intros (v1' & P & Q & R & S).
  econstructor; intuition auto.
  econstructor; eauto.
  destruct Archi.ptr64; auto using Val.add_lessdef, Val.addl_lessdef, vagree_lessdef, lessdef_vagree.
Admitted.

Lemma transfer_builtin_args_sound:
  forall cp e sp m e' m' bc al vl,
  eval_builtin_args ge (fun r => e#r) cp (Vptr sp Ptrofs.zero) m al vl ->
  forall ne1 nm1 ne2 nm2,
  transfer_builtin_args (ne1, nm1) al = (ne2, nm2) ->
  eagree e e' ne2 ->
  magree m m' (nlive ge sp nm2) ->
  genv_match bc ge ->
  bc sp = BCstack ->
  exists vl',
     eval_builtin_args ge (fun r => e'#r) cp (Vptr sp Ptrofs.zero) m' al vl'
  /\ Val.lessdef_list vl vl'
  /\ eagree e e' ne1
  /\ magree m m' (nlive ge sp nm1).
Proof.
Local Opaque transfer_builtin_arg.
  induction 1; simpl; intros.
- inv H. exists (@nil val); intuition auto. constructor.
- destruct (transfer_builtin_arg All (ne1, nm1) a1) as [ne' nm'] eqn:TR.
  exploit IHlist_forall2; eauto. intros (vs' & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound; eauto. intros (v1' & A2 & B2 & C2 & D2).
  exists (v1' :: vs'); intuition auto. constructor; auto.
Qed.

Lemma can_eval_builtin_arg:
  forall cp sp e m e' m' P,
  magree m m' P ->
  forall a v,
  eval_builtin_arg ge (fun r => e#r) cp (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => e'#r) cp (Vptr sp Ptrofs.zero) m' a v'.
Proof.
  intros until P; intros MA.
  assert (LD: forall chunk addr cp v,
              Mem.loadv chunk m addr cp = Some v ->
              exists v', Mem.loadv chunk m' addr cp = Some v').
  {
    intros. destruct addr; simpl in H; try discriminate.
    eapply Mem.valid_access_load. eapply magree_valid_access; eauto.
    eapply Mem.load_valid_access; eauto. }
  induction 1; try (econstructor; now constructor).
- exploit LD; eauto. intros (v' & A). exists v'; econstructor; eauto.
- exploit LD; eauto. intros (v' & A). exists v'; econstructor.
  unfold Genv.symbol_address in *. rewrite symbols_preserved. eassumption.
- destruct IHeval_builtin_arg1 as (v1' & A1).
  destruct IHeval_builtin_arg2 as (v2' & A2).
  exists (Val.longofwords v1' v2'); constructor; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1).
  destruct IHeval_builtin_arg2 as (v2' & A2).
  econstructor; econstructor; eauto.
Qed.

Lemma can_eval_builtin_args:
  forall cp sp e m e' m' P,
  magree m m' P ->
  forall al vl,
  eval_builtin_args ge (fun r => e#r) cp (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => e'#r) cp (Vptr sp Ptrofs.zero) m' al vl'.
Proof.
  induction 2.
- exists (@nil val); constructor.
- exploit can_eval_builtin_arg; eauto. intros (v' & A).
  destruct IHlist_forall2 as (vl' & B).
  exists (v' :: vl'); constructor; eauto.
Qed.

(** Properties of volatile memory accesses *)

Lemma transf_volatile_store:
  forall cp v1 v2 v1' v2' m tm chunk sp nm t v m',
  volatile_store_sem cp chunk ge (v1::v2::nil) m t v m' ->
  Val.lessdef v1 v1' ->
  vagree v2 v2' (store_argument chunk) ->
  magree m tm (nlive ge sp nm) ->
  v = Vundef /\
  exists tm', volatile_store_sem cp chunk ge (v1'::v2'::nil) tm t Vundef tm'
           /\ magree m' tm' (nlive ge sp nm).
Proof.
  intros. inv H. split; auto.
  inv H0. inv H9.
- (* volatile *)
  exists tm; split; auto. econstructor. econstructor; eauto.
  eapply eventval_match_lessdef; eauto. apply store_argument_load_result; auto.
- (* not volatile *)
  exploit magree_store_parallel. eauto. eauto. eauto.
  instantiate (1 := nlive ge sp nm). auto.
  intros (tm' & P & Q).
  exists tm'; split. econstructor. econstructor; eauto.
  eapply ma_access; eauto.
  auto.
Qed.

Lemma eagree_set_undef:
  forall e1 e2 ne r, eagree e1 e2 ne -> eagree (e1#r <- Vundef) e2 ne.
Proof.
  intros; red; intros. rewrite PMap.gsspec. destruct (peq r0 r); auto with na.
Qed.

(** * The simulation diagram *)

Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' -> sound_state prog S1 ->
  exists S2', step tge S1' t S2' /\ match_states S2 S2'.
Proof.

Ltac TransfInstr :=
  match goal with
  | [INSTR: (fn_code _)!_ = Some _,
     FUN: transf_function _ _ = OK _,
     ANL: analyze _ _ = Some _ |- _ ] =>
       generalize (transf_function_at _ _ _ _ _ _ FUN ANL INSTR);
       let TI := fresh "TI" in
       intro TI; unfold transf_instr in TI
  end.

Ltac UseTransfer :=
  match goal with
  | [INSTR: (fn_code _)!?pc = Some _,
     ANL: analyze _ _ = Some ?an |- _ ] =>
       destruct (an!!pc) as [ne nm] eqn:ANPC;
       unfold transfer in *;
       rewrite INSTR in *;
       simpl in *
  end.

  induction 1; intros S1' MS SS; inv MS.

- (* nop *)
  TransfInstr; UseTransfer.
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.

- (* op *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne res)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne res)) eqn:INTZERO;
  [idtac|destruct (operation_is_redundant op (nreg ne res)) eqn:REDUNDANT]].
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na.
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v := Vint Int.zero); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.
+ (* redundant operation *)
  destruct args.
  * (* kept as is because no arguments -- should never happen *)
  simpl in *.
  exploit needs_of_operation_sound. eapply ma_perm; eauto.
  eauto. instantiate (1 := nreg ne res). eauto with na. eauto with na. intros [tv [A B]].
  econstructor; split.
  eapply exec_Iop with (v := tv); eauto.
  rewrite <- A. rewrite <- comp_transf_function; eauto.
  apply eval_operation_preserved. exact symbols_preserved.
  admit. admit. admit.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  * (* turned into a move *)
  unfold fst in ENV. unfold snd in MEM. simpl in H0.
  assert (VA: vagree v te#r (nreg ne res)).
  { eapply operation_is_redundant_sound with (arg1' := te#r) (args' := te##args).
    eauto. eauto. exploit add_needs_vagree; eauto. }
  econstructor; split.
  eapply exec_Iop; eauto. simpl; reflexivity.
  eapply match_succ_states; eauto. simpl; auto.
  eapply eagree_update; eauto 2 with na.
+ (* preserved operation *)
  simpl in *.
  exploit needs_of_operation_sound. eapply ma_perm; eauto. eauto. eauto 2 with na. eauto with na.
  intros [tv [A B]].
  econstructor; split.
  eapply exec_Iop with (v := tv); eauto.
  rewrite <- A. rewrite <- comp_transf_function; eauto.
  apply eval_operation_preserved. exact symbols_preserved.
  admit. admit. admit.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.

- (* load *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne dst)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne dst)) eqn:INTZERO];
  simpl in *.
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na.
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v := Vint Int.zero); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.
+ (* preserved *)
  exploit eval_addressing_lessdef. eapply add_needs_all_lessdef; eauto. eauto.
  intros (ta & U & V). inv V; try discriminate.
  destruct ta; simpl in H1; try discriminate.
  exploit magree_load; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. apply nlive_add with bc (comp_of f) i; assumption.
  intros (tv & P & Q).
  econstructor; split.
  eapply exec_Iload with (a := Vptr b i). eauto.
  rewrite <- U.
  rewrite <- comp_transf_function; eauto.
  apply eval_addressing_preserved. exact symbols_preserved.
  admit. admit. admit.
  rewrite <- comp_transf_function; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto.

- (* store *)
  TransfInstr; UseTransfer.
  destruct (nmem_contains nm (aaddressing (vanalyze cu f) # pc addr args)
             (size_chunk chunk)) eqn:CONTAINS.
+ (* preserved *)
  simpl in *.
  exploit eval_addressing_lessdef. eapply add_needs_all_lessdef; eauto. eauto.
  intros (ta & U & V). inv V; try discriminate.
  destruct ta; simpl in H1; try discriminate.
  exploit magree_store_parallel. eauto. eauto. instantiate (1 := te#src). eauto with na.
  instantiate (1 := nlive ge sp0 nm).
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. apply nlive_remove with bc (comp_of f) b i; assumption.
  intros (tm' & P & Q).
  econstructor; split.
  eapply exec_Istore with (a := Vptr b i). eauto.
  rewrite <- U.
  rewrite <- comp_transf_function; eauto.
  apply eval_addressing_preserved. exact symbols_preserved.
  admit. admit. admit.
  rewrite <- comp_transf_function; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  eauto 3 with na.
+ (* dead instruction, turned into a nop *)
  destruct a; simpl in H1; try discriminate.
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  eapply magree_store_left; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.

- (* call *)
  TransfInstr; UseTransfer.
  exploit find_function_translated; eauto 2 with na. intros (cu' & tfd & A & B & C).
  exploit find_function_ptr_translated; eauto 2 with na. intros D.
  econstructor; split.
  eapply exec_Icall; eauto. eapply sig_function_translated; eauto.
  rewrite <- comp_transf_function; eauto.
  eapply allowed_call_translated; eauto.
  intros CROSS.
  (* TODO: write a lemma *)
  assert (eagree rs te (add_needs_all args (add_ros_need_all ros (kill res ne))) ->
          Forall not_ptr rs ## args ->
          Forall not_ptr te ## args).
  { clear. induction args.
    - eauto.
    - intros AG H.
      simpl in AG.
      inv H.
      constructor.
      + eapply add_need_all_lessdef in AG. inv AG; eauto.
        rewrite <- H0 in H2; inv H2.
      + eapply add_need_all_eagree in AG. eauto. }
  eapply H1; eauto. eapply NO_CROSS_PTR.
  rewrite (comp_transl_partial _ B).
  rewrite comp_transf_function; eauto.
  rewrite <- (comp_transl_partial _ B), <- comp_transf_function; eauto.
  eapply call_trace_translated; eauto.
  eapply match_call_states with (cu := cu'); eauto.
  constructor; auto. eapply match_stackframes_intro with (cu := cu); eauto.
  intros.
  edestruct analyze_successors; eauto. simpl; eauto.
  eapply eagree_ge; eauto. rewrite ANPC. simpl.
  apply eagree_update; eauto with na.
  eauto 2 with na.
  eapply magree_extends; eauto. apply nlive_all.

- (* tailcall *)
  TransfInstr; UseTransfer.
  exploit find_function_translated; eauto 2 with na. intros (cu' & tfd & A & B & L).
  exploit magree_free. eauto. eauto. instantiate (1 := nlive ge stk nmem_all).
  intros; eapply nlive_dead_stack; eauto.
  intros (tm' & C & D).
  (* exploit find_function_ptr_translated; eauto 2 with na. intros E. *)
  econstructor; split.
  eapply exec_Itailcall; eauto. eapply sig_function_translated; eauto.
  rewrite <- (comp_transl_partial _ B), COMP. now apply (comp_transl_partial _ FUN).
  erewrite stacksize_translated by eauto.
  rewrite <- comp_transf_function; eauto.
  eapply match_call_states with (cu := cu'); eauto 2 with na.
  eapply magree_extends; eauto. apply nlive_all.

- (* builtin *)
  TransfInstr; UseTransfer. revert ENV MEM TI.
  functional induction (transfer_builtin (vanalyze cu f)#pc ef args res ne nm);
  simpl in *; intros.
+ (* volatile load *)
  inv H0. inv H6. rename b1 into v1.
  destruct (transfer_builtin_arg All
              (kill_builtin_res res ne,
              nmem_add nm (aaddr_arg (vanalyze cu f) # pc a1)
                (size_chunk chunk)) a1) as (ne1, nm1) eqn: TR.
  InvSoundState. exploit transfer_builtin_arg_sound; eauto.
  intros (tv1 & A & B & C & D).
  unfold comp_of in ALLOWED; simpl in ALLOWED; subst _x.
  inv H1. simpl in B. inv B.
  assert (X: exists tvres, volatile_load ge (comp_of f) chunk tm b ofs t tvres /\ Val.lessdef vres tvres).
  {
    inv H2.
  * exists (Val.load_result chunk v); split; auto. constructor; auto.
  * exploit magree_load; eauto.
    exploit aaddr_arg_sound_1; eauto. rewrite <- AN. intros.
    intros. eapply nlive_add; eassumption.
    intros (tv & P & Q).
    exists tv; split; auto. econstructor; eauto.
    eapply ma_access; eauto.
  }
  destruct X as (tvres & P & Q).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  unfold comp_of. simpl. rewrite comp_transf_function; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  admit. admit. admit.
  constructor. rewrite <- comp_transf_function; eauto. constructor.
  rewrite comp_transf_function; eauto.
  eapply external_call_symbols_preserved. apply senv_preserved.
  constructor. rewrite <- comp_transf_function; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto.
+ (* volatile store *)
  inv H0. inv H6. inv H7. rename b1 into v1. rename b0 into v2.
  destruct (transfer_builtin_arg (store_argument chunk)
              (kill_builtin_res res ne, nm) a2) as (ne2, nm2) eqn: TR2.
  destruct (transfer_builtin_arg All (ne2, nm2) a1) as (ne1, nm1) eqn: TR1.
  InvSoundState.
  exploit transfer_builtin_arg_sound. eexact H4. eauto. eauto. eauto. eauto. eauto.
  intros (tv1 & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound. eexact H3. eauto. eauto. eauto. eauto. eauto.
  intros (tv2 & A2 & B2 & C2 & D2).
  exploit transf_volatile_store; eauto.
  intros (EQ & tm' & P & Q). subst vres.
  econstructor; split.
  eapply exec_Ibuiltin; eauto. rewrite <- comp_transf_function; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  admit. admit. admit.
  constructor. rewrite <- comp_transf_function; eauto. constructor.
  rewrite <- comp_transf_function; eauto. constructor.
  eapply external_call_symbols_preserved. apply senv_preserved.
  simpl; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* memcpy *)
  rewrite e1 in TI.
  inv H0. inv H6. inv H7. rename b1 into v1. rename b0 into v2.
  set (adst := aaddr_arg (vanalyze cu f) # pc dst) in *.
  set (asrc := aaddr_arg (vanalyze cu f) # pc src) in *.
  destruct (transfer_builtin_arg All
              (kill_builtin_res res ne,
               nmem_add (nmem_remove nm adst sz) asrc sz) dst)
           as (ne2, nm2) eqn: TR2.
  destruct (transfer_builtin_arg All (ne2, nm2) src) as (ne1, nm1) eqn: TR1.
  InvSoundState.
  exploit transfer_builtin_arg_sound. eexact H3. eauto. eauto. eauto. eauto. eauto.
  intros (tv1 & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound. eexact H4. eauto. eauto. eauto. eauto. eauto.
  intros (tv2 & A2 & B2 & C2 & D2).
  inv H1.
  exploit magree_loadbytes. eauto. eauto.
  intros. eapply nlive_add; eauto.
  unfold asrc, vanalyze; rewrite AN; eapply aaddr_arg_sound_1; eauto.
  intros (tbytes & P & Q).
  exploit magree_storebytes_parallel.
  eapply magree_monotone. eexact D2.
  instantiate (1 := nlive ge sp0 (nmem_remove nm adst sz)).
  intros. apply incl_nmem_add; auto.
  eauto.
  instantiate (1 := nlive ge sp0 nm).
  intros. eapply nlive_remove; eauto.
  unfold adst, vanalyze; rewrite AN; eapply aaddr_arg_sound_1; eauto.
  erewrite Mem.loadbytes_length in H1 by eauto.
  rewrite Z2Nat.id in H1 by lia. auto.
  eauto.
  intros (tm' & A & B).
  econstructor; split.
  eapply exec_Ibuiltin; eauto. rewrite <- comp_transf_function; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  admit. admit. admit.
  constructor. rewrite <- comp_transf_function; eauto.
  constructor. rewrite <- comp_transf_function; eauto. constructor.
  eapply external_call_symbols_preserved. apply senv_preserved.
  simpl in B1; inv B1. simpl in B2; inv B2. econstructor; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* memcpy eliminated *)
  rewrite e1 in TI.
  inv H0. inv H6. inv H7. rename b1 into v1. rename b0 into v2.
  set (adst := aaddr_arg (vanalyze cu f) # pc dst) in *.
  set (asrc := aaddr_arg (vanalyze cu f) # pc src) in *.
  inv H1.
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  destruct res; auto. apply eagree_set_undef; auto.
  eapply magree_storebytes_left; eauto.
  clear H3.
  exploit aaddr_arg_sound; eauto.
  intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.
  erewrite Mem.loadbytes_length in H0 by eauto.
  rewrite Z2Nat.id in H0 by lia. auto.
+ (* annot *)
  destruct (transfer_builtin_args (kill_builtin_res res ne, nm) _x3) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  inv H1.
  econstructor; split.
  eapply exec_Ibuiltin; eauto. rewrite <- comp_transf_function; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  admit. admit. admit.
  rewrite <- comp_transf_function; eauto.
  eapply external_call_symbols_preserved. apply senv_preserved.
  constructor. eapply eventval_list_match_lessdef; eauto 2 with na.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* annot val *)
  destruct (transfer_builtin_args (kill_builtin_res res ne, nm) _x3) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  inv H1. inv B. inv H6.
  econstructor; split.
  eapply exec_Ibuiltin; eauto. rewrite <- comp_transf_function; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  admit. admit. admit.
  rewrite <- comp_transf_function; eauto.
  eapply external_call_symbols_preserved. apply senv_preserved.
  constructor.
  eapply eventval_match_lessdef; eauto 2 with na.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* debug *)
  inv H1.
  exploit can_eval_builtin_args; eauto. intros (vargs' & A).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  rewrite <- comp_transf_function; eauto.
  rewrite <- comp_transf_function; eauto.
  constructor.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* all other builtins *)
  assert ((fn_code tf)!pc = Some(Ibuiltin _x _x0 res pc')).
  {
    destruct _x; auto. destruct _x0; auto. destruct _x0; auto. destruct _x0; auto. contradiction.
  }
  clear y TI.
  destruct (transfer_builtin_args (kill_builtin_res res ne, nmem_all) _x0) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  exploit external_call_mem_extends; eauto 2 with na.
  eapply magree_extends; eauto. intros. apply nlive_all.
  intros (v' & tm' & P & Q & R & S).
  econstructor; split.
  eapply exec_Ibuiltin; eauto. rewrite <- comp_transf_function; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  admit. admit. admit.
  rewrite <- comp_transf_function; eauto.
  eapply external_call_symbols_preserved. apply senv_preserved. eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
  eapply mextends_agree; eauto.

- (* conditional *)
  TransfInstr; UseTransfer. destruct (peq ifso ifnot).
+ replace (if b then ifso else ifnot) with ifso by (destruct b; congruence).
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
+ econstructor; split.
  eapply exec_Icond; eauto.
  eapply needs_of_condition_sound. eapply ma_perm; eauto. eauto. eauto with na.
  eapply match_succ_states; eauto 2 with na.
  simpl; destruct b; auto.

- (* jumptable *)
  TransfInstr; UseTransfer.
  assert (LD: Val.lessdef rs#arg te#arg) by eauto 2 with na.
  rewrite H0 in LD. inv LD.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  eapply match_succ_states; eauto 2 with na.
  simpl. eapply list_nth_z_in; eauto.

- (* return *)
  TransfInstr; UseTransfer.
  exploit magree_free. eauto. eauto. instantiate (1 := nlive ge stk nmem_all).
  intros; eapply nlive_dead_stack; eauto.
  intros (tm' & A & B).
  econstructor; split.
  eapply exec_Ireturn; eauto.
  erewrite stacksize_translated by eauto.
  rewrite <- comp_transf_function; eauto.
  unfold transf_function in FUN. destruct (analyze (ValueAnalysis.analyze (romem_for cu) f) f); inv FUN.
  constructor; auto.
  destruct or; simpl; eauto 2 with na.
  eapply magree_extends; eauto. apply nlive_all.

- (* internal function *)
  monadInv FUN. generalize EQ. unfold transf_function. fold (vanalyze cu f). intros EQ'.
  destruct (analyze (vanalyze cu f) f) as [an|] eqn:AN; inv EQ'.
  exploit Mem.alloc_extends; eauto. apply Z.le_refl. apply Z.le_refl.
  intros (tm' & A & B).
  econstructor; split.
  econstructor; simpl; eauto.
  simpl. econstructor; eauto.
  apply eagree_init_regs; auto.
  apply mextends_agree; auto.

- (* external function *)
  exploit external_call_mem_extends; eauto.
  intros (res' & tm' & A & B & C & D).
  simpl in FUN. inv FUN.
  econstructor; split.
  econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.

- (* return *)
  inv STACKS. inv H1.
  econstructor; split.
  constructor.
  rewrite <- comp_transf_function; eauto.
  intros G; specialize (NO_CROSS_PTR G); inv RES; auto; contradiction.
  rewrite <- comp_transf_function; eauto.
  now eapply return_trace_lessdef; eauto using senv_preserved.
  econstructor; eauto. apply mextends_agree; auto.
Admitted.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros (cu & tf & A & B & C).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply (Genv.init_mem_match TRANSF); eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. eapply sig_function_translated; eauto.
  econstructor; eauto. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor.
Qed.

(** * Semantic preservation *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  intros.
  apply forward_simulation_step with
     (match_states := fun s1 s2 => sound_state prog s1 /\ match_states s1 s2).
- apply senv_preserved.
- simpl; intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
  exists st2; intuition. eapply sound_initial; eauto.
- simpl; intros. destruct H. eapply transf_final_states; eauto.
- simpl; intros. destruct H0.
  assert (sound_state prog s1') by (eapply sound_step; eauto).
  fold ge; fold tge. exploit step_simulation; eauto. intros [st2' [A B]].
  exists st2'; auto.
Qed.

End PRESERVATION.
