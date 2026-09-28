(* Facts about [public_first_order] and [external_call_conds] for ordinary
   programs, on ccs-backtranslation.

   [public_first_order] and [external_call_conds] are the predicates used by
   the CHECKPUB and ECC premises of [Asm.step_fix] (riscV/Asm.v:1444,1482,
   1498,1511); both are defined in common/Events.v:2159-2230.

   Everything here is generic in the program type, so it applies to Clight
   programs as well as to Asm programs. *)

From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import Values AST Memdata Memory Events Globalenvs.

Definition is_byte (mv: memval) : Prop :=
  match mv with Byte _ => True | _ => False end.

(** * Reading memory contents through [Mem.loadbytes] *)

(* Memory.v ends with [Global Opaque Mem.loadbytes ...]; we unfold it here only
   to relate [Mem.loadbytes] to [Mem.mem_contents]. *)
Local Transparent Mem.loadbytes.

Lemma getN_in_inv:
  forall n p c mv, In mv (Mem.getN n p c) ->
  exists q, p <= q < p + Z.of_nat n /\ ZMap.get q c = mv.
Proof.
  induction n; simpl; intros p c mv H.
  - contradiction.
  - destruct H as [H|H].
    + exists p. split; [lia | auto].
    + apply IHn in H. destruct H as (q & R & E). exists q. split; [lia | auto].
Qed.

Lemma loadbytes_contents_inv:
  forall m b o n cp bytes mv,
  Mem.loadbytes m b o n cp = Some bytes -> In mv bytes ->
  exists q, o <= q < o + n /\ ZMap.get q (Mem.mem_contents m) !! b = mv.
Proof.
  intros m b o n cp bytes mv LB IN. unfold Mem.loadbytes in LB.
  destruct (_ && _); inv LB.
  apply getN_in_inv in IN. destruct IN as (q & R & E). exists q. split; auto.
  destruct (zle 0 n).
  - rewrite Z2Nat.id in R; lia.
  - destruct n; simpl in R; lia.
Qed.

Lemma loadbytes_contents:
  forall m b o n cp bytes q,
  Mem.loadbytes m b o n cp = Some bytes -> o <= q < o + n ->
  In (ZMap.get q (Mem.mem_contents m) !! b) bytes.
Proof.
  intros m b o n cp bytes q LB R. unfold Mem.loadbytes in LB.
  destruct (_ && _); inv LB.
  apply Mem.getN_in. rewrite Z2Nat.id by lia. lia.
Qed.

Section INIT.

Context {F V: Type} {CF: has_comp F}.

Definition init_data_no_addrof (i: init_data) : Prop :=
  match i with Init_addrof _ _ => False | _ => True end.

Lemma bytes_of_init_data_list_app:
  forall (ge: Genv.t F V) l1 l2,
  Genv.bytes_of_init_data_list ge (l1 ++ l2) =
  Genv.bytes_of_init_data_list ge l1 ++ Genv.bytes_of_init_data_list ge l2.
Proof.
  induction l1; simpl; intros; auto. rewrite IHl1, app_assoc. auto.
Qed.

(** The bytes of an [Init_addrof] initializer are never [Byte]s: they are
    the fragments of a pointer (or [Undef] if the symbol is not defined, in
    which case [Genv.init_mem] fails anyway). *)
Lemma addrof_bytes_non_byte:
  forall (ge: Genv.t F V) symb ofs,
  exists mv, In mv (Genv.bytes_of_init_data ge (Init_addrof symb ofs)) /\ ~ is_byte mv.
Proof.
  intros. simpl. destruct (Genv.find_symbol ge symb); destruct Archi.ptr64; simpl;
  eexists; (split; [left; reflexivity | simpl; tauto]).
Qed.

Lemma addrof_bytes_fragment:
  forall (ge: Genv.t F V) symb ofs bs,
  Genv.find_symbol ge symb = Some bs ->
  exists qt n, In (Fragment (Vptr bs ofs) qt n) (Genv.bytes_of_init_data ge (Init_addrof symb ofs)).
Proof.
  intros. simpl. rewrite H. destruct Archi.ptr64; simpl; do 2 eexists; left; reflexivity.
Qed.

Lemma no_addrof_bytes:
  forall (ge: Genv.t F V) i mv,
  init_data_no_addrof i -> In mv (Genv.bytes_of_init_data ge i) -> is_byte mv.
Proof.
  intros ge i mv NA IN. destruct i; simpl in *; try contradiction;
  try (unfold inj_bytes in IN; apply in_map_iff in IN; destruct IN as (x & <- & _); exact I).
  (* Init_space *)
  apply repeat_spec in IN. subst. exact I.
Qed.

Lemma no_addrof_list_bytes:
  forall (ge: Genv.t F V) il mv,
  Forall init_data_no_addrof il -> In mv (Genv.bytes_of_init_data_list ge il) -> is_byte mv.
Proof.
  induction il; simpl; intros mv FA IN.
  - contradiction.
  - inv FA. apply in_app_or in IN. destruct IN as [IN|IN].
    + eapply no_addrof_bytes; eauto.
    + eapply IHil; eauto.
Qed.

Lemma perm_globvar_readable:
  forall (gv: globvar V),
  gvar_volatile gv = false -> perm_order (Genv.perm_globvar gv) Readable.
Proof.
  intros. unfold Genv.perm_globvar. rewrite H. destruct (gvar_readonly gv); constructor.
Qed.

Lemma public_symbol_of_prog_public:
  forall (p: AST.program F V) id b,
  In id (prog_public p) ->
  Genv.find_symbol (Genv.globalenv p) id = Some b ->
  Senv.public_symbol (Genv.globalenv p) id = true.
Proof.
  intros. simpl. unfold Genv.public_symbol. rewrite H0. rewrite Genv.globalenv_public.
  destruct (In_dec ident_eq id (prog_public p)); [reflexivity | contradiction].
Qed.

(** ** Theorem 1: a public, non-volatile global variable whose initializer
    contains an address (C: [int *p = &x;], [char *msg = "hi";], a table of
    function pointers, a struct with a pointer field, ...) holds a pointer
    fragment in the initial memory, at a readable offset. *)
Theorem init_addrof_public_var_fragment:
  forall (p: AST.program F V) m id b gv pre symb ofs post bs,
  Genv.init_mem p = Some m ->
  Genv.find_symbol (Genv.globalenv p) id = Some b ->
  Genv.find_var_info (Genv.globalenv p) b = Some gv ->
  gvar_volatile gv = false ->
  gvar_init gv = pre ++ Init_addrof symb ofs :: post ->
  Genv.find_symbol (Genv.globalenv p) symb = Some bs ->
  exists q qt n,
    0 <= q < init_data_list_size (gvar_init gv) /\
    Mem.perm m b q Cur Readable /\
    ZMap.get q (Mem.mem_contents m) !! b = Fragment (Vptr bs ofs) qt n.
Proof.
  intros until bs. intros INIT FS FV NVOL INITD FSYM.
  exploit Genv.init_mem_characterization; eauto. intros (RP & _ & _ & LB).
  specialize (LB NVOL).
  destruct (addrof_bytes_fragment (Genv.globalenv p) symb ofs bs FSYM) as (qt & n & IN).
  assert (IN': In (Fragment (Vptr bs ofs) qt n) (Genv.bytes_of_init_data_list (Genv.globalenv p) (gvar_init gv))).
  { rewrite INITD, bytes_of_init_data_list_app. apply in_or_app. right. simpl.
    apply in_or_app. left. auto. }
  exploit loadbytes_contents_inv; eauto. intros (q & R & E).
  exists q, qt, n. split; [lia|]. split; auto.
  eapply Mem.perm_implies. apply RP. lia. apply perm_globvar_readable; auto.
Qed.

Theorem init_addrof_public_var_not_first_order:
  forall (p: AST.program F V) m id b gv pre symb ofs post,
  Genv.init_mem p = Some m ->
  In id (prog_public p) ->
  Genv.find_symbol (Genv.globalenv p) id = Some b ->
  Genv.find_var_info (Genv.globalenv p) b = Some gv ->
  gvar_volatile gv = false ->
  gvar_init gv = pre ++ Init_addrof symb ofs :: post ->
  ~ public_first_order (Genv.globalenv p) m.
Proof.
  intros until post. intros INIT PUB FS FV NVOL INITD.
  exploit Genv.init_mem_characterization; eauto. intros (RP & _ & _ & LB).
  specialize (LB NVOL).
  destruct (addrof_bytes_non_byte (Genv.globalenv p) symb ofs) as (mv & IN & NB).
  assert (IN': In mv (Genv.bytes_of_init_data_list (Genv.globalenv p) (gvar_init gv))).
  { rewrite INITD, bytes_of_init_data_list_app. apply in_or_app. right. simpl.
    apply in_or_app. left. auto. }
  exploit loadbytes_contents_inv; eauto. intros (q & R & E).
  intros PFO.
  assert (PERM: Mem.perm m b q Cur Readable).
  { eapply Mem.perm_implies. apply RP. lia. apply perm_globvar_readable; auto. }
  specialize (PFO id b q (public_symbol_of_prog_public p id b PUB FS) FS PERM).
  unfold loc_first_order in PFO. rewrite E in PFO. apply NB. destruct mv; simpl in *; auto.
Qed.

(** ** Theorem 2: a non-volatile variable whose initializer has no address
    (in particular a zero-initialized one, [Init_space], such as C's
    [int *q;] without initializer) is [Byte]-filled in the initial memory. *)
Theorem init_no_addrof_var_first_order:
  forall (p: AST.program F V) m b gv,
  Genv.init_mem p = Some m ->
  Genv.find_var_info (Genv.globalenv p) b = Some gv ->
  gvar_volatile gv = false ->
  Forall init_data_no_addrof (gvar_init gv) ->
  forall q, Mem.perm m b q Cur Readable -> loc_first_order m b q.
Proof.
  intros p m b gv INIT FV NVOL FA q PERM.
  exploit Genv.init_mem_characterization; eauto. intros (RP & PO & _ & LB).
  specialize (LB NVOL). exploit PO; eauto. intros (R & _).
  pose proof (loadbytes_contents _ _ _ _ _ _ q LB) as IN.
  specialize (IN ltac:(lia)).
  pose proof (no_addrof_list_bytes _ _ _ FA IN) as ISB.
  unfold loc_first_order. destruct (ZMap.get q (Mem.mem_contents m) !! b); simpl in *; auto.
Qed.

(** ** Theorem 3: characterization of [public_first_order] in the initial
    memory: it holds iff no public, non-volatile global variable has an
    [Init_addrof] in its initializer. *)

Lemma find_symbol_find_def:
  forall (p: AST.program F V) id b,
  Genv.find_symbol (Genv.globalenv p) id = Some b ->
  exists g, Genv.find_def (Genv.globalenv p) b = Some g.
Proof.
  intros. exploit Genv.find_symbol_inversion; eauto. intros IN.
  exploit prog_defmap_dom; eauto. intros (g & PD).
  apply Genv.find_def_symbol in PD. destruct PD as (b' & FS' & FD).
  rewrite H in FS'. inv FS'. eauto.
Qed.

Theorem init_mem_public_first_order_iff:
  forall (p: AST.program F V) m,
  Genv.init_mem p = Some m ->
  (public_first_order (Genv.globalenv p) m <->
   forall id b gv,
     In id (prog_public p) ->
     Genv.find_symbol (Genv.globalenv p) id = Some b ->
     Genv.find_var_info (Genv.globalenv p) b = Some gv ->
     gvar_volatile gv = false ->
     Forall init_data_no_addrof (gvar_init gv)).
Proof.
  intros p m INIT. split.
  - intros PFO id b gv PUB FS FV NVOL.
    apply Forall_forall. intros i IN.
    destruct i; simpl; auto.
    apply in_split in IN. destruct IN as (pre & post & EQ).
    eapply init_addrof_public_var_not_first_order; eauto.
  - intros H id b ofs PUB FS PERM.
    simpl in PUB, FS.
    assert (INPUB: In id (prog_public p)).
    { unfold Genv.public_symbol in PUB. rewrite FS in PUB.
      rewrite Genv.globalenv_public in PUB.
      destruct (In_dec ident_eq id (prog_public p)); auto; discriminate. }
    destruct (find_symbol_find_def p id b FS) as (g & FD).
    destruct g as [f|gv].
    + (* functions: only Nonempty permission *)
      assert (FF: Genv.find_funct_ptr (Genv.globalenv p) b = Some f).
      { unfold Genv.find_funct_ptr. rewrite FD. auto. }
      exploit Genv.init_mem_characterization_2; eauto. intros (_ & ONLY).
      exploit ONLY; eauto. intros (_ & EQ). discriminate.
    + assert (FV: Genv.find_var_info (Genv.globalenv p) b = Some gv).
      { unfold Genv.find_var_info. rewrite FD. auto. }
      destruct (gvar_volatile gv) eqn:VOL.
      * (* volatile: only Nonempty permission *)
        exploit Genv.init_mem_characterization; eauto. intros (_ & PO & _).
        exploit PO; eauto. intros (_ & ORD).
        unfold Genv.perm_globvar in ORD. rewrite VOL in ORD. inv ORD.
      * eapply init_no_addrof_var_first_order; eauto.
Qed.

End INIT.

(** ** Theorem 4: storing a pointer (or [Vundef]) into a public variable
    breaks [public_first_order], whatever the chunk. This covers a public
    variable declared without initializer and later assigned a pointer
    ([q = &x;] compiles to an [Mint64] store of a [Vptr] on RV64). *)

Lemma encode_val_ptr_undef_non_byte:
  forall chunk v,
  (v = Vundef \/ exists b o, v = Vptr b o) ->
  forall mv, In mv (encode_val chunk v) -> ~ is_byte mv.
Proof.
  intros chunk v H mv IN.
  destruct H as [->|(b & o & ->)]; destruct chunk; simpl in IN;
  try destruct Archi.ptr64; simpl in IN;
  repeat (destruct IN as [<-|IN]; [simpl; tauto|]); contradiction.
Qed.

Theorem store_ptr_public_not_first_order:
  forall (ge: Senv.t) chunk m b o v cp m' id,
  Mem.store chunk m b o v cp = Some m' ->
  (v = Vundef \/ exists b' o', v = Vptr b' o') ->
  Senv.public_symbol ge id = true ->
  Senv.find_symbol ge id = Some b ->
  ~ public_first_order ge m'.
Proof.
  intros ge chunk m b o v cp m' id ST V PUB FS PFO.
  assert (VA: Mem.valid_access m chunk b o Writable (Some cp)) by (eapply Mem.store_valid_access_3; eauto).
  destruct VA as (RP & _ & _).
  assert (PERM: Mem.perm m' b o Cur Readable).
  { eapply Mem.perm_store_1; eauto. eapply Mem.perm_implies. apply RP.
    pose proof (size_chunk_pos chunk). lia. constructor. }
  specialize (PFO id b o PUB FS PERM). unfold loc_first_order in PFO.
  erewrite Mem.store_mem_contents in PFO by eauto. rewrite PMap.gss in PFO.
  pose proof (encode_val_length chunk v) as LEN.
  pose proof (encode_val_ptr_undef_non_byte chunk v V) as NB.
  destruct (encode_val chunk v) as [|mv rest] eqn:E.
  - destruct chunk; discriminate.
  - simpl in PFO. rewrite Mem.setN_outside in PFO by lia. rewrite ZMap.gss in PFO.
    apply (NB mv). left; auto. destruct mv; simpl in *; auto.
Qed.

(** ** Theorem 5: ECC facts for ordinary external calls and builtins. *)

(* A struct assignment into a public global compiles to an [EF_memcpy]
   builtin (cfrontend/Cshmgen.v:429-444) whose first argument is the address
   of the global; its ECC is false. *)
Theorem ecc_memcpy_public_dest_false:
  forall ge m cp sz al b o args,
  block_public ge b ->
  ~ external_call_conds (EF_memcpy cp sz al) ge m (Vptr b o :: args).
Proof.
  intros. simpl. unfold EF_memcpy_dest_not_pub. tauto.
Qed.

(* A symbol that is not in [prog_public] (e.g. a string literal
   [__stringlit_N], which C2C declares static, cfrontend/C2C.ml:584-591,
   or any [static] variable) is not a public block. *)
Theorem non_public_symbol_not_block_public:
  forall {F V: Type} {CF: has_comp F} (p: AST.program F V) id b,
  ~ In id (prog_public p) ->
  Genv.find_symbol (Genv.globalenv p) id = Some b ->
  ~ block_public (Genv.globalenv p) b.
Proof.
  intros F V CF p id b NIN FS (id' & INV & PUB).
  simpl in INV, PUB. apply Genv.invert_find_symbol in INV.
  assert (id' = id) by (eapply Genv.genv_vars_inj; eauto). subst id'.
  unfold Genv.public_symbol in PUB. rewrite FS, Genv.globalenv_public in PUB.
  destruct (In_dec ident_eq id (prog_public p)); [contradiction | discriminate].
Qed.

(* An [EF_external] call (e.g. printf) whose first argument points to a
   non-public block (a string literal, a stack buffer, a static variable)
   violates ECC. *)
Theorem ecc_external_nonpublic_ptr_arg_false:
  forall ge m cp name sg ty tys b o vs,
  ~ block_public ge b ->
  sig_args sg = ty :: tys ->
  ~ external_call_conds (EF_external cp name sg) ge m (Vptr b o :: vs).
Proof.
  intros ge m cp name sg ty tys b o vs NB SG. simpl. unfold visible_fo, vals_public.
  rewrite SG. intros (_ & F2). inv F2. inv H2. auto.
Qed.

(* Any [EF_external] call in a memory where some public variable holds a
   pointer or [Undef] violates ECC, whatever its arguments. *)
Theorem ecc_external_not_first_order_false:
  forall ge m cp name sg args,
  ~ public_first_order ge m ->
  ~ external_call_conds (EF_external cp name sg) ge m args.
Proof.
  intros. simpl. unfold visible_fo. tauto.
Qed.
