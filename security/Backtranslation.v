Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import riscV.Asm.
Require Import BtInfoAsm.
Require Import Ctypes Clight.


Record syscall_properties (sem: extcall_sem) (sg: signature) : Prop :=
  mk_syscall_properties {
      sc_args_match:
      forall ge cp args m1 name evargs evres res m2,
        sem ge cp args m1 (Event_syscall name evargs evres :: nil) res m2 ->
        eventval_list_match ge evargs sg.(sig_args) args;
    }.


Section GENV.

  Context {F: Type}.
  Context {V: Type}.

  (* For NR, use below: *)
  (* ::: mkpass Unusedglobproof.match_prog *)
  (* match_prog_unique: *)
  (*   list_norepet (prog_defs_names tp) *)
  Lemma genv_def_to_some_ident
        (p: AST.program F V)
        (NR: list_norepet (prog_defs_names p))
        ge
        (GE: ge = Genv.globalenv p)
        b gd
        (DEF: Genv.find_def ge b = Some gd)
    :
    exists id b', Genv.find_symbol ge id = Some b' /\ Genv.find_def ge b' = Some gd.
  Proof.
    subst ge. exploit Genv.find_def_inversion; eauto. intros [id IN].
    assert (GET: (prog_defmap p) ! id = Some gd).
    { unfold prog_defmap. unfold prog_defs_names in NR. apply PTree_Properties.of_list_norepet; auto. }
    apply Genv.find_def_symbol in GET. destruct GET as [b' [FINDSYM FINDDEF]]. eauto.
  Qed.

  Lemma genv_find_def_add_global_spec
        (ge: Genv.t F V) id gd
        (NEW: Genv.find_symbol ge id = None)
        b gd'
        (ADD: Genv.find_def (Genv.add_global ge (id, gd)) b = Some gd')
    :
    ((b = (Genv.genv_next ge)) /\ (gd' = gd)) \/
      ((b <> (Genv.genv_next ge)) /\ (Genv.find_def ge b = Some gd')).
  Proof.
    destruct (Pos.eqb_spec b (Genv.genv_next ge)).
    - left; split; auto.
      unfold Genv.find_def, Genv.add_global in ADD. subst; simpl in *.
      rewrite PTree.gss in ADD. inversion ADD; auto.
    - right; split; auto.
      unfold Genv.find_def, Genv.add_global in ADD. simpl in *.
      rewrite PTree.gso in ADD; auto.
  Qed.

  Lemma genv_def_to_ident
        (p: AST.program F V)
        (NR: list_norepet (prog_defs_names p))
        ge
        (GE: ge = Genv.globalenv p)
        b gd
        (DEF: Genv.find_def ge b = Some gd)
    :
    exists id, Genv.invert_symbol ge b = Some id.
  Proof.
    subst ge. unfold Genv.globalenv, Genv.add_globals, prog_defs_names in *.
    destruct p; simpl in *. clear - NR DEF.
    remember (Genv.empty_genv F V prog_public prog_pol) as ge.
    replace (fold_left (Genv.add_global (V:=V)) prog_defs ge) with
      (fold_right (fun ig g => Genv.add_global g ig) ge (rev prog_defs)) in *.
    2:{ rewrite fold_left_rev_right. f_equal. }
    remember (rev prog_defs) as rev_prog_defs.
    assert (RNR: list_norepet (map fst rev_prog_defs)).
    { subst. rewrite map_rev. apply list_norepet_rev; auto. }
    clear prog_defs NR Heqrev_prog_defs. subst ge.
    revert prog_public prog_pol b gd DEF RNR.
    induction rev_prog_defs; intros.
    { unfold Genv.find_def in DEF. simpl in DEF. rewrite PTree.gempty in DEF. congruence. }
    destruct a as [id0 gd0].
    simpl in *. specialize (IHrev_prog_defs prog_public prog_pol).
    remember (fold_right (fun (ig : ident * globdef F V) (g : Genv.t F V) => Genv.add_global g ig) (Genv.empty_genv F V prog_public prog_pol) rev_prog_defs) as ge.
    assert (GE: ge = Genv.globalenv (AST.mkprogram (rev rev_prog_defs) prog_public id0 prog_pol)).
    { subst ge. unfold Genv.globalenv. unfold Genv.add_globals. simpl.
      rewrite <- fold_left_rev_right. rewrite rev_involutive. auto. }
    apply genv_find_def_add_global_spec in DEF.
    { destruct DEF as [[BLK GD] | [BLK GD]].
      - subst b gd0. exists id0.
        apply Genv.find_invert_symbol. unfold Genv.find_symbol, Genv.add_global; simpl.
        rewrite PTree.gss. auto.
      - inversion RNR; clear RNR. subst hd tl. specialize (IHrev_prog_defs _ _ GD H2).
        destruct IHrev_prog_defs as [id' INV]. exists id'.
        apply Genv.find_invert_symbol. unfold Genv.find_symbol, Genv.add_global; simpl.
        rewrite PTree.gso. apply Genv.invert_find_symbol in INV. auto.
        clear - H1 Heqge INV GE. apply Genv.invert_find_symbol in INV.
        rewrite GE in INV. apply Genv.find_symbol_inversion in INV.
        unfold prog_defs_names in INV. simpl in INV.
        rewrite map_rev in INV. apply in_rev in INV. intros CONTRA. subst id'. auto.
    }
    { destruct (Genv.find_symbol ge id0) eqn:CASE; auto. exfalso.
      rewrite GE in CASE. apply Genv.find_symbol_inversion in CASE.
      unfold prog_defs_names in CASE. simpl in CASE. rewrite map_rev in CASE. apply in_rev in CASE.
      clear - CASE RNR. inversion RNR. auto.
    }
  Qed.

End GENV.


Section MEM.

  (* f doesn't map anything to [b], e.g. the counter and function parameters *)
  Definition meminj_notmap (f: meminj) b := forall b0 ofs0, ~ (f b0 = Some (b, ofs0)).

  Lemma loc_out_of_reach_unchanged_on_content:
    forall f b ofs m1 m1' m2'
      (NOTMAP: meminj_notmap f b),
      Mem.perm m1' b ofs Cur Readable ->
      (* Mem.perm m1' b ofs Cur Writable -> *)
      Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ->
      ZMap.get ofs (Mem.mem_contents m2') !! b = ZMap.get ofs (Mem.mem_contents m1') !! b.
  Proof.
    intros. destruct H0. apply unchanged_on_contents; eauto.
    unfold loc_out_of_reach. intros. now specialize (NOTMAP _ _ H0).
    (* eapply Mem.perm_implies; eauto. constructor. *)
  Qed.

  Lemma loc_out_of_reach_unchanged_on_perm:
    forall f b ofs m1 m1' m2' k p
      (NOTMAP: meminj_notmap f b),
      Mem.perm m1' b ofs k p ->
      Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ->
      Mem.perm m2' b ofs k p.
  Proof.
    intros. destruct H0. apply unchanged_on_perm; eauto.
    unfold loc_out_of_reach. intros. now specialize (NOTMAP _ _ H0).
    eapply Mem.perm_valid_block; eauto.
  Qed.

  (* Record unchanged_on (P : block -> Z -> Prop) (m_before m_after : mem) : Prop := mk_unchanged_on *)
  (* { unchanged_on_nextblock : Ple (Mem.nextblock m_before) (Mem.nextblock m_after); *)
  (*   unchanged_on_perm : forall (b : block) (ofs : Z) (k : perm_kind) (p : permission), P b ofs -> Mem.valid_block m_before b -> Mem.perm m_before b ofs k p <-> Mem.perm m_after b ofs k p; *)
  (*   unchanged_on_contents : forall (b : block) (ofs : Z), P b ofs -> Mem.perm m_before b ofs Cur Readable -> ZMap.get ofs (Mem.mem_contents m_after) !! b = ZMap.get ofs (Mem.mem_contents m_before) !! b; *)
  (*   unchanged_on_own : forall (b : block) (cp : option compartment), Mem.valid_block m_before b -> Mem.can_access_block m_before b cp <-> Mem.can_access_block m_after b cp }. *)

  Lemma inject_separated_notmap
        f f' m m' b
        (NM: meminj_notmap f b)
        (VALID: Mem.valid_block m' b)
        (* (INJ: Mem.inject f m m') *)
        (INCR: inject_incr f f')
        (SEP: inject_separated f f' m m')
    :
    meminj_notmap f' b.
  Proof.
    unfold meminj_notmap, inject_incr, inject_separated in *.
    intros. intros CONTRA. specialize (NM b0 ofs0). destruct (f b0) eqn:FB.
    { destruct p. specialize (INCR _ _ _ FB). rewrite CONTRA in INCR. inversion INCR; clear INCR; subst. congruence. }
    specialize (SEP _ _ _ FB CONTRA). destruct SEP as [NV1 NV2]. congruence.
  Qed.

  (*
forall b, b is the block of one of the counter ->
     (forall b0 ofs, ~ (f b0 = Some (b, ofs)))
   *)

(** Events.v **)
(* (** External calls must commute with memory injections, *)
(*   in the following sense. *) *)
(*   ec_mem_inject: *)
(*     forall ge1 ge2 c vargs m1 t vres m2 f m1' vargs', *)
(*     symbols_inject f ge1 ge2 -> *)
(*     sem ge1 c vargs m1 t vres m2 -> *)
(*     Mem.inject f m1 m1' -> *)
(*     Val.inject_list f vargs vargs' -> *)
(*     exists f', exists vres', exists m2', *)
(*        sem ge2 c vargs' m1' t vres' m2' *)
(*     /\ Val.inject f' vres vres' *)
(*     /\ Mem.inject f' m2 m2' *)
(*     /\ Mem.unchanged_on (loc_unmapped f) m1 m2 *)
(*     /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' *)
(*     /\ inject_incr f f' *)
(*     /\ inject_separated f f' m1 m1'; *)

End MEM.


Section Backtranslation.

  Ltac simpl_expr :=
    repeat (match goal with
            | |- eval_expr _ _ _ _ _ _ _ => econstructor
            | |- eval_lvalue _ _ _ _ _ _ _ _ _ => econstructor 2
            (* | |- eval_lvalue _ _ _ _ _ _ _ _ _ => econstructor *)
            | |- deref_loc _ _ _ _ _ _ _ => econstructor
            | |- assign_loc _ _ _ _ _ _ _ _ _ => econstructor
            | |- Cop.sem_cmp _ _ _ _ _ _ = Some _ => unfold Cop.sem_cmp
            | |- Cop.sem_add _ _ _ _ _ _ = Some _ => unfold Cop.sem_add
            | |- Cop.sem_binarith _ _ _ _ _ _ _ _ _ = Some _ => unfold Cop.sem_binarith
            | |- match Cop.sem_cast _ ?x ?x _ with | _ => _ end = Some _ => rewrite Cop.cast_val_casted
            | |- Cop.sem_cast _ ?y ?y _ = Some _ => rewrite Cop.cast_val_casted
            | |- Cop.val_casted _ _ => constructor
            | H: ?x = _ |- Cop.bool_val (_ ?x) _ _ = Some _ => rewrite H; try reflexivity
            end; simpl; eauto).

  Ltac take_step := econstructor; [econstructor; simpl_expr | | traceEq]; simpl.


  Section SWITCH.
    (** switch statement; used when converting a trace to a code **)

    Definition type_counter: type := Tlong Unsigned noattr.
    Definition type_bool:    type := Tint IBool Signed noattr.

    Definition switch_clause (cnt: ident) (n: Z) (s_then s_else: statement): statement :=
      let one := Econst_long Int64.one type_counter in
      Sifthenelse (Ebinop Cop.Oeq
                          (Evar cnt type_counter)
                          (Econst_long (Int64.repr n) type_counter)
                          type_bool)
                  (* if true *)
                  (Ssequence
                     (Sassign (Evar cnt type_counter)
                              (Ebinop Cop.Oadd (Evar cnt type_counter) one type_counter))
                     s_then)
                  (* if false *)
                  s_else.

    Ltac simpl_expr' :=
      unfold type_counter; unfold type_bool; simpl; simpl_expr.

    Ltac take_step' := econstructor; [econstructor; simpl_expr' | | traceEq]; simpl.

    Lemma switch_clause_spec p (cnt: ident) f e le m b (n: int64) (n': Z) s_then s_else:
      let cp := comp_of f in
      let ge := globalenv p in
      e ! cnt = None ->
      Genv.find_symbol ge cnt = Some b ->
      Mem.valid_access m Mint64 b 0 Writable (Some cp) ->
      Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong n) ->
      if Int64.eq n (Int64.repr n') then
        exists m',
          Mem.storev Mint64 m (Vptr b Ptrofs.zero) (Vlong (Int64.add n Int64.one)) cp = Some m' /\
            Star (Clight.semantics1 p) (State f (switch_clause cnt n' s_then s_else) Kstop e le m) E0 (State f s_then Kstop e le m')
      else
        Star (Clight.semantics1 p) (State f (switch_clause cnt n' s_then s_else) Kstop e le m) E0 (State f s_else Kstop e le m).
    Proof.
      intros; subst cp ge.
      destruct (Int64.eq n (Int64.repr n')) eqn:eq_n_n'.
      - simpl.
        destruct (Mem.valid_access_store m Mint64 b 0%Z (comp_of f) (Vlong (Int64.add n Int64.one))) as [m' m_m']; try assumption.
        exists m'. split; eauto.
        do 4 take_step'.
        now apply star_refl.
      - (* take_steps. *)
        take_step'. rewrite Int.eq_true; simpl.
        now apply star_refl.
    Qed.


    Definition switch_add_statement cnt s res :=
      (Z.pred (fst res), switch_clause cnt (Z.pred (fst res)) s (snd res)).

    Definition switch (cnt: ident) (ss: list statement) (s_else: statement): statement :=
      snd (fold_right (switch_add_statement cnt) (Z.of_nat (length ss), s_else) ss).

    Lemma fst_switch (cnt: ident) n (s_else: statement) (ss : list statement) :
      fst (fold_right (switch_add_statement cnt) (n, s_else) ss) = (n - Z.of_nat (length ss))%Z.
    Proof.
      induction ss as [|s' ss IH]; try now rewrite Z.sub_0_r.
      simpl; lia.
    Qed.

    Lemma switch_spec_else
          p (cnt: ident) f (e: env) le m b (n: Z) ss s_else
          (WF: Z.of_nat (length ss) < Int64.modulus)
          (RANGE: Z.of_nat (length ss) <= n < Int64.modulus)
      :
      let ge := globalenv p in
      let cp := comp_of f in
      e ! cnt = None ->
      Genv.find_symbol ge cnt = Some b ->
      (* e ! (bt_env.(local_counter) cp) = Some (b, type_counter) -> *)
      (* Mem.valid_access m Mint64 b 0 Writable (Some cp) -> *)
      Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (Int64.repr n)) ->
      Star (Clight.semantics1 p)
           (State f (switch cnt ss s_else) Kstop e le m)
           E0
           (State f s_else Kstop e le m).
    Proof.
      intros; subst cp ge. unfold switch. destruct RANGE as [RA1 RA2].
      assert (G: forall n',
                 (Z.of_nat (length ss)) <= n' ->
                 n' <= n ->
                 Star (Clight.semantics1 p)
                      (State f (snd (fold_right (switch_add_statement cnt) (n', s_else) ss)) Kstop e le m)
                      E0
                      (State f s_else Kstop e le m)).
      { intros n' LE1 LE2.
        induction ss as [|s ss IH]; try apply star_refl.
        simpl. simpl in RA1, LE1. rewrite fst_switch, <- Z.sub_succ_r.
        take_step'.
        { rewrite Int64.eq_false. reflexivity. clear - WF RA1 RA2 LE1 LE2.
          destruct (Z.eqb_spec n (n' - Z.of_nat (S (length ss)))) as [n_eq_0|?]; simpl.
          - lia.
          - intros EQ. apply n0; clear n0.
            rewrite <- (Int64.unsigned_repr n).
            rewrite EQ. rewrite Int64.unsigned_repr. lia.
            1: split.
            all: unfold Int64.max_unsigned; try lia.
        }
        rewrite Int.eq_true; simpl.
        eapply IH; lia.
      }
      now apply G; lia.
    Qed.

    Let nat64 n := Int64.repr (Z.of_nat n).

    Lemma switch_spec
          p (cnt: ident) f (e: env) le m b
          ss s ss' s_else
          (WF: Z.of_nat (length (ss ++ s :: ss')) < Int64.modulus)
      :
      let ge := globalenv p in
      let cp := comp_of f in
      e ! cnt = None ->
      Genv.find_symbol ge cnt = Some b ->
      Mem.valid_access m Mint64 b 0 Writable (Some cp) ->
      Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (nat64 (length ss))) ->
      exists m',
        Mem.storev Mint64 m (Vptr b Ptrofs.zero) (Vlong (Int64.add (nat64 (length ss)) Int64.one)) cp = Some m' /\
          Star (Clight.semantics1 p)
               (State f (switch cnt (ss ++ s :: ss') s_else) Kstop e le m)
               E0
               (State f s Kstop e le m').
    Proof.
      intros.
      assert (Eswitch :
               exists s_else',
                 switch cnt (ss ++ s :: ss') s_else =
                   switch cnt ss (switch_clause cnt (Z.of_nat (length ss)) s s_else')).
      { unfold switch. rewrite fold_right_app, app_length. simpl.
        exists (snd (fold_right (switch_add_statement cnt) (Z.of_nat (length ss + S (length ss')), s_else) ss')).
        repeat f_equal. rewrite -> surjective_pairing at 1. simpl.
        rewrite fst_switch, Nat.add_succ_r.
        assert (A: Z.pred (Z.of_nat (S (Datatypes.length ss + Datatypes.length ss')) - Z.of_nat (Datatypes.length ss')) = Z.of_nat (Datatypes.length ss)) by lia.
        rewrite A. reflexivity.
      }
      destruct Eswitch as [s_else' ->]. clear s_else. rename s_else' into s_else.
      exploit (switch_clause_spec p cnt f e le m b (nat64 (length ss)) (Z.of_nat (length ss)) s s_else); auto.
      unfold nat64. rewrite Int64.eq_true. intro Hcont.
      destruct Hcont as (m' & Hstore & Hstar2).
      exists m'. split; trivial.
      apply (fun H => @star_trans _ _ _ _ _ E0 _ H E0 _ _ Hstar2); trivial.
      assert (WF2: Z.of_nat (Datatypes.length ss) < Int64.modulus).
      { clear - WF. rewrite app_length in WF. lia. }
      eapply switch_spec_else; eauto. split; auto. reflexivity.
    Qed.

  End SWITCH.


  Section CONV.
    (** converting event to data **)

    Context {F: Type}.
    Context {V: Type}.
    Variable ge: Genv.t F V.

    Definition wf_env (e: env) id := e ! id = None.

    Definition eventval_to_val (ge: Senv.t) (v: eventval): val :=
      match v with
      | EVint i => Vint i
      | EVlong i => Vlong i
      | EVfloat f => Vfloat f
      | EVsingle f => Vsingle f
      | EVptr_global id ofs => match Senv.find_symbol ge id with
                              | Some b => Vptr b ofs
                              | None => Vundef
                              end
      end.

    Definition list_eventval_to_list_val ge (vs: list eventval): list val :=
      List.map (eventval_to_val ge) vs.

    Definition eventval_to_type (v: eventval): type :=
      match v with
      | EVint _ => Tint I32 Signed noattr
      | EVlong _ => Tlong Signed noattr
      | EVfloat _ => Tfloat F64 noattr
      | EVsingle _ => Tfloat F32 noattr
      | EVptr_global id _ => Tpointer Tvoid noattr
      end.

    Definition ptr_of_id_ofs (id: ident) (ofs: ptrofs): expr :=
      if Archi.ptr64
      then
        Ebinop Cop.Oadd
               (Eaddrof (Evar id Tvoid) (Tpointer Tvoid noattr))
               (Econst_long (Ptrofs.to_int64 ofs) (Tlong Signed noattr))
               (Tpointer Tvoid noattr)
      else
        Ebinop Cop.Oadd
               (Eaddrof (Evar id Tvoid) (Tpointer Tvoid noattr))
               (Econst_int (Ptrofs.to_int ofs) (Tint I32 Signed noattr))
               (Tpointer Tvoid noattr).

    Lemma ptr_of_id_ofs_typeof
          i i0
      :
      typeof (ptr_of_id_ofs i i0) = Tpointer Tvoid noattr.
    Proof. unfold ptr_of_id_ofs. destruct Archi.ptr64; simpl; auto. Qed.

    Definition eventval_to_expr (v: eventval): expr :=
      match v with
      | EVint i => Econst_int i (Tint I32 Signed noattr)
      | EVlong i => Econst_long i (Tlong Signed noattr)
      | EVfloat f => Econst_float f (Tfloat F64 noattr)
      | EVsingle f => Econst_single f (Tfloat F32 noattr)
      | EVptr_global id ofs => ptr_of_id_ofs id ofs
      end.

    Definition wf_eventval_env (e: env) (v: eventval): Prop :=
      match v with
      | EVptr_global id _ => wf_env e id
      | _ => True
      end.

    Definition wf_eventval_pub (v: eventval): Prop :=
      match v with
      | EVptr_global id _ => (Senv.public_symbol ge id = true)
      | _ => True
      end.

    Definition wf_eventval_ge (v: eventval): Prop :=
      match v with
      | EVptr_global id _ => (exists b, Genv.find_symbol ge id = Some b)
      | _ => True
      end.

    Lemma wf_eventval_pub_ge
          v
      :
      wf_eventval_pub v -> wf_eventval_ge v.
    Proof. intros H. destruct v; simpl in *; auto. apply Genv.public_symbol_exists in H; auto. Qed.

    Fixpoint list_eventval_to_typelist (vs: list eventval): typelist :=
      match vs with
      | nil => Tnil
      | cons v vs' => Tcons (eventval_to_type v) (list_eventval_to_typelist vs')
      end.

    Definition list_eventval_to_list_expr (vs: list eventval): list expr :=
      List.map eventval_to_expr vs.

    Lemma typeof_eventval_to_expr_type
          v
      :
      typeof (eventval_to_expr v) = eventval_to_type v.
    Proof. destruct v; simpl; auto. apply ptr_of_id_ofs_typeof. Qed.

  End CONV.


  Section CODEAUX.

    (* We extract function data: argument types, fn_return, rn_callconv from signature *)
    (* Correctness should follow from the semantics of Asm, especially eventval_match *)
    Definition typ_to_type: typ -> type :=
      fun t: typ =>
        match t with
        | AST.Tint => Tint I32 Signed noattr
        | AST.Tfloat => Tfloat F64 noattr
        | AST.Tlong => Tlong Signed noattr
        | AST.Tsingle => Tfloat F32 noattr
        (* do not appear in eventval_match *)
        | AST.Tany32 => Tvoid
        | AST.Tany64 => Tvoid
        end.

    Fixpoint list_typ_to_typelist (ts: list typ): typelist :=
      match ts with
      | nil => Tnil
      | cons t ts' => Tcons (typ_to_type t) (list_typ_to_typelist ts')
      end.

    Definition rettype_to_type: rettype -> type :=
      fun rt: rettype =>
        match rt with
        | Tint8signed | Tint8unsigned | Tint16signed | Tint16unsigned => Tint I32 Signed noattr
        | AST.Tvoid => Tint I32 Signed noattr
        | Tret t => typ_to_type t
        end.

    (* Definition rettype_to_type: rettype -> type := *)
    (*   fun rt: rettype => *)
    (*     match rt with *)
    (*     | Tint8signed => Tint I8 Signed noattr *)
    (*     | Tint8unsigned => Tint I8 Unsigned noattr *)
    (*     | Tint16signed => Tint I16 Signed noattr *)
    (*     | Tint16unsigned => Tint I16 Unsigned noattr *)
    (*     | AST.Tvoid => Tvoid *)
    (*     | Tret t => typ_to_type t *)
    (*     end. *)

    Lemma proj_rettype_to_type_rettype_of_type_eq
          ge evres rt res
          (EVM: eventval_match ge evres (proj_rettype rt) res)
      :
      (* (rettype_of_type (rettype_to_type rt)) = rt. *)
      proj_rettype (rettype_of_type (rettype_to_type rt)) = proj_rettype rt.
    Proof.
      inv EVM; destruct rt; simpl; auto.
      destruct t; simpl in *; auto; try congruence.
      destruct t; simpl in *; auto; try congruence.
      destruct t; simpl in *; auto; try congruence.
      destruct t; simpl in *; auto; try congruence.
      unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH.
      destruct t; simpl in *; auto; try congruence.
      destruct t; simpl in *; auto; try congruence.
    Qed.

    (* Lemma retttype_to_type_rettype_of_type_eq *)
    (*       ge evres rt res *)
    (*       (EVM: eventval_match ge evres (proj_rettype rt) res) *)
    (*   : *)
    (*   (rettype_of_type (rettype_to_type rt)) = rt. *)
    (* Proof. *)
    (*   inv EVM; destruct rt; simpl; auto. *)
    (*   destruct t; simpl in *; auto; try congruence. *)
    (*   destruct t; simpl in *; auto; try congruence. *)
    (*   destruct t; simpl in *; auto; try congruence. *)
    (*   destruct t; simpl in *; auto; try congruence. *)
    (*   unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. *)
    (*   destruct t; simpl in *; auto; try congruence. *)
    (*   destruct t; simpl in *; auto; try congruence. *)
    (* Qed. *)

    (* Wanted internal function data from signature *)
    (* Definition fun_data : Type := (typelist * type * calling_convention). *)
    Record fun_data : Type := mkfundata { dargs: typelist; dret: type; dcc: calling_convention }.
    Definition funs_data : Type := (PTree.tree fun_data).

    (* Definition from_sig_fun_data (sig: signature): fun_data := (list_typ_to_typelist sig.(sig_args), rettype_to_type sig.(sig_res), sig.(sig_cc)). *)
    Definition from_sig_fun_data (sig: signature): fun_data :=
      mkfundata (list_typ_to_typelist sig.(sig_args)) (rettype_to_type sig.(sig_res)) (sig.(sig_cc)).

    (* Extract from Asm *)
    Definition from_asmfun_fun_data (af: Asm.function): fun_data := from_sig_fun_data af.(fn_sig).
    Definition from_extfun_fun_data (ef: external_function): fun_data := from_sig_fun_data (ef_sig ef).
    Definition from_asmfd_fun_data (fd: Asm.fundef): fun_data :=
      match fd with | AST.Internal af => from_asmfun_fun_data af | AST.External ef => from_extfun_fun_data ef end.
    Definition from_asmgd_fun_data (gd: globdef Asm.fundef unit): option fun_data :=
      match gd with | Gfun fd => Some (from_asmfd_fun_data fd) | Gvar _ => None end.

    Definition from_asm_funs_data (asm: Asm.program): funs_data :=
      let defs := Genv.genv_defs (Genv.globalenv asm) in
      PTree.map_filter1 from_asmgd_fun_data defs.

    (* Extract from Clight *)
    Definition from_clfun_fun_data (cf: Clight.function): fun_data := mkfundata (type_of_params cf.(fn_params)) cf.(fn_return) cf.(fn_callconv).
    (* Definition from_clfd_fun_data (fd: Clight.fundef): fun_data := *)
    (*   match fd with | Ctypes.Internal cf => from_clfun_fun_data cf | Ctypes.External _ tps tr cc => mkfundata tps tr cc end. *)
    Definition from_clfd_fun_data (fd: Clight.fundef): fun_data :=
      match fd with | Ctypes.Internal cf => from_clfun_fun_data cf | Ctypes.External ef _ _ _ => from_extfun_fun_data ef end.
    Definition from_clgd_fun_data (gd: globdef Clight.fundef type): option fun_data :=
      match gd with | Gfun fd => Some (from_clfd_fun_data fd) | Gvar _ => None end.

    Definition from_cl_funs_data (cl: Clight.program): funs_data :=
      let defs := Genv.genv_defs (genv_genv (globalenv cl)) in
      PTree.map_filter1 from_clgd_fun_data defs.

    (* (* Return case *) *)
    (* Definition eventval_to_expr_return (v: eventval) (rt: rettype): expr := *)
    (*   let ty := rettype_to_type rt in *)
    (*   match v with *)
    (*   | EVint i => Econst_int i ty *)
    (*   | EVlong i => Econst_long i ty *)
    (*   | EVfloat f => Econst_float f ty *)
    (*   | EVsingle f => Econst_single f ty *)
    (*   | EVptr_global id ofs => ptr_of_id_ofs id ofs *)
    (*   end. *)

  End CODEAUX.


  Section CODE.
    (** converting *informative* trace to code **)

    Context {F: Type}.
    Context {V: Type}.
    Variable ge: Genv.t F V.

    (* converting functions *)
    Definition code_of_external (argsexpr: list expr) (ik: info_kind) :=
      match ik with
      | info_builtin ef =>
          Sbuiltin None ef (dargs (from_sig_fun_data (ef_sig ef))) argsexpr
      | info_external b sg =>
          match Genv.invert_symbol ge b with
          | Some id =>
              let tys := from_sig_fun_data sg in
              Scall None (Evar id (Tfunction (dargs tys) (dret tys) (dcc tys))) argsexpr
          | None => Sskip
          end
      | _ => Sskip
      end.

    Definition code_of_vload (ch: memory_chunk) (id: ident) (ofs: Ptrofs.int) (v: eventval) (ik: info_kind) :=
      let argsexpr := (ptr_of_id_ofs id ofs :: nil) in code_of_external argsexpr ik.

    Definition code_of_vstore (ch: memory_chunk) (id: ident) (ofs: Ptrofs.int) (v: eventval) (ik: info_kind) :=
      let argsexpr := ((ptr_of_id_ofs id ofs) :: (eventval_to_expr v) :: nil) in code_of_external argsexpr ik.

    Definition code_of_annot (str: string) (vs: list eventval) (ik: info_kind) :=
      let argsexpr := (list_eventval_to_list_expr vs) in code_of_external argsexpr ik.

    Definition code_of_syscall (name: string) (vs: list eventval) (v: eventval) (ik: info_kind) :=
      let argsexpr := (list_eventval_to_list_expr vs) in code_of_external argsexpr ik.

    Definition code_of_call (cp cp': compartment) (id: ident) (vs: list eventval) (ik: info_kind) :=
      match ik with
      | info_call _ sg =>
          let tys := from_sig_fun_data sg in
          Scall None (Evar id (Tfunction (dargs tys) (dret tys) (dcc tys))) (list_eventval_to_list_expr vs)
      | _ => Sskip
      end.

    Definition code_of_return (cp cp': compartment) (v: eventval) (ik: info_kind) :=
      match ik with
      | info_return _ =>
          Sreturn (Some (eventval_to_expr v))
      | _ => Sskip
      end.

    (* Definition code_of_return (cp cp': compartment) (v: eventval) (ik: info_kind) := *)
    (*   match ik with *)
    (*   | info_return sg => *)
    (*       Sreturn (Some (eventval_to_expr_return v (sig_res sg))) *)
    (*   | _ => Sskip *)
    (*   end. *)

    Definition code_of_ievent (e: ievent): statement :=
      match e with
      | (Event_vload ch id ofs v, ik) => code_of_vload ch id ofs v ik
      | (Event_vstore ch id ofs v, ik) => code_of_vstore ch id ofs v ik
      | (Event_annot str vs, ik) => code_of_annot str vs ik
      | (Event_call cp cp' id vs, ik) => code_of_call cp cp' id vs ik
      | (Event_syscall name vs v, ik) => code_of_syscall name vs v ik
      | (Event_return cp cp' v, ik) => code_of_return cp cp' v ik
      end.

    (* A while(1)-loop with a big switch inside it *)
    (* TODO: needs to distinguish intra/cross syscall *)
    (* Definition code_of_trace (fds: funs_data) (t: trace) cnt: statement := *)
    (*   Swhile (Econst_int Int.one (Tint I32 Signed noattr)) (switch cnt (map (code_of_event fds) t) (Sreturn None)). *)

  End CODE.


  Section CODEPROP.

    Let cgenv := Genv.t fundef type.

    (* Properties *)
    Lemma eventval_match_transl
          F V (ge: Genv.t F V)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      eventval_match ge ev (typ_of_type (typ_to_type ty)) (eventval_to_val ge ev).
    Proof.
      inversion EM; subst; simpl; try constructor.
      setoid_rewrite H0. unfold Tptr in *. destruct Archi.ptr64; auto.
    Qed.

    Lemma eventval_match_eventval_to_val
          F V (ge: Genv.t F V)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      eventval_to_val ge ev = v.
    Proof. inversion EM; subst; simpl; auto. setoid_rewrite H0. auto. Qed.

    Lemma eventval_match_wf_eventval_ge
          F V (ge: Genv.t F V)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      wf_eventval_ge ge ev.
    Proof. inversion EM; subst; simpl; eauto. Qed.

    Lemma eventval_list_match_transl
          F V (ge: Genv.t F V)
          evs tys vs
          (EM: eventval_list_match ge evs tys vs)
      :
      eventval_list_match ge evs (typlist_of_typelist (list_typ_to_typelist tys)) (list_eventval_to_list_val ge evs).
    Proof.
      induction EM; simpl. constructor. constructor; auto. eapply eventval_match_transl; eauto.
    Qed.

    Lemma eventval_list_match_transl_val
          F V (ge: Genv.t F V)
          evs tys vs
          (EM: eventval_list_match ge evs tys vs)
      :
      eventval_list_match ge evs tys (list_eventval_to_list_val ge evs).
    Proof.
      induction EM; simpl. constructor. constructor; auto. erewrite eventval_match_eventval_to_val; eauto.
    Qed.

    Lemma typ_type_typ
          F V (ge: Genv.t F V)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      typ_of_type (typ_to_type ty) = ty.
    Proof. inversion EM; simpl; auto. subst. unfold Tptr. destruct Archi.ptr64; simpl; auto. Qed.

    Lemma ptr_of_id_ofs_eval
          id ofs e (ge: genv) b cp le m
          (GE1: wf_env e id)
          (GE2: Genv.find_symbol ge id = Some b)
      :
      eval_expr ge e cp le m (ptr_of_id_ofs id ofs) (Vptr b ofs).
    Proof.
      unfold ptr_of_id_ofs. destruct (Archi.ptr64) eqn:ARCH.
      - eapply eval_Ebinop. eapply eval_Eaddrof. eapply eval_Evar_global; eauto.
        simpl_expr.
        simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.of_int64_to_int64; auto.
      - eapply eval_Ebinop. eapply eval_Eaddrof. eapply eval_Evar_global; eauto.
        simpl_expr.
        simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
        erewrite Ptrofs.agree32_of_ints_eq; auto. apply Ptrofs.agree32_to_int; auto.
    Qed.

    Lemma eventval_to_expr_val_eval
          (ge: genv) en cp temp m ev
          (WFENV: wf_eventval_env en ev)
          (WFGE: wf_eventval_ge ge ev)
      :
      eval_expr ge en cp temp m (eventval_to_expr ev) (eventval_to_val ge ev).
    Proof.
      destruct ev; simpl in *; try constructor.
      destruct WFGE as [b WFGE].
      rewrite WFGE. unfold ptr_of_id_ofs. destruct Archi.ptr64 eqn:ARCH.
      - econstructor; try econstructor. eapply eval_Evar_global; eauto.
        simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.of_int64_to_int64; auto.
      - econstructor; try econstructor. eapply eval_Evar_global; eauto.
        simpl. simpl_expr. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_zero_l.
        erewrite Ptrofs.agree32_of_ints_eq; auto. apply Ptrofs.agree32_to_int; auto.
    Qed.

    Lemma sem_cast_eventval_match
          (ge: cgenv) v ty vv m
          (EM: eventval_match ge v (typ_of_type (typ_to_type ty)) vv)
      :
      Cop.sem_cast vv (typeof (eventval_to_expr v)) (typ_to_type ty) m = Some vv.
    Proof.
      destruct ty; simpl in *; inversion EM; subst; simpl in *; simpl_expr.
      all: try rewrite ptr_of_id_ofs_typeof; simpl.
      all: try (cbn; auto).
      all: unfold Tptr in *; destruct Archi.ptr64 eqn:ARCH; try congruence.
      { unfold Cop.sem_cast. simpl. rewrite ARCH. simpl. rewrite pred_dec_true; auto. }
      { unfold Cop.sem_cast. simpl. rewrite ARCH. auto. }
    Qed.

    Lemma list_eventval_to_expr_val_eval
          (ge: genv) en cp temp m evs tys
          (WFENV: Forall (wf_eventval_env en) evs)
          (EMS: eventval_list_match ge evs (typlist_of_typelist (list_typ_to_typelist tys)) (list_eventval_to_list_val ge evs))
      :
      eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_typ_to_typelist tys) (list_eventval_to_list_val ge evs).
    Proof.
      revert en cp temp m WFENV.
      match goal with | [H: eventval_list_match _ _ ?t ?v |- _] => remember t as tys2; remember v as vs2 end.
      revert tys Heqtys2 Heqvs2. induction EMS; intros; subst; simpl in *.
      { destruct tys; simpl in *. constructor. congruence. }
      inversion Heqvs2; clear Heqvs2; subst; simpl in *.
      inversion WFENV; clear WFENV; subst.
      destruct tys; simpl in Heqtys2. congruence with Heqtys2.
      inversion Heqtys2; clear Heqtys2; subst; simpl in *.
      econstructor; eauto. eapply eventval_to_expr_val_eval; eauto.
      eapply eventval_match_wf_eventval_ge; eauto.
      eapply sem_cast_eventval_match; eauto.
    Qed.

    Lemma eventval_match_eventval_to_type
          F V (ge: Genv.t F V)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      eventval_match ge ev (typ_of_type (eventval_to_type ev)) v.
    Proof. inversion EM; subst; simpl; auto. Qed.

    Lemma list_eventval_match_eventval_to_type
          F V (ge: Genv.t F V)
          evs tys vs
          (ESM: eventval_list_match ge evs tys vs)
      :
      eventval_list_match ge evs (typlist_of_typelist (list_eventval_to_typelist evs)) vs.
    Proof. induction ESM; simpl. constructor. constructor; auto. eapply eventval_match_eventval_to_type; eauto. Qed.

    Lemma val_load_result_idem
          ch v
      :
      Val.load_result ch (Val.load_result ch v) = Val.load_result ch v.
    Proof.
      destruct ch, v; simpl; auto.
      5,6,7: destruct Archi.ptr64; simpl; auto.
      1,3: rewrite Int.sign_ext_idem; auto.
      3,4: rewrite Int.zero_ext_idem; auto.
      all: lia.
    Qed.

    Lemma val_load_result_aux
          F V (ge: Genv.t F V)
          ev ch v
          (EM: eventval_match ge ev (type_of_chunk ch) (Val.load_result ch v))
      :
      eventval_match ge ev (type_of_chunk ch) (Val.load_result ch (eventval_to_val ge ev)).
    Proof.
      inversion EM; subst; simpl in *; auto.
      1,2,3,4: rewrite H1, H2; rewrite val_load_result_idem; auto.
      rewrite H3, H. rewrite H0. rewrite val_load_result_idem. auto.
    Qed.

    Lemma eventval_match_proj_rettype
          F V (ge: Genv.t F V)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      eventval_match ge ev (proj_rettype (rettype_of_type (typ_to_type ty))) v.
    Proof.
      inversion EM; subst; simpl; try constructor.
      unfold Tptr in *. destruct Archi.ptr64; simpl; auto.
    Qed.

    Lemma sem_cast_eventval
          (ge: cgenv) v m
          (WFEV: wf_eventval_ge ge v)
      :
      Cop.sem_cast (eventval_to_val ge v) (typeof (eventval_to_expr v)) (eventval_to_type v) m = Some (eventval_to_val ge v).
    Proof. rewrite typeof_eventval_to_expr_type. destruct v; simpl in *; simpl_expr. destruct WFEV. rewrite H. simpl_expr. Qed.

    Lemma list_eventval_to_expr_val_eval2
          (ge: genv) en cp temp m evs
          (WFENV: Forall (wf_eventval_env en) evs)
          (WFGE: Forall (wf_eventval_ge ge) evs)
      :
      eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_eventval_to_typelist evs) (list_eventval_to_list_val ge evs).
    Proof.
      move evs at top. revert ge en cp temp m WFENV WFGE. induction evs; intros; simpl in *.
      constructor.
      inversion WFENV; clear WFENV; subst. inversion WFGE; clear WFGE; subst.
      econstructor; eauto. eapply eventval_to_expr_val_eval; eauto.
      apply sem_cast_eventval; auto.
    Qed.

    Lemma eventval_match_sem_cast
          (* F V (ge: Genv.t F V) *)
          (ge: cgenv)
          m ev ty v
          (EM: eventval_match ge ev ty v)
      :
      (* Cop.sem_cast (eventval_to_val ge ev) (typeof (eventval_to_expr ev)) (typ_to_type ty) m = Some (eventval_to_val ge ev). *)
      Cop.sem_cast v (typeof (eventval_to_expr ev)) (typ_to_type ty) m = Some v.
    Proof.
      inversion EM; subst; simpl; try constructor. all: simpl_expr.
      rewrite ptr_of_id_ofs_typeof. unfold Tptr. unfold Cop.sem_cast. destruct Archi.ptr64 eqn:ARCH; simpl.
      - rewrite ARCH; auto.
      - rewrite ARCH; auto.
    Qed.

    Lemma list_eventval_to_expr_val_eval_typs
          (ge: genv) en cp temp m evs tys vs
          (WFENV: Forall (wf_eventval_env en) evs)
          (EMS: eventval_list_match ge evs tys vs)
      :
      eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_typ_to_typelist tys) vs.
    Proof.
      revert en cp temp m WFENV.
      induction EMS; intros; subst; simpl in *. constructor.
      inversion WFENV; clear WFENV; subst.
      econstructor; eauto. 2: eapply eventval_match_sem_cast; eauto.
      exploit eventval_match_eventval_to_val. eauto. intros. rewrite <- H0. eapply eventval_to_expr_val_eval; auto.
      eapply eventval_match_wf_eventval_ge; eauto.
    Qed.

    Lemma sem_cast_ptr
          b ofs m
      :
      Cop.sem_cast (Vptr b ofs) (Tpointer Tvoid noattr) (typ_to_type Tptr) m = Some (Vptr b ofs).
    Proof.
      unfold Tptr. destruct Archi.ptr64 eqn:ARCH; unfold Cop.sem_cast; simpl; rewrite ARCH; auto.
    Qed.

    Lemma sem_cast_proj_rettype
          (ge: cgenv) evres rty res m
          (EVM: eventval_match ge evres (proj_rettype rty) res)
      :
      Cop.sem_cast (eventval_to_val ge evres)
                   (typeof (eventval_to_expr evres))
                   (rettype_to_type rty) m
      = Some (eventval_to_val ge evres).
    Proof.
      destruct rty; simpl in *.
      { eapply eventval_match_sem_cast. eauto. erewrite eventval_match_eventval_to_val; eauto. }
      { inv EVM; simpl; simpl_expr.
        setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
        unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
        unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
      }
      { inv EVM; simpl; simpl_expr.
        setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
        unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
        unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
      }
      { inv EVM; simpl; simpl_expr.
        setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
        unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
        unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
      }
      { inv EVM; simpl; simpl_expr.
        setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
        unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
        unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
      }
      { inv EVM; simpl; simpl_expr.
        setoid_rewrite H2. rewrite ptr_of_id_ofs_typeof.
        unfold Tptr in *. destruct Archi.ptr64 eqn:ARCH. congruence.
        unfold Cop.sem_cast. simpl. rewrite ARCH. auto.
      }
    Qed.

  End CODEPROP.


  Section STEPPROP.

    Variant external_call_event_match_common
            (ef: external_function) (ev: event) (ge: Senv.t) (cp: compartment) (m1: mem)
      : val -> mem -> Prop :=
      | ext_match_vload
          ch
          (EF: ef = EF_vload ch)
          id ofs evv
          (EV: ev = Event_vload ch id ofs evv)
          b res m2
          (SEM: volatile_load_sem ch ge cp (Vptr b ofs :: nil) m1 (ev :: nil) res m2)
        :
        external_call_event_match_common ef ev ge cp m1 res m2
      | ext_match_vstore
          ch
          (EF: ef = EF_vstore ch)
          id ofs evv
          (EV: ev = Event_vstore ch id ofs evv)
          b argv m2
          (SEM: volatile_store_sem ch ge cp (Vptr b ofs :: argv :: nil) m1 (ev :: nil) Vundef m2)
        :
        external_call_event_match_common ef ev ge cp m1 Vundef m2
      | ext_match_annot
          len text targs
          (EF: ef = EF_annot len text targs)
          evargs
          (EV: ev = Event_annot text evargs)
          vargs m2
          (SEM: extcall_annot_sem text targs ge cp vargs m1 (ev :: nil) Vundef m2)
        :
        external_call_event_match_common ef ev ge cp m1 Vundef m2
      | ext_match_external
          name excp sg
          (EF: ef = EF_external name excp sg)
          evname evargs evres
          (EV: ev = Event_syscall evname evargs evres)
          vargs vres m2
          (SEM: external_functions_sem name sg ge cp vargs m1 (ev :: nil) vres m2)
          (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs)
        :
        external_call_event_match_common ef ev ge cp m1 vres m2
      | ext_match_builtin
          name sg
          (EF: (ef = EF_builtin name sg) \/ (ef = EF_runtime name sg))
          evname evargs evres
          (EV: ev = Event_syscall evname evargs evres)
          (ISEXT: Builtins.lookup_builtin_function name sg = None)
          vargs vres m2
          (SEM: external_functions_sem name sg ge cp vargs m1 (ev :: nil) vres m2)
          (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs)
        :
        external_call_event_match_common ef ev ge cp m1 vres m2
      | ext_match_inline_asm
          txt sg strs
          (EF: ef = EF_inline_asm txt sg strs)
          evname evargs evres
          (EV: ev = Event_syscall evname evargs evres)
          vargs vres m2
          (SEM: inline_assembly_sem txt sg ge cp vargs m1 (ev :: nil) vres m2)
          (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs)
        :
        external_call_event_match_common ef ev ge cp m1 vres m2
    .

    Variant external_call_wf_env (ev: event) (e: env): Prop :=
      | ext_wf_env_vload
          ch id ofs evv
          (EV: ev = Event_vload ch id ofs evv)
          (WF: wf_env e id)
        :
        external_call_wf_env ev e
      | ext_wf_env_vstore
          ch id ofs evv
          (EV: ev = Event_vstore ch id ofs evv)
          (WF0: wf_env e id)
          (WF1: wf_eventval_env e evv)
        :
        external_call_wf_env ev e
      | ext_wf_env_annot
          text evargs
          (EV: ev = Event_annot text evargs)
          (WFENV: Forall (wf_eventval_env e) evargs)
        :
        external_call_wf_env ev e
      | ext_wf_env_syscall
          evname evargs evres
          (EV: ev = Event_syscall evname evargs evres)
          (WFENV: Forall (wf_eventval_env e) evargs)
        :
        external_call_wf_env ev e.

    Definition external_call_event_match (ef: external_function) (ev: event) (ge: Senv.t) (cp: compartment) (m1: mem) (e: env) : val -> mem -> Prop :=
      fun res m2 =>
      (external_call_event_match_common ef ev ge cp m1 res m2) /\ (external_call_wf_env ev e).

    (* Variant external_call_event_match (ef: external_function) (ev: event) (ge: Senv.t) (cp: compartment) (m1: mem) (e: env) : val -> mem -> Prop := *)
    (*   | ext_match_vload *)
    (*       ch *)
    (*       (EF: ef = EF_vload ch) *)
    (*       id ofs evv *)
    (*       (EV: ev = Event_vload ch id ofs evv) *)
    (*       (WF: wf_env e id) *)
    (*       b res m2 *)
    (*       (SEM: volatile_load_sem ch ge cp (Vptr b ofs :: nil) m1 (ev :: nil) res m2) *)
    (*     : *)
    (*     external_call_event_match ef ev ge cp m1 e res m2 *)
    (*   | ext_match_vstore *)
    (*       ch *)
    (*       (EF: ef = EF_vstore ch) *)
    (*       id ofs evv *)
    (*       (EV: ev = Event_vstore ch id ofs evv) *)
    (*       (WF0: wf_env e id) *)
    (*       (WF1: wf_eventval_env e evv) *)
    (*       b argv m2 *)
    (*       (SEM: volatile_store_sem ch ge cp (Vptr b ofs :: argv :: nil) m1 (ev :: nil) Vundef m2) *)
    (*     : *)
    (*     external_call_event_match ef ev ge cp m1 e Vundef m2 *)
    (*   | ext_match_annot *)
    (*       len text targs *)
    (*       (EF: ef = EF_annot len text targs) *)
    (*       evargs *)
    (*       (EV: ev = Event_annot text evargs) *)
    (*       (WFENV: Forall (wf_eventval_env e) evargs) *)
    (*       vargs m2 *)
    (*       (SEM: extcall_annot_sem text targs ge cp vargs m1 (ev :: nil) Vundef m2) *)
    (*     : *)
    (*     external_call_event_match ef ev ge cp m1 e Vundef m2 *)
    (*   | ext_match_external *)
    (*       name excp sg *)
    (*       (EF: ef = EF_external name excp sg) *)
    (*       evname evargs evres *)
    (*       (EV: ev = Event_syscall evname evargs evres) *)
    (*       (WFENV: Forall (wf_eventval_env e) evargs) *)
    (*       vargs vres m2 *)
    (*       (SEM: external_functions_sem name sg ge cp vargs m1 (ev :: nil) vres m2) *)
    (*       (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs) *)
    (*     : *)
    (*     external_call_event_match ef ev ge cp m1 e vres m2 *)
    (*   | ext_match_builtin *)
    (*       name sg *)
    (*       (EF: (ef = EF_builtin name sg) \/ (ef = EF_runtime name sg)) *)
    (*       evname evargs evres *)
    (*       (EV: ev = Event_syscall evname evargs evres) *)
    (*       (WFENV: Forall (wf_eventval_env e) evargs) *)
    (*       (ISEXT: Builtins.lookup_builtin_function name sg = None) *)
    (*       vargs vres m2 *)
    (*       (SEM: external_functions_sem name sg ge cp vargs m1 (ev :: nil) vres m2) *)
    (*       (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs) *)
    (*     : *)
    (*     external_call_event_match ef ev ge cp m1 e vres m2 *)
    (*   | ext_match_inline_asm *)
    (*       txt sg strs *)
    (*       (EF: ef = EF_inline_asm txt sg strs) *)
    (*       evname evargs evres *)
    (*       (EV: ev = Event_syscall evname evargs evres) *)
    (*       (WFENV: Forall (wf_eventval_env e) evargs) *)
    (*       vargs vres m2 *)
    (*       (SEM: inline_assembly_sem txt sg ge cp vargs m1 (ev :: nil) vres m2) *)
    (*       (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs) *)
    (*     : *)
    (*     external_call_event_match ef ev ge cp m1 e vres m2 *)
    (* . *)

    (* Step lemmas *)
    Lemma code_of_event_step_intra_call_ext
          ev ik ef
          p f k e le m1 ge cp res m2
          (CP: cp = comp_of f)
          (GE: ge = globalenv p)
          (EXT: external_call_event_match ef ev ge cp m1 e res m2)
          fb
          (IK: ik = info_external fb (ef_sig ef))
          fid
          (INV: Genv.invert_symbol ge fb = Some fid)
          (WF: wf_env e fid)
          (* bt_wf *)
          (* from_asm *)
          (ISEXT: let tys := from_sig_fun_data (ef_sig ef) in
                  Genv.find_funct_ptr ge fb = Some (Ctypes.External ef (dargs tys) (dret tys) (dcc tys)))
          (ALLOWED: Genv.allowed_call ge cp (Vptr fb Ptrofs.zero))
          (INTRA: Genv.type_of_call ge cp (Genv.find_comp ge (Vptr fb Ptrofs.zero)) <> Genv.CrossCompartmentCall)
      :
      Star (Clight.semantics1 p)
           (State f (code_of_ievent ge (ev, ik)) k e le m1)
           (ev :: nil)
           (State f Sskip k e le m2).
    Proof.
      destruct EXT as [EXT ENV]. inv EXT; subst; simpl in *.
      - inv ENV; inv EV.
        pose proof SEM as SEM0. inv SEM. inv H5. rewrite INV. econstructor 2.
        { eapply step_call.
          4:{ instantiate (2:=Vptr fb Ptrofs.zero). unfold Genv.find_funct. rewrite pred_dec_true; eauto. }
          4:{ simpl. eauto. }
          auto.
          { eapply eval_Elvalue. eapply eval_Evar_global; auto. eapply Genv.invert_find_symbol; eauto. simpl. econstructor 2. auto. }
          { econstructor; eauto. 3: econstructor. eapply ptr_of_id_ofs_eval; eauto.
            rewrite ptr_of_id_ofs_typeof. eapply sem_cast_ptr.
          }
          auto.
          { intros F. simpl in *. contradiction. }
          { econstructor 1. auto. }
        }
        econstructor 2.
        { eapply step_external_function. simpl. eauto. }
        econstructor 2.
        { unfold Genv.find_comp, Genv.find_funct in INTRA. rewrite pred_dec_true in INTRA; auto. rewrite ISEXT in INTRA; simpl in INTRA. unfold comp_of at 2 in INTRA. simpl in INTRA.
          eapply step_returnstate; simpl.
          - intros F. contradiction.
          - econstructor 1. auto.
        }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV.
        pose proof SEM as SEM0. inv SEM. inv H5. rewrite INV. econstructor 2.
        { eapply step_call.
          4:{ instantiate (2:=Vptr fb Ptrofs.zero). unfold Genv.find_funct. rewrite pred_dec_true; eauto. }
          4:{ simpl. eauto. }
          auto.
          { eapply eval_Elvalue. eapply eval_Evar_global; auto. eapply Genv.invert_find_symbol; eauto. simpl. econstructor 2. auto. }
          { econstructor; eauto. eapply ptr_of_id_ofs_eval; eauto.
            rewrite ptr_of_id_ofs_typeof. eapply sem_cast_ptr.
            econstructor; eauto. 3: econstructor. eapply eventval_to_expr_val_eval; auto.
            eapply eventval_match_wf_eventval_ge; eauto.
            eapply eventval_match_sem_cast. erewrite eventval_match_eventval_to_val; eauto.
          }
          auto.
          { intros F. simpl in *. contradiction. }
          { econstructor 1. auto. }
        }
        econstructor 2.
        { eapply step_external_function. unfold call_comp. simpl. econstructor. econstructor 1; eauto. eapply val_load_result_aux; eauto. }
        econstructor 2.
        { unfold Genv.find_comp, Genv.find_funct in INTRA. rewrite pred_dec_true in INTRA; auto. rewrite ISEXT in INTRA; simpl in INTRA. unfold comp_of at 2 in INTRA. simpl in INTRA.
          eapply step_returnstate; simpl.
          - intros F. contradiction.
          - econstructor 1. auto.
        }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV.
        pose proof SEM as SEM0. inv SEM. rewrite INV. econstructor 2.
        { eapply step_call.
          4:{ instantiate (2:=Vptr fb Ptrofs.zero). unfold Genv.find_funct. rewrite pred_dec_true; eauto. }
          4:{ simpl. eauto. }
          auto.
          { eapply eval_Elvalue. eapply eval_Evar_global; auto. eapply Genv.invert_find_symbol; eauto. simpl. econstructor 2. auto. }
          { eapply list_eventval_to_expr_val_eval_typs; eauto. }
          auto.
          { intros F. simpl in *. contradiction. }
          { econstructor 1. auto. }
        }
        econstructor 2.
        { eapply step_external_function. unfold call_comp. simpl. eauto. }
        econstructor 2.
        { unfold Genv.find_comp, Genv.find_funct in INTRA. rewrite pred_dec_true in INTRA; auto. rewrite ISEXT in INTRA; simpl in INTRA. unfold comp_of at 2 in INTRA. simpl in INTRA.
          eapply step_returnstate; simpl.
          - intros F. contradiction.
          - econstructor 1. auto.
        }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV. rewrite INV. econstructor 2.
        { eapply step_call.
          4:{ instantiate (2:=Vptr fb Ptrofs.zero). unfold Genv.find_funct. rewrite pred_dec_true; eauto. }
          4:{ simpl. eauto. }
          auto.
          { eapply eval_Elvalue. eapply eval_Evar_global; auto. eapply Genv.invert_find_symbol; eauto. simpl. econstructor 2. auto. }
          { eapply list_eventval_to_expr_val_eval_typs; eauto. }
          auto.
          { intros F. simpl in *. contradiction. }
          { econstructor 1. auto. }
        }
        econstructor 2.
        { eapply step_external_function. unfold call_comp. simpl. eauto. }
        econstructor 2.
        { unfold Genv.find_comp, Genv.find_funct in INTRA. rewrite pred_dec_true in INTRA; auto. rewrite ISEXT in INTRA; simpl in INTRA. unfold comp_of at 2 in INTRA. simpl in INTRA.
          eapply step_returnstate; simpl.
          - intros F. contradiction.
          - econstructor 1. auto.
        }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV. rewrite INV. econstructor 2.
        { eapply step_call.
          4:{ instantiate (2:=Vptr fb Ptrofs.zero). unfold Genv.find_funct. rewrite pred_dec_true; eauto. }
          4:{ simpl. eauto. }
          auto.
          { eapply eval_Elvalue. eapply eval_Evar_global; auto. eapply Genv.invert_find_symbol; eauto. simpl. econstructor 2. auto. }
          { eapply list_eventval_to_expr_val_eval_typs; eauto. destruct EF; subst; simpl; eauto. }
          auto.
          { intros F. simpl in *. contradiction. }
          { econstructor 1. auto. }
        }
        econstructor 2.
        { eapply step_external_function. unfold call_comp. simpl. destruct EF; subst; simpl; red; rewrite ISEXT0; eauto. }
        econstructor 2.
        { unfold Genv.find_comp, Genv.find_funct in INTRA. rewrite pred_dec_true in INTRA; auto. rewrite ISEXT in INTRA; simpl in INTRA. unfold comp_of at 2 in INTRA. simpl in INTRA.
          eapply step_returnstate; simpl.
          - intros F. contradiction.
          - econstructor 1. auto.
        }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV. rewrite INV. econstructor 2.
        { eapply step_call.
          4:{ instantiate (2:=Vptr fb Ptrofs.zero). unfold Genv.find_funct. rewrite pred_dec_true; eauto. }
          4:{ simpl. eauto. }
          auto.
          { eapply eval_Elvalue. eapply eval_Evar_global; auto. eapply Genv.invert_find_symbol; eauto. simpl. econstructor 2. auto. }
          { eapply list_eventval_to_expr_val_eval_typs; eauto. }
          auto.
          { intros F. simpl in *. contradiction. }
          { econstructor 1. auto. }
        }
        econstructor 2.
        { eapply step_external_function. unfold call_comp. simpl. eauto. }
        econstructor 2.
        { unfold Genv.find_comp, Genv.find_funct in INTRA. rewrite pred_dec_true in INTRA; auto. rewrite ISEXT in INTRA; simpl in INTRA. unfold comp_of at 2 in INTRA. simpl in INTRA.
          eapply step_returnstate; simpl.
          - intros F. contradiction.
          - econstructor 1. auto.
        }
        simpl. econstructor 1. all: eauto.
    Qed.

    Lemma code_of_event_step_builtin
          ev ik ef
          p f k e le m1 ge cp res m2
          (CP: cp = comp_of f)
          (GE: ge = globalenv p)
          (EXT: external_call_event_match ef ev ge cp m1 e res m2)
          (IK: ik = info_builtin ef)
          (* bt_wf *)
          (* from_asm *)
      :
      Star (Clight.semantics1 p)
           (State f (code_of_ievent ge (ev, ik)) k e le m1)
           (ev :: nil)
           (State f Sskip k e le m2).
    Proof.
      destruct EXT as [EXT ENV]. inv EXT; subst; simpl in *.
      - inv ENV; inv EV. pose proof SEM as SEM0. inv SEM. inv H5. econstructor 2.
        { eapply step_builtin; eauto.
          econstructor; eauto. 3: econstructor. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. eapply sem_cast_ptr.
        }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV. pose proof SEM as SEM0. inv SEM. inv H5. econstructor 2.
        { apply val_load_result_aux in H10.
          eapply step_builtin.
          - econstructor; eauto. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. eapply sem_cast_ptr.
          econstructor; eauto. 3: econstructor. eapply eventval_to_expr_val_eval; auto. eapply eventval_match_wf_eventval_ge; eauto.
          eapply eventval_match_sem_cast. erewrite eventval_match_eventval_to_val; eauto.
          - simpl. econstructor. econstructor 1; eauto.
        }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV. pose proof SEM as SEM0. inv SEM. econstructor 2.
        { eapply step_builtin; eauto. eapply list_eventval_to_expr_val_eval_typs; eauto. }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV. econstructor 2.
        { eapply step_builtin; eauto. eapply list_eventval_to_expr_val_eval_typs; eauto. }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV. econstructor 2.
        { destruct EF; subst; simpl.
          - eapply step_builtin. eapply list_eventval_to_expr_val_eval_typs; eauto.
            simpl. red. rewrite ISEXT. eauto.
          - eapply step_builtin. eapply list_eventval_to_expr_val_eval_typs; eauto.
            simpl. red. rewrite ISEXT. eauto.
        }
        simpl. econstructor 1. all: eauto.
      - inv ENV; inv EV. econstructor 2.
        { eapply step_builtin; eauto. eapply list_eventval_to_expr_val_eval_typs; eauto. }
        simpl. econstructor 1. all: eauto.
    Qed.

    Lemma code_of_event_step_cross_call_ext
          (* ev ef *)
          tr ef
          p k m ge cp vres m'
          targs tres cconv vargs
          (CP: cp = call_comp k)
          (GE: ge = globalenv p)
          (* (EXT: external_call ef ge cp vargs m (ev :: nil) vres m') *)
          (EXT: external_call ef ge cp vargs m tr vres m')
          (* bt_wf *)
          (* from_asm *)
      :
      Star (Clight.semantics1 p)
           (Callstate (External ef targs tres cconv) vargs k m)
           (tr)
           (* (ev :: nil) *)
           (Returnstate vres k m' (rettype_of_type tres) (comp_of ef)).
    Proof.
      subst; simpl in *. econstructor 2. eapply step_external_function. eauto.
      econstructor 1. traceEq.
    Qed.

    Lemma code_of_event_step_cross_call_start
          ev ik
          p f k e le m ge cp
          (CP: cp = comp_of f)
          (GE: ge = globalenv p)
          cp' fid evargs
          (EV: ev = Event_call cp cp' fid evargs)
          ce sg
          (IK: ik = info_call ce sg)
          (WF0: wf_env e fid)
          (WF1: Forall (wf_eventval_env e) evargs)
          tdata
          (TD: tdata = from_sig_fun_data sg)
          args
          (ARGS: args = list_eventval_to_list_val ge evargs)
          b
          (FINDB: Genv.find_symbol ge fid = Some b)
          fd
          (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
          (TYPEF: type_of_fundef fd = Tfunction tdata.(dargs) tdata.(dret) tdata.(dcc))
          (CP': cp' = comp_of fd)
          (CROSS: Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall)
          (NPTR: Forall not_ptr args)
          (ALLOW: Genv.allowed_cross_call ge cp (Vptr b Ptrofs.zero))
          (ESM: eventval_list_match ge evargs (sig_args sg) args)
      :
      Star (Clight.semantics1 p)
           (State f (code_of_ievent ge (ev, ik)) k e le m)
           (ev :: nil)
           (Callstate fd args (Kcall None f e le k) m).
    Proof.
      subst; simpl. econstructor 2.
      { eapply step_call. 4: eauto. all: simpl; eauto.
        { econstructor. econstructor 2; eauto. simpl. econstructor 2; auto. }
        { eapply list_eventval_to_expr_val_eval_typs; auto. }
        { red. auto. }
        { econstructor 2; eauto.
          - unfold Genv.find_comp. setoid_rewrite FINDF. auto.
          - eapply Genv.find_invert_symbol; eauto.
          - eapply eventval_list_match_transl; eauto.
        }
      }
      { econstructor 1. }
      { simpl. unfold Genv.find_comp.
        unfold Genv.find_funct in *. simpl in *. rewrite FINDF. auto.
      }
    Qed.

    Lemma code_of_event_step_cross_call_int
          p f vargs k m1 m2 e le
          (ENT: function_entry1 (globalenv p) f vargs m1 e le m2)
      :
      Star (Clight.semantics1 p)
           (Callstate (Internal f) vargs k m1)
           (nil)
           (State f (fn_body f) k e le m2).
    Proof.
      subst; simpl in *. econstructor 2. eapply step_internal_function. eauto.
      econstructor 1. auto.
    Qed.

    Lemma code_of_event_step_cross_returnstate
          ev ik sg evres
          p ge res optid f e le k m ty cp
          (GE: ge = globalenv p)
          (EV: ev = Event_return (comp_of f) cp evres)
          (IK: ik = info_return sg)
          (CROSS: Genv.type_of_call ge (comp_of f) cp = Genv.CrossCompartmentCall)
          (EVM: eventval_match ge evres (proj_rettype (sig_res sg)) res)
          (NPTR: not_ptr res)
          (RETTY: ty = sig_res sg)
      :
      Star (Clight.semantics1 p)
           (Returnstate res (Kcall optid f e le k) m ty cp)
           (ev :: nil)
           (State f Sskip k e (set_opttemp optid res le) m).
    Proof.
      subst; simpl. econstructor 2.
      { eapply step_returnstate; eauto. econstructor 2; eauto. }
      econstructor 1. auto.
    Qed.

    Lemma code_of_event_step_cross_return_code
          ev ik
          p f k e le m ge cp
          (CP: cp = comp_of f)
          (GE: ge = globalenv p)
          cp_c evres
          (EV: ev = Event_return cp_c cp evres)
          (WF: wf_eventval_env e evres)
          sg
          (IK: ik = info_return sg)
          (CROSS: Genv.type_of_call ge cp_c cp = Genv.CrossCompartmentCall)
          optid f_c e_c le_c k_c
          (CONT: call_cont k = Kcall optid f_c e_c le_c k_c)
          (CPC: cp_c = comp_of f_c)
          res
          (EVM: eventval_match ge evres (proj_rettype (sig_res sg)) res)
          (NPTR: not_ptr res)
          (TY: fn_return f = rettype_to_type (sig_res sg))
          m'
          (FREE: Mem.free_list m (blocks_of_env ge e) cp = Some m')
      :
      Star (Clight.semantics1 p)
           (State f (code_of_ievent ge (ev, ik)) k e le m)
           (ev :: nil)
           (State f_c Sskip k_c e_c (set_opttemp optid res le_c) m').
    Proof.
      subst; simpl. exploit eventval_match_eventval_to_val. eapply EVM. intros RES.
      econstructor 2.
      { eapply step_return_1; eauto.
        { eapply eventval_to_expr_val_eval; auto. eapply eventval_match_wf_eventval_ge; eauto. }
        { rewrite TY. eapply sem_cast_proj_rettype. eauto. }
      }
      econstructor 2.
      { rewrite CONT. eapply step_returnstate.
        { subst res. auto. }
        { econstructor 2; auto. rewrite TY. erewrite proj_rettype_to_type_rettype_of_type_eq.
          2: eauto. subst res; eauto.
        }
      }
      { subst res. econstructor 1. }
      all: eauto.
    Qed.

  End STEPPROP.


  Section WELLFORMED.

    Definition empty_te: temp_env := PTree.empty val.

    (* Variant sf_cont_type : Type := | sf_cont: block -> signature -> sf_cont_type. *)
    Variant sf_cont_type : Type := | sf_cont: block -> sf_cont_type.
    Definition sf_conts := list sf_cont_type.

    (* wf_sem: from asm, wf_st: proof invariant for Clight states *)
    Inductive from_info_asm_wf (ge: Asm.genv) : block -> mem -> sf_conts -> itrace -> Prop :=
    | from_info_asm_wf_intra_call_external
        cur m1 sf ev ik tl
        cp
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        ef res m2
        (EXTEV: external_call_event_match_common ef ev ge cp m1 res m2)
        fb
        (IK: ik = info_external fb (ef_sig ef))
        fid
        (INV: Genv.invert_symbol ge fb = Some fid)
        (ISEXT: Genv.find_funct_ptr ge fb = Some (AST.External ef))
        (ALLOWED: Genv.allowed_call ge cp (Vptr fb Ptrofs.zero))
        (INTRA: Genv.type_of_call ge cp (Genv.find_comp ge (Vptr fb Ptrofs.zero)) <> Genv.CrossCompartmentCall)
        (NEXT: from_info_asm_wf ge cur m2 sf tl)
      :
      from_info_asm_wf ge cur m1 sf ((ev, ik) :: tl)
    | from_info_asm_wf_builtin
        cur m1 sf ev ik tl
        cp
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        ef res m2
        (EXT: external_call_event_match_common ef ev ge cp m1 res m2)
        (IK: ik = info_builtin ef)
        (NEXT: from_info_asm_wf ge cur m2 sf tl)
      :
      from_info_asm_wf ge cur m1 sf ((ev, ik) :: tl)
    | from_info_asm_wf_cross_call_internal
        cur m1 sf ev ik tl
        cp
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        cp' fid evargs
        (EV: ev = Event_call cp cp' fid evargs)
        sg
        (IK: ik = info_call not_cross_ext sg)
        b
        (FINDB: Genv.find_symbol ge fid = Some b)
        fd
        (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
        (CP': cp' = comp_of fd)
        (CROSS: Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall)
        args
        (NPTR: Forall not_ptr args)
        (ALLOW: Genv.allowed_cross_call ge cp (Vptr b Ptrofs.zero))
        (ESM: eventval_list_match ge evargs (sig_args sg) args)
        callee_f
        (INTERNAL: fd = AST.Internal callee_f)
        (* TODO: separate this; 
           might be better to upgrade Asm semantics to actually refer to its fn_sig.
           Note that it's not possible to recover Clight fun type data from trace since
           there can be conflicts, since Asm semantics actually allows non-fixed sigs.
         *)
        (SIG: sg = Asm.fn_sig callee_f)
        (* internal call: memory changes in Clight-side, so need inj-relation *)
        (NEXT: from_info_asm_wf ge b m1 ((sf_cont cur) :: sf) tl)
      :
      from_info_asm_wf ge cur m1 sf ((ev, ik) :: tl)
    | from_info_asm_wf_cross_return_internal
        cur m1 ev ik tl
        cp
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        cp_c evres
        (EV: ev = Event_return cp_c cp evres)
        sg
        (IK: ik = info_return sg)
        cur_f
        (INTERNAL: Genv.find_funct_ptr ge cur = Some (AST.Internal cur_f))
        (* TODO: separate this *)
        (SIG: sg = Asm.fn_sig cur_f)
        (CROSS: Genv.type_of_call ge cp_c cp = Genv.CrossCompartmentCall)
        res
        (EVM: eventval_match ge evres (proj_rettype (sig_res sg)) res)
        (NPTR: not_ptr res)
        b_c sf_tl
        (CPC: cp_c = Genv.find_comp ge (Vptr b_c Ptrofs.zero))
        (* internal return: memory changes in Clight-side, so need inj-relation *)
        (NEXT: from_info_asm_wf ge b_c m1 sf_tl tl)
      :
      from_info_asm_wf ge cur m1 ((sf_cont b_c) :: sf_tl) ((ev, ik) :: tl)
    | from_info_asm_wf_cross_call_external1
        (* early cut at call event *)
        cur m1 sf ev ik
        cp
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        cp' fid evargs
        (EV: ev = Event_call cp cp' fid evargs)
        sg
        (IK: ik = info_call is_cross_ext sg)
        b
        (FINDB: Genv.find_symbol ge fid = Some b)
        fd
        (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
        (CP': cp' = comp_of fd)
        (CROSS: Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall)
        args
        (NPTR: Forall not_ptr args)
        (ALLOW: Genv.allowed_cross_call ge cp (Vptr b Ptrofs.zero))
        (ESM: eventval_list_match ge evargs (sig_args sg) args)
        ef
        (EXTERNAL: fd = AST.External ef)
        (* TODO: separate this *)
        (SIG: sg = ef_sig ef)
      :
      from_info_asm_wf ge cur m1 sf ((ev, ik) :: nil)
    | from_info_asm_wf_cross_call_external2
        (* early cut at call-ext_call event *)
        cur m1 sf ev1 ik1
        cp
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        cp' fid evargs
        (EV: ev1 = Event_call cp cp' fid evargs)
        sg
        (IK: ik1 = info_call is_cross_ext sg)
        b
        (FINDB: Genv.find_symbol ge fid = Some b)
        fd
        (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
        (CP': cp' = comp_of fd)
        (CROSS: Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall)
        args
        (NPTR: Forall not_ptr args)
        (ALLOW: Genv.allowed_cross_call ge cp (Vptr b Ptrofs.zero))
        (ESM: eventval_list_match ge evargs (sig_args sg) args)
        ef
        (EXTERNAL: fd = AST.External ef)
        (* TODO: separate this *)
        (SIG: sg = ef_sig ef)
        (* external call part *)
        tr vres m2
        (EXTCALL: external_call ef ge cp args m1 tr vres m2)
        itr
        (INFO: itr = map (fun e => (e, info_external b (ef_sig ef))) tr)
      :
      from_info_asm_wf ge cur m1 sf ((ev1, ik1) :: itr)
    | from_info_asm_wf_cross_call_external3
        (* full call-ext_call-return event *)
        cur m1 sf ev1 ik1
        cp
        (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        cp' fid evargs
        (EV: ev1 = Event_call cp cp' fid evargs)
        sg
        (IK: ik1 = info_call is_cross_ext sg)
        b
        (FINDB: Genv.find_symbol ge fid = Some b)
        fd
        (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
        (CP': cp' = comp_of fd)
        (CROSS: Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall)
        args
        (NPTR: Forall not_ptr args)
        (ALLOW: Genv.allowed_cross_call ge cp (Vptr b Ptrofs.zero))
        (ESM: eventval_list_match ge evargs (sig_args sg) args)
        ef
        (EXTERNAL: fd = AST.External ef)
        (* TODO: separate this *)
        (SIG: sg = ef_sig ef)
        (* external call part *)
        tr vres m2
        (EXTCALL: external_call ef ge cp args m1 tr vres m2)
        itr
        (INFO: itr = map (fun e => (e, info_external b (ef_sig ef))) tr)
        (* return part *)
        ev3 ik3 tl
        evres
        (EV: ev3 = Event_return cp cp' evres)
        sg
        (IK: ik3 = info_return sg)
        (EVM: eventval_match ge evres (proj_rettype (sig_res sg)) vres)
        (NPTR: not_ptr vres)
        (NEXT: from_info_asm_wf ge cur m2 sf tl)
      :
      from_info_asm_wf ge cur m1 sf ((ev1, ik1) :: (itr ++ ((ev3, ik3) :: tl)))
    .

    (* TODO *)
    (* we need a more precise invariant for the proof; counters, mem_inj, env, cont, state *)

  End WELLFORMED.


  Section PROJ.
    (** Projection of the trace according to compartments **)

    Definition comp_of_event (e: event): option (compartment * compartment) :=
      match e with
      | Event_call cp cp' id vs => Some (cp, cp')
      | Event_return cp' cp v => Some (cp, cp')
      | _ => None
      end.

    (* Instance has_comp_event: has_comp event := *)

    Definition comp_proj_trace (cp: compartment) (t: trace): compartment * trace :=
      fold_right
        (fun ev '(cp_now, sub) => match comp_of_event ev with
                               | Some (cp_curr, cp_next) => (cp_next, if (Pos.eqb cp_curr cp) then (ev :: sub) else sub)
                               | None => (cp_now, if (Pos.eqb cp_now cp) then (ev :: sub) else sub)
                               end)
        (default_compartment, nil) t.

    Definition comp_subtrace (cp: compartment) (t: trace) :=
      snd (comp_proj_trace cp t).

    Definition code_of_subtrace cp t :=
      code_of_trace cp (comp_subtrace cp t).

    Definition codes_of_subtraces (cps: list compartment) t : PTree.t statement :=
      PTree_Properties.of_list (map (fun cp => (cp, code_of_subtrace cp t)) cps).

    Definition get_cps_from_policy (p: Policy.t): list compartment :=
      map fst (PTree.elements p.(Policy.policy_export)).

  End PROJ.


  (* TODO *)
  (* Axiom backtranslation: Asm.program -> split -> trace -> Clight.program * Clight.program. *)
  (* Axiom backtranslation_correct: *)
  (*   forall pol s t p C, *)
  (*     backtranslation pol s t = (p, C) -> *)
  (*     clight_compatible s p C /\ *)
  (*     exists W, link p C = Some W /\ *)
  (*            clight_program_has_initial_trace W t. *)

  (* Definition clight_has_side (s: split) (lr: side) (p: Clight.program) := *)
  (*   List.Forall (fun '(id, gd) => *)
  (*                  match gd with *)
  (*                  | Gfun (Ctypes.Internal f) => s (comp_of f) = lr *)
  (*                  | _ => True *)
  (*                  end) *)
  (*               (Ctypes.prog_defs p). *)

  (* Definition clight_compatible (s: split) (p p': Clight.program) := *)
  (*   clight_has_side s Left p /\ clight_has_side s Right p'. *)

  (* Definition clight_program_has_initial_trace (p: Clight.program) (t: trace): Prop := *)
  (*   forall beh, program_behaves (Clight.semantics1 p) beh -> behavior_prefix t beh. *)

  (* Axiom backtranslation_pol: forall pol s t, *)
  (*     Ctypes.prog_pol (fst (backtranslation pol s t)) = pol /\ *)
  (*     Ctypes.prog_pol (snd (backtranslation pol s t)) = pol. *)

  (* Clight.program = Ctypes.program Clight.function *)

  (* old CCS version *)
  Lemma comp_subtrace_app (C: Component.id) (t1 t2: trace) :
    comp_subtrace C (t1 ++ t2) = comp_subtrace C t1 ++ comp_subtrace C t2.
  Proof. apply: filter_cat. Qed.

  Definition procedure_of_trace C P t :=
    expr_of_trace C P (comp_subtrace C t).

  Definition procedures_of_trace (t: trace) : NMap (NMap expr) :=
    mapim (fun C Ciface =>
             let procs :=
                 if C == Component.main then
                   Procedure.main |: Component.export Ciface
                 else Component.export Ciface in
               mkfmapf (fun P => procedure_of_trace C P t) procs)
          intf.

  Definition valid_procedure C P :=
    C = Component.main /\ P = Procedure.main
    \/ exported_procedure intf C P.

  Lemma find_procedures_of_trace_exp (t: trace) C P :
    exported_procedure intf C P ->
    find_procedure (procedures_of_trace t) C P
    = Some (procedure_of_trace C P t).
  Proof.
    intros [CI [C_CI CI_P]].
    unfold find_procedure, procedures_of_trace.
    rewrite mapimE C_CI /= mkfmapfE.
    case: eqP=> _; last by rewrite CI_P.
    by rewrite in_fsetU1 CI_P orbT.
  Qed.

  Lemma find_procedures_of_trace_main (t: trace) :
    find_procedure (procedures_of_trace t) Component.main Procedure.main
    = Some (procedure_of_trace Component.main Procedure.main t).
  Proof.
    rewrite /find_procedure /procedures_of_trace.
    rewrite mapimE eqxx.
    case: (intf Component.main) (has_main)=> [Cint|] //= _.
    by rewrite mkfmapfE in_fsetU1 eqxx.
  Qed.

  Lemma find_procedures_of_trace (t: trace) C P :
    valid_procedure C P ->
    find_procedure (procedures_of_trace t) C P
    = Some (procedure_of_trace C P t).
  Proof.
    by move=> [[-> ->]|?];
    [apply: find_procedures_of_trace_main|apply: find_procedures_of_trace_exp].
  Qed.

  Definition program_of_trace (t: trace) : program :=
    {| prog_interface  := intf;
       prog_procedures := procedures_of_trace t;
       prog_buffers    := mapm (fun _ => inr [Int 0]) intf |}.

  (* old CCS version *)
  

  Section WithTrace.

    Variable cp: compartment.
    Variable t: trace.
    (* Hypothesis t_cp: forall e \in t, comp_of e = cp. *)
    (* Hypothesis t_small_enoug: length t <= 2^60. *)

    Definition statement_of_trace: statement :=
      switch (map (statement_of_event cp) t) Sskip.




  End WithTrace.

End Backtranslation.

  (* Axiom backtranslation: Policy.t -> split -> trace -> Clight.program * Clight.program. *)
  (* Axiom backtranslation_correct: *)
  (*   forall pol s t p C, *)
  (*     backtranslation pol s t = (p, C) -> *)
  (*     clight_compatible s p C /\ *)
  (*     exists W, link p C = Some W /\ *)
  (*            clight_program_has_initial_trace W t. *)

  (* Axiom backtranslation_compiles: *)
  (*   forall pol s t p C, *)
  (*     backtranslation pol s t = (p, C) -> *)
  (*     exists p_compiled C_compiled, *)
  (*       transf_clight_program p = OK p_compiled /\ *)
  (*         transf_clight_program C = OK C_compiled. *)

  (* Axiom backtranslation_pol: forall pol s t, *)
  (*     Ctypes.prog_pol (fst (backtranslation pol s t)) = pol /\ *)
  (*     Ctypes.prog_pol (snd (backtranslation pol s t)) = pol. *)
