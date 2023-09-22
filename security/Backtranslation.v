Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import Tactics.
Require Import riscV.Asm.
Require Import BtBasics BtInfoAsm MemoryDelta MemoryWeak.
Require Import Ctypes Clight.

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

    Lemma switch_clause_spec (ge: genv) (cnt: ident) f e le m b k (n: int64) (n': Z) s_then s_else:
      let cp := comp_of f in
      e ! cnt = None ->
      Genv.find_symbol ge cnt = Some b ->
      Mem.valid_access m Mint64 b 0 Writable (Some cp) ->
      Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong n) ->
      if Int64.eq n (Int64.repr n') then
        exists m',
          Mem.storev Mint64 m (Vptr b Ptrofs.zero) (Vlong (Int64.add n Int64.one)) cp = Some m' /\
            star (step1) ge (State f (switch_clause cnt n' s_then s_else) k e le m) E0 (State f s_then k e le m')
      else
        star (step1) ge (State f (switch_clause cnt n' s_then s_else) k e le m) E0 (State f s_else k e le m).
    Proof.
      intros; subst cp.
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
          (ge: genv) (cnt: ident) f (e: env) le m b k (n: Z) ss s_else
          (WF: Z.of_nat (length ss) < Int64.modulus)
          (RANGE: Z.of_nat (length ss) <= n < Int64.modulus)
      :
      let cp := comp_of f in
      e ! cnt = None ->
      Genv.find_symbol ge cnt = Some b ->
      Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (Int64.repr n)) ->
      star (step1) ge
           (State f (switch cnt ss s_else) k e le m)
           E0
           (State f s_else k e le m).
    Proof.
      intros; subst cp. unfold switch. destruct RANGE as [RA1 RA2].
      assert (G: forall n',
                 (Z.of_nat (length ss)) <= n' ->
                 n' <= n ->
                 star (step1) ge
                      (State f (snd (fold_right (switch_add_statement cnt) (n', s_else) ss)) k e le m)
                      E0
                      (State f s_else k e le m)).
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

    Definition nat64 n := Int64.repr (Z.of_nat n).

    Lemma switch_spec
          (ge: genv) (cnt: ident) f (e: env) le m b k
          ss s ss' s_else
          (WF: Z.of_nat (length (ss ++ s :: ss')) < Int64.modulus)
      :
      let cp := comp_of f in
      e ! cnt = None ->
      Genv.find_symbol ge cnt = Some b ->
      Mem.valid_access m Mint64 b 0 Writable (Some cp) ->
      Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (nat64 (length ss))) ->
      exists m',
        Mem.storev Mint64 m (Vptr b Ptrofs.zero) (Vlong (Int64.add (nat64 (length ss)) Int64.one)) cp = Some m' /\
          star (step1) ge
               (State f (switch cnt (ss ++ s :: ss') s_else) k e le m)
               E0
               (State f s k e le m').
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
      exploit (switch_clause_spec ge cnt f e le m b k (nat64 (length ss)) (Z.of_nat (length ss)) s s_else); auto.
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

    Variable ge: Senv.t.

    Definition not_in_env (e: env) id := e ! id = None.

    (* Definition wf_env (e: env) := *)
    (*   forall id, if (Senv.public_symbol ge id) then not_in_env e id else True. *)
    Definition wf_env (e: env) :=
      forall id, match Senv.find_symbol ge id with
            | Some _ => not_in_env e id
            | _ => True
            end.

    Definition eventval_to_val (v: eventval): val :=
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

    Definition list_eventval_to_list_val (vs: list eventval): list val :=
      List.map (eventval_to_val) vs.

    Definition eventval_to_type (v: eventval): type :=
      match v with
      | EVint _ => Tint I32 Signed noattr
      | EVlong _ => Tlong Signed noattr
      | EVfloat _ => Tfloat F64 noattr
      | EVsingle _ => Tfloat F32 noattr
      | EVptr_global id _ => Tpointer Tvoid noattr
      end.

    Fixpoint list_eventval_to_typelist (vs: list eventval): typelist :=
      match vs with
      | nil => Tnil
      | cons v vs' => Tcons (eventval_to_type v) (list_eventval_to_typelist vs')
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

    Definition list_eventval_to_list_expr (vs: list eventval): list expr :=
      List.map eventval_to_expr vs.

    Lemma typeof_eventval_to_expr_type
          v
      :
      typeof (eventval_to_expr v) = eventval_to_type v.
    Proof. destruct v; simpl; auto. apply ptr_of_id_ofs_typeof. Qed.

    (* Definition wf_eventval_env (e: env) (v: eventval): Prop := *)
    (*   match v with *)
    (*   | EVptr_global id _ => wf_env e id *)
    (*   | _ => True *)
    (*   end. *)

    Definition wf_eventval_pub (v: eventval): Prop :=
      match v with
      | EVptr_global id _ => (Senv.public_symbol ge id = true)
      | _ => True
      end.

    (* Definition wf_eventval_ge (v: eventval): Prop := *)
    (*   match v with *)
    (*   | EVptr_global id _ => (exists b, Genv.find_symbol ge id = Some b) *)
    (*   | _ => True *)
    (*   end. *)

    (* Lemma wf_eventval_pub_ge *)
    (*       v *)
    (*   : *)
    (*   wf_eventval_pub v -> wf_eventval_ge v. *)
    (* Proof. intros H. destruct v; simpl in *; auto. apply Genv.public_symbol_exists in H; auto. Qed. *)

  End CONV.


  Section CODEAUX.

    (* We extract function data: argument types, fn_return, rn_callconv from signature *)
    (* Correctness should follow from eventval_match *)
    Definition typ_to_type: typ -> type :=
      fun t: typ =>
        match t with
        | AST.Tint => Tint I32 Signed noattr
        | AST.Tfloat => Tfloat F64 noattr
        | AST.Tlong => Tlong Signed noattr
        | AST.Tsingle => Tfloat F32 noattr
        (* do not appear in eventval_match *)
        | AST.Tany32 => Tint I32 Signed noattr
        | AST.Tany64 => Tlong Signed noattr
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


  Section CONV.

    (* Context {F: Type}. *)
    (* Context {V: Type}. *)
    (* Variable ge: Genv.t F V. *)

    Variable ge: Senv.t.

    (* Type: Tvoid has size 1, which is what we want *)
    Definition expr_of_addr (id: ident) (ofs: ptrofs): expr :=
      ptr_of_id_ofs id ofs.

    Definition chunk_to_type (ch: memory_chunk): option type :=
      match ch with
      | Mint8signed => Some (Tint I8 Signed noattr)
      | Mint8unsigned => Some (Tint I8 Unsigned noattr)
      | Mint16signed => Some (Tint I16 Signed noattr)
      | Mint16unsigned => Some (Tint I16 Unsigned noattr)
      | Mint32 => Some (Tint I32 Signed noattr)
      | Mint64 => Some (Tlong Signed noattr)
      | Mfloat32 => Some (Tfloat F32 noattr)
      | Mfloat64 => Some (Tfloat F64 noattr)
      | Many32 => None
      | Many64 => None
      end.

    Lemma access_mode_chunk_to_type_wf
          ch ty
          (CT: chunk_to_type ch = Some ty)
      :
      access_mode ty = By_value ch.
    Proof. destruct ch; inv CT; ss. Qed.

    Definition chunk_val_to_expr (ch: memory_chunk) (v: val) : option expr :=
      match chunk_to_type ch with
      | Some ty =>
          match v with
          | Vint i => Some (Econst_int i ty)
          | Vlong i => Some (Econst_long i ty)
          | Vfloat f => Some (Econst_float f ty)
          | Vsingle f => Some (Econst_single f ty)
          | Vptr b ofs =>
              match Senv.invert_symbol ge b with
              | Some id => Some (ptr_of_id_ofs id ofs)
              | None => None
              end
          (* | Vint i => Some (Econst_int i (Tint I32 Signed noattr)) *)
          (* | Vlong i => Some (Econst_long i (Tlong Signed noattr)) *)
          (* | Vfloat f => Some (Econst_float f (Tfloat F64 noattr)) *)
          (* | Vsingle f => Some (Econst_single f (Tfloat F32 noattr)) *)
          (* | Vptr b ofs => let id := senv_invert_symbol_total ge b in Some (ptr_of_id_ofs id ofs) *)
          | Vundef => None
          end
      | None => None
      end.

  End CONV.


  Section CODE.
    (** converting *informative* trace to code **)

    Variable ge: Senv.t.

    Definition code_mem_delta_storev cp0 (d: mem_delta_storev): statement :=
      let '(ch, ptr, v, cp) := d in
      match ptr with
      | Vptr b ofs =>
          match Senv.invert_symbol ge b with
          | Some id =>
              match chunk_to_type ch, chunk_val_to_expr ge ch v with
              | Some ty, Some ve =>
                  if ((Senv.public_symbol ge id) && (wf_chunk_val_b ch v) && (cp0 =? cp)%positive)
                  then Sassign (Ederef (expr_of_addr id ofs) ty) ve
                  else Sskip
              | _, _ => Sskip
              end
          | None => Sskip
          end
      | _ => Sskip
      end.

    Definition code_mem_delta_kind cp (d: mem_delta_kind): statement :=
      match d with
      | mem_delta_kind_storev dd => code_mem_delta_storev cp dd
      | _ => Sskip
      end.

    Definition code_mem_delta cp (d: mem_delta) (snext: statement): statement :=
      fold_right Ssequence snext (map (code_mem_delta_kind cp) d).

    Definition code_bundle_call cp (tr: trace) (id: ident) (evargs: list eventval) (sg: signature) (d: mem_delta): statement :=
      let tys := from_sig_fun_data sg in
      code_mem_delta cp d (Scall None (Evar id (Tfunction tys.(dargs) tys.(dret) tys.(dcc))) (list_eventval_to_list_expr evargs)).

    Definition code_bundle_return cp (tr: trace) (evr: eventval) (d: mem_delta): statement :=
      code_mem_delta cp d (Sreturn (Some (eventval_to_expr evr))).

    Definition code_bundle_builtin cp (tr: trace) (ef: external_function) (evargs: list eventval) (d: mem_delta): statement :=
      code_mem_delta cp d (Sbuiltin None ef (list_eventval_to_typelist evargs) (list_eventval_to_list_expr evargs)).

    Definition code_bundle_event cp (be: bundle_event): statement :=
      match be with
      | Bundle_call tr id evargs sg d => code_bundle_call cp tr id evargs sg d
      | Bundle_return tr evr d => code_bundle_return cp tr evr d
      | Bundle_builtin tr ef evargs d => code_bundle_builtin cp tr ef evargs d
      end.

    Definition one_expr: expr := Econst_int Int.one (Tint I32 Signed noattr).

    Definition switch_bundle_events cnt cp (tr: bundle_trace) :=
      switch cnt (map (fun ib => code_bundle_event cp (snd ib)) tr) (Sreturn None).

    (* A while(1)-loop with big if-then-elses inside it *)
    Definition code_bundle_trace cp (cnt: ident) (tr: bundle_trace): statement :=
      Swhile one_expr (switch_bundle_events cnt cp tr).

  End CODE.


  Section CODEPROOFS.

    Lemma ptr_of_id_ofs_eval
          (ge: genv) id ofs e b cp le m
          (GE1: wf_env ge e)
          (GE2: Senv.find_symbol ge id = Some b)
      :
      eval_expr ge e cp le m (ptr_of_id_ofs id ofs) (Vptr b ofs).
    Proof.
      specialize (GE1 id). rewrite GE2 in GE1.
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

    Lemma code_mem_delta_cons
          (ge: Senv.t) cp k d sn
      :
      code_mem_delta ge cp (k :: d) sn =
        Ssequence (code_mem_delta_kind ge cp k) (code_mem_delta ge cp d sn).
    Proof. unfold code_mem_delta. ss. Qed.

    Lemma code_mem_delta_app
          (ge: Senv.t) cp d1 d2 sn
      :
      code_mem_delta ge cp (d1 ++ d2) sn = (code_mem_delta ge cp d1 (code_mem_delta ge cp d2 sn)).
    Proof.
      revert sn d2. induction d1; intros; ss.
      rewrite ! code_mem_delta_cons. erewrite IHd1. auto.
    Qed.

    Lemma type_of_chunk_val_to_expr
          (ge: Senv.t) ch ty v e
          (WF: wf_chunk_val_b ch v)
          (CT: chunk_to_type ch = Some ty)
          (CVE: chunk_val_to_expr ge ch v = Some e)
      :
      typeof e = ty.
    Proof. unfold chunk_val_to_expr in CVE. rewrite CT in CVE. des_ifs. Qed.

    Definition val_is_int (v: val) := (match v with | Vint _ => True | _ => False end).
    Definition val_is_not_int (v: val) := (match v with | Vint _ => False | _ => True end).

    Lemma val_cases v: (val_is_int v) \/ (val_is_not_int v).
    Proof. destruct v; ss; auto. Qed.

    Lemma sem_cast_chunk_val
          (ge: Senv.t) m ch ty v e
          (WF: wf_chunk_val_b ch v)
          (CT: chunk_to_type ch = Some ty)
          (CVE: chunk_val_to_expr ge ch v = Some e)
          (NINT: val_is_not_int v)
      :
      Cop.sem_cast v (typeof e) ty m = Some v.
    Proof.
      erewrite type_of_chunk_val_to_expr; eauto. apply Cop.cast_val_casted. clear - WF CT NINT.
      unfold wf_chunk_val_b, wf_chunk_val_b in WF. des_ifs; ss; inv CT; econs.
    Qed.

    Definition cast_chunk_int (ch: memory_chunk) (i: int): val :=
      match ch with
      | Mint8signed => Vint (Int.sign_ext 8 i)
      | Mint8unsigned => Vint (Int.zero_ext 8 i)
      | Mint16signed => Vint (Int.sign_ext 16 i)
      | Mint16unsigned => Vint (Int.zero_ext 16 i)
      | Mint32 => Vint i
      | _ => Vundef
      end.

    Lemma chunk_val_to_expr_eval
          (ge: genv) ch v exp e cp le m
          (EXP: chunk_val_to_expr ge ch v = Some exp)
          (WF: wf_chunk_val_b ch v)
      :
      eval_expr ge e cp le m exp v.
    Proof. unfold chunk_val_to_expr in EXP. des_ifs; ss; econs. Qed.

    Lemma wf_chunk_val_chunk_to_type
          ch v
          (WF: wf_chunk_val_b ch v)
      :
      exists ty, chunk_to_type ch = Some ty.
    Proof. unfold wf_chunk_val_b in WF. des_ifs; ss; eauto. Qed.

    Lemma wf_chunk_val_chunk_val_to_expr
          (ge: Senv.t) ch v
          (WF: wf_chunk_val_b ch v)
      :
      exists ve, chunk_val_to_expr ge ch v = Some ve.
    Proof.
      unfold chunk_val_to_expr. exploit wf_chunk_val_chunk_to_type; eauto.
      intros (ty & TY). rewrite TY. unfold wf_chunk_val_b in WF. des_ifs; ss; eauto.
    Qed.

    Lemma code_mem_delta_storev_correct
          (ge: genv) f k e le m m'
          d
          (WFE: wf_env ge e)
          (STORE: mem_delta_apply_storev (Some m) d = Some m')
          (WF: wf_mem_delta_storev_b ge (comp_of f) d)
      :
      step1 ge (State f (code_mem_delta_storev ge (comp_of f) d) k e le m)
            E0 (State f Sskip k e le m').
    Proof.
      unfold wf_mem_delta_storev_b in WF. des_ifs. rename m0 into ch, i into ofs. ss.
      exploit wf_chunk_val_chunk_to_type; eauto. intros (ty & TY).
      exploit wf_chunk_val_chunk_val_to_expr; eauto. intros (ve & EXPR).
      rewrite H, Heq, TY, EXPR.
      destruct (val_cases v) as [INT | NINT].
      { unfold val_is_int in INT. des_ifs. clear INT. eapply step_assign.
        - econs. unfold expr_of_addr. eapply ptr_of_id_ofs_eval; auto.
          eapply Genv.invert_find_symbol; eauto.
        - instantiate (1:=Vint i). eapply chunk_val_to_expr_eval; eauto.
        - instantiate (1:=cast_chunk_int ch i). erewrite type_of_chunk_val_to_expr; eauto.
          unfold chunk_to_type in TY. destruct ch; ss; inv TY.
          + unfold Cop.sem_cast. ss. des_ifs.
          + unfold Cop.sem_cast. ss. des_ifs.
          + unfold Cop.sem_cast. ss. des_ifs.
          + unfold Cop.sem_cast. ss. des_ifs.
          + unfold Cop.sem_cast. ss. des_ifs.
        - simpl_expr. eapply access_mode_chunk_to_type_wf; eauto.
          rewrite <- STORE. apply Pos.eqb_eq in WF. subst c. destruct ch; ss.
          + rewrite Mem.store_int8_sign_ext. auto.
          + rewrite Mem.store_int8_zero_ext. auto.
          + rewrite Mem.store_int16_sign_ext. auto.
          + rewrite Mem.store_int16_zero_ext. auto.
      }
      { rewrite WF, H0. ss. eapply step_assign.
        - econs. unfold expr_of_addr. eapply ptr_of_id_ofs_eval; auto.
          eapply Genv.invert_find_symbol; eauto.
        - instantiate (1:=v). eapply chunk_val_to_expr_eval; eauto.
        - ss. eapply sem_cast_chunk_val; eauto.
        - simpl_expr. eapply access_mode_chunk_to_type_wf; eauto.
          apply Pos.eqb_eq in WF. clarify.
      }
    Qed.

    Lemma wf_mem_delta_storev_false_is_skip
          (ge: Senv.t) cp d
          (NWF: wf_mem_delta_storev_b ge cp d = false)
      :
      code_mem_delta_storev ge cp d = Sskip.
    Proof. destruct d as [[[ch ptr] v] cp0]. ss. des_ifs. Qed.

    Lemma code_mem_delta_correct
          (ge: genv)
          f k e le m m'
          d snext
          (WFE: wf_env ge e)
          (APPD: mem_delta_apply_wf ge (comp_of f) d (Some m) = Some m')
      :
      (star step1 ge (State f (code_mem_delta ge (comp_of f) d snext) k e le m)
            E0 (State f snext k e le m')).
    Proof.
      revert m m' snext APPD. induction d; intros.
      { unfold mem_delta_apply_wf in APPD. ss. inv APPD. unfold code_mem_delta. ss. econs 1. }
      rewrite mem_delta_apply_wf_cons in APPD. rewrite code_mem_delta_cons.
      des_ifs.
      - exploit mem_delta_apply_wf_some; eauto. intros (mi & APPD0). rewrite APPD0 in APPD.
        destruct a; ss. econs 2.
        { eapply step_seq. }
        econs 2.
        { eapply code_mem_delta_storev_correct; eauto. }
        take_step. eapply IHd; eauto. eauto. auto.
      - destruct a; ss.
        rewrite wf_mem_delta_storev_false_is_skip; auto.
        all: take_step; take_step; eapply IHd; eauto.
    Qed.

    Lemma code_bundle_trace_spec
          (ge: genv) cp cnt tr
          f e le m k
      :
      star step1 ge
           (State f (code_bundle_trace ge cp cnt tr) k e le m)
           E0
           (State f (switch_bundle_events ge cnt cp tr)
                  (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge cnt cp tr)) Sskip k)
                  e le m).
    Proof.
      econs 2.
      { unfold code_bundle_trace, Swhile. eapply step_loop. }
      econs 2.
      { eapply step_seq. }
      econs 2.
      { eapply step_ifthenelse. simpl_expr. ss. }
      rewrite Int.eq_false; ss. econs 2.
      { eapply step_skip_seq. }
      econs 1. all: eauto.
    Qed.

  End CODEPROOFS.


  Section GEN.

    Definition list_typ_to_list_type (ts: list typ): list type := map typ_to_type ts.

    Definition gen_function (ge: Senv.t) (cnt: ident) (params: list (ident * type)) (tr: bundle_trace) (a_f: Asm.function): function :=
      let a_sg := Asm.fn_sig a_f in
      (* let targs := list_typ_to_list_type a_sg.(sig_args) in *)
      let tret := rettype_to_type a_sg.(sig_res) in
      let cc := a_sg.(sig_cc) in
      let cp := Asm.fn_comp a_f in
      mkfunction cp
                 tret
                 cc
                 params
                 []
                 []
                 (code_bundle_trace ge cp cnt tr).

    Definition gen_fundef (ge: Senv.t) (cnt: ident) params (tr: bundle_trace) (a_fd: Asm.fundef): Clight.fundef :=
      match a_fd with
      | AST.Internal a_f => Internal (gen_function ge cnt params tr a_f)
      | AST.External ef =>
          let dsg := from_sig_fun_data (ef_sig ef) in
          External ef dsg.(dargs) dsg.(dret) dsg.(dcc)
      end.

    Definition gen_globvar (gv: globvar unit): globvar type :=
      mkglobvar Tvoid gv.(gvar_comp) gv.(gvar_init) gv.(gvar_readonly) gv.(gvar_volatile).

    Definition default_globvar: globvar type :=
      mkglobvar Tvoid default_compartment [] false false.

    Definition gen_globdef ge cnt params tr (a_gd: globdef Asm.fundef unit): globdef Clight.fundef type :=
      match a_gd with
      | Gfun a_fd => Gfun (gen_fundef ge cnt params tr a_fd)
      | Gvar a_gv => Gvar (gen_globvar a_gv)
      end.

    Definition gen_counter cp: globdef Clight.fundef type :=
      Gvar (mkglobvar type_counter cp [(Init_int64 Int64.zero)] false false).

    (* Generate the max + 1 of the keys *)
    Definition next_id {A} (l: list (ident * A)): ident :=
      Pos.succ (fold_left (fun x '(i, _) => if (x <? i)%positive then i else x) l 1%positive).

    (* Generate fresh counter ids with definitions for each global definitions *)
    Definition gen_counter_defs m (gds: list (ident * globdef Asm.fundef unit)): PTree.t (ident * globdef Clight.fundef type) :=
      fold_left (fun pt '(id, gd) => PTree.set id (Pos.add id m, gen_counter (comp_of gd)) pt) gds (@PTree.empty _).

    Definition params_of := PTree.t (list (ident * type)).

    Fixpoint numbering {A} (i: ident) (l: list A): list (ident * A) :=
      match l with
      | [] => []
      | hd :: tl => (i, hd) :: (numbering (Pos.succ i) tl)
      end.

    Definition gen_params_one (m: ident) (gd: globdef Asm.fundef unit): option (list (ident * type)) :=
      match gd with
      | Gvar _ => None
      | Gfun fd =>
          let types := map typ_to_type (sig_args (funsig fd)) in
          Some (numbering m types)
      end.

    (* Generate fresh parameter ids for each function --- parameter ids for different functions are allowed to be duplicated *)
    Definition gen_params (m: ident) (gds: list (ident * globdef Asm.fundef unit)): params_of :=
      fold_left (fun pt '(id, gd) =>
                   match gen_params_one m gd with | Some ps => PTree.set id ps pt | None => pt end) gds (@PTree.empty _).

    Definition gen_progdef (ge: Senv.t) (tr: bundle_trace) a_gd (ocnt: option (ident * globdef Clight.fundef type)) (oparams: option (list (ident * type))): globdef Clight.fundef type :=
      match ocnt, oparams with
      | Some (cnt, _), Some params => gen_globdef ge cnt params tr a_gd
      | _, _ => Gvar default_globvar
      end.

    Definition get_id_tr (tr: bundle_trace) (id0: ident): bundle_trace := filter (fun '(id, _) => Pos.eqb id0 id) tr.

    Definition gen_prog_defs (a_ge: Senv.t) tr (gds: list (ident * globdef Asm.fundef unit)): list (ident * globdef Clight.fundef type) :=
      let m0 := next_id gds in
      let cnts := gen_counter_defs m0 gds in
      let cnt_defs := map snd (PTree.elements cnts) in
      let m1 := next_id cnt_defs in
      let params := gen_params m1 gds in
      (map (fun '(id, gd) => (id, gen_progdef a_ge (get_id_tr tr id) gd (cnts ! id) (params ! id))) gds) ++ cnt_defs.

    Program Definition gen_program tr (a_p: Asm.program): Clight.program :=
      let a_ge := Genv.globalenv a_p in
      @Build_program _
                     (gen_prog_defs a_ge tr a_p.(AST.prog_defs))
                     (AST.prog_public a_p)
                     (AST.prog_main a_p)
                     (AST.prog_pol a_p)
                     []
                     (@PTree.empty composite)
                     _.

  End GEN.


  Section GENPROOFS.

    Definition wf_keys {A} (l: list (ident * A)) := list_norepet (map fst l).

    Definition wf_params_of (pars: params_of) :=
      (forall id params, (pars ! id = Some params) -> list_norepet (var_names params)).

    Definition wf_params_of_sig (pars: params_of) (ge: Asm.genv) :=
      forall b f id params, (Genv.find_funct_ptr ge b = Some f) -> (Genv.find_symbol ge id = Some b) -> (pars ! id = Some params) ->
                       (list_typ_to_list_type (sig_args (funsig f)) = map snd params).

    Definition wf_params_of_symb (pars: params_of) (ge: Clight.genv) :=
      forall id b, (Senv.find_symbol ge id = Some b) ->
              forall fid ps, pars ! fid = Some ps -> ~ (In id (map fst ps)).

    Lemma next_id_lt
          A (l: list (ident * A))
          id a
          (IN: In (id, a) l)
      :
      Pos.lt id (next_id l).
    Proof.
    Admitted.

    Lemma gen_counter_defs_lt
          m agds
          id cnt cd
          (GET: (gen_counter_defs m agds) ! id = Some (cnt, cd))
      :
      (Pos.lt m cnt).
    Proof.
    Admitted.

    Lemma gen_params_lt
          m agds
          id ps
          (GET: (gen_params m agds) ! id = Some ps)
          p t
          (IN: In (p, t) ps)
      :
      Pos.lt m p.
    Proof.
    Admitted.

    Lemma gen_params_wf
          m agds
      :
      wf_params_of (gen_params m agds).
    Proof.
    Admitted.

    (* Lemma gen_params_wf_sig *)
    (*       m agds *)
    (*   : *)
    (*   wf_params_of_sig (gen_params m agds). *)
    (* Proof. *)
    (* Admitted. *)


    Lemma get_id_tr_cons
          id be tr
      :
      get_id_tr (be :: tr) id = if (Pos.eqb id (fst be)) then (be :: get_id_tr tr id) else (get_id_tr tr id).
    Proof. unfold get_id_tr. ss. des_ifs; ss; clarify. Qed.

    Lemma get_id_tr_app
          id tr1 tr2
      :
      get_id_tr (tr1 ++ tr2) id = (get_id_tr tr1 id) ++ (get_id_tr tr2 id).
    Proof. unfold get_id_tr. rewrite filter_app. auto. Qed.

    Lemma alloc_variables_wf_params_of_symb0
          ge cp e m params e' m'
          (AE: alloc_variables ge cp e m params e' m')
          (WFE: wf_env ge e)
          (pars: params_of)
          (WFP: wf_params_of_symb pars ge)
          fid vars
          (PAR: pars ! fid = Some vars)
          (INCL: forall x, In x params -> In x vars)
      :
      wf_env ge e'.
    Proof.
      revert_until AE. induction AE; ii.
      { eapply WFE. }
      eapply IHAE. 3: eapply PAR.
      3:{ i. eapply INCL. ss. right; auto. }
      2: auto.
      clear IHAE id0. unfold wf_env in *. i. specialize (WFE id0). des_ifs.
      unfold not_in_env in *. specialize (WFP _ _ Heq _ _ PAR).
      destruct (Pos.eqb_spec id id0).
      2:{ rewrite PTree.gso; auto. }
      subst id0. exfalso. apply WFP; clear WFP. specialize (INCL (id, ty)).
      replace id with (fst (id, ty)). 2: ss. apply in_map. apply INCL. ss. left; auto.
    Qed.

    Lemma alloc_variables_wf_params_of_symb
          ge cp m params e' m'
          (AE: alloc_variables ge cp empty_env m params e' m')
          (pars: params_of)
          (WFP: wf_params_of_symb pars ge)
          fid
          (PAR: pars ! fid = Some params)
      :
      wf_env ge e'.
    Proof. eapply alloc_variables_wf_params_of_symb0; eauto. ii. des_ifs. Qed.

  End GENPROOFS.


  Section GENV.

    Definition symbs_public (ge1 ge2: Senv.t) := (forall id : ident, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id).
    Definition symbs_find (ge1 ge2: Senv.t) := forall id b, Senv.find_symbol ge1 id = Some b -> Senv.find_symbol ge2 id = Some b.
    Definition symbs_volatile (ge1 ge2: Senv.t) := forall b, Senv.block_is_volatile ge2 b = Senv.block_is_volatile ge1 b.

    Definition match_symbs (ge1 ge2: Senv.t) := symbs_public ge1 ge2 /\ symbs_find ge1 ge2 /\ symbs_volatile ge1 ge2.

    Lemma match_symbs_meminj_public
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
      :
      meminj_public ge1 = meminj_public ge2.
    Proof.
      destruct MSYMB as (MSYMB1 & MSYMB2 & MSYMB3). unfold meminj_public. extensionalities b. des_ifs.
      - exfalso. apply Senv.invert_find_symbol in Heq. exploit MSYMB2; eauto. intros.
        apply Senv.find_invert_symbol in x0. rewrite x0 in Heq1. inv Heq1. specialize (MSYMB1 i0). clarify.
      - exfalso. apply Senv.invert_find_symbol in Heq. exploit MSYMB2; eauto. intros.
        apply Senv.find_invert_symbol in x0. clarify.
      - exfalso. apply Senv.invert_find_symbol in Heq. exploit MSYMB2; eauto. intros.
        apply Senv.find_invert_symbol in x0. rewrite x0 in Heq1. inv Heq1. specialize (MSYMB1 i0). clarify.
      - exfalso. rewrite MSYMB1 in Heq1. apply Senv.public_symbol_exists in Heq1. des.
        exploit MSYMB2; eauto. intros. apply Senv.invert_find_symbol in Heq0. clarify.
        apply Senv.find_invert_symbol in Heq1. clarify.
    Qed.

    Lemma match_symbs_wf_mem_delta_storev
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp0 d
      :
      wf_mem_delta_storev_b ge1 cp0 d = wf_mem_delta_storev_b ge2 cp0 d.
    Proof.
      destruct MSYMB as (MSYMB1 & MSYMB2 & MSYMB3).
      destruct d as [[[ch ptr] v] cp]. ss. des_ifs.
      - do 2 f_equal. apply Senv.invert_find_symbol, MSYMB2, Senv.find_invert_symbol in Heq. clarify.
      - exfalso. apply Senv.invert_find_symbol, MSYMB2, Senv.find_invert_symbol in Heq. clarify.
      - destruct (Senv.public_symbol ge2 i0) eqn:PUB; ss.
        exfalso. rewrite MSYMB1 in PUB. apply Senv.public_symbol_exists in PUB. des.
        exploit MSYMB2; eauto. intros. apply Senv.invert_find_symbol in Heq0. clarify.
        apply Senv.find_invert_symbol in PUB. clarify.
    Qed.

    Lemma match_symbs_wf_mem_delta_kind
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp
      :
      wf_mem_delta_kind_b ge1 cp = wf_mem_delta_kind_b ge2 cp.
    Proof. unfold wf_mem_delta_kind_b. extensionalities d. des_ifs. apply match_symbs_wf_mem_delta_storev; auto. Qed.

    Lemma match_symbs_get_wf_mem_delta
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp d
      :
      get_wf_mem_delta ge1 cp d = get_wf_mem_delta ge2 cp d.
    Proof. unfold get_wf_mem_delta. erewrite match_symbs_wf_mem_delta_kind; eauto. Qed.

    Lemma match_symbs_mem_delta_apply_wf
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp d m
      :
      mem_delta_apply_wf ge1 cp d m = mem_delta_apply_wf ge2 cp d m.
    Proof. unfold mem_delta_apply_wf. erewrite match_symbs_get_wf_mem_delta; eauto. Qed.

    Lemma match_symbs_code_mem_delta_kind
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp
      :
      code_mem_delta_kind ge1 cp = code_mem_delta_kind ge2 cp.
    Proof.
      extensionalities k. unfold code_mem_delta_kind. des_ifs.
      destruct d as [[[ch ptr] v] cp0]. ss. destruct ptr; ss.
      destruct MSYMB as (MSYMB1 & MSYMB2 & MSYMB3).
      destruct (Senv.invert_symbol ge1 b) eqn:INV1.
      { exploit Senv.invert_find_symbol; eauto. intros FIND1.
        exploit MSYMB2; eauto. intros FIND2. exploit Senv.find_invert_symbol; eauto. intros INV2.
        rewrite INV2. destruct (chunk_to_type ch) eqn:CHTY; auto.
        des_ifs.
        - apply andb_prop in Heq0, Heq2. des. apply andb_prop in Heq0, Heq2. des.
          assert (chunk_val_to_expr ge2 ch v = chunk_val_to_expr ge1 ch v).
          { unfold chunk_val_to_expr. rewrite CHTY. clear - Heq6.
            unfold wf_chunk_val_b in Heq6. des_ifs.
          }
          rewrite Heq, Heq1 in H. clarify.
        - exfalso. apply andb_prop in Heq0. des. apply andb_prop in Heq0. des.
          clarify. rewrite ! andb_true_r in Heq2. rewrite MSYMB1 in Heq2. clarify.
        - exfalso. apply andb_prop in Heq0. des. apply andb_prop in Heq0. des.
          apply (wf_chunk_val_chunk_val_to_expr (ge2)) in Heq3; eauto. des; clarify.
        - exfalso. apply andb_prop in Heq2. des. apply andb_prop in Heq2. des.
          clarify. rewrite ! andb_true_r in Heq0. rewrite MSYMB1 in Heq2; clarify.
        - exfalso. apply andb_prop in Heq1. des. apply andb_prop in Heq1. des.
          apply (wf_chunk_val_chunk_val_to_expr (ge1)) in Heq3; eauto. des; clarify.
      }
      { des_ifs.
        exfalso. apply andb_prop in Heq2. des. apply andb_prop in Heq2. des.
        rewrite MSYMB1 in Heq2. eapply Senv.public_symbol_exists in Heq2. des.
        exploit MSYMB2. eapply Heq2. intros FIND4. eapply Senv.invert_find_symbol in Heq. clarify.
        exploit Senv.find_invert_symbol. apply Heq2. intros INV3. clarify.
      }
    Qed.

    Lemma match_symbs_code_mem_delta
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp d s
      :
      code_mem_delta ge1 cp d s = code_mem_delta ge2 cp d s.
    Proof. unfold code_mem_delta. erewrite match_symbs_code_mem_delta_kind; eauto. Qed.

    Lemma match_symbs_code_bundle_call
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp tr id evargs sg d
      :
      code_bundle_call ge1 cp tr id evargs sg d = code_bundle_call ge2 cp tr id evargs sg d.
    Proof. unfold code_bundle_call. erewrite match_symbs_code_mem_delta; eauto. Qed.

    Lemma match_symbs_code_bundle_return
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp tr evr d
      :
      code_bundle_return ge1 cp tr evr d = code_bundle_return ge2 cp tr evr d.
    Proof. unfold code_bundle_return. erewrite match_symbs_code_mem_delta; eauto. Qed.

    Lemma match_symbs_code_bundle_builtin
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp tr ef evargs d
      :
      code_bundle_builtin ge1 cp tr ef evargs d = code_bundle_builtin ge2 cp tr ef evargs d.
    Proof. unfold code_bundle_builtin. erewrite match_symbs_code_mem_delta; eauto. Qed.

    Lemma match_symbs_code_bundle_events
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp
      :
      code_bundle_event ge1 cp = code_bundle_event ge2 cp.
    Proof.
      extensionalities be. unfold code_bundle_event. des_ifs.
      eapply match_symbs_code_bundle_call; auto. eapply match_symbs_code_bundle_return; auto. eapply match_symbs_code_bundle_builtin; auto.
    Qed.

    Lemma match_symbs_switch_bundle_events
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp cnt tr
      :
      switch_bundle_events ge1 cnt cp tr = switch_bundle_events ge2 cnt cp tr.
    Proof. unfold switch_bundle_events. erewrite match_symbs_code_bundle_events; eauto. Qed.

    Lemma match_symbs_code_bundle_trace
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
          cp cnt tr
      :
      code_bundle_trace ge1 cp cnt tr = code_bundle_trace ge2 cp cnt tr.
    Proof. unfold code_bundle_trace. erewrite match_symbs_switch_bundle_events; eauto. Qed.


    Lemma match_symbs_symbols_inject
          ge1 ge2
          (MSYMB: match_symbs ge1 ge2)
      :
      symbols_inject (meminj_public ge1) ge1 ge2.
    Proof.
    Admitted.

  End GENV.


  Section PROOF.

    Lemma filter_filter
          A (l: list A) (p q: A -> bool)
      :
      filter q (filter p l) = filter (fun a => (p a) && (q a)) l.
    Proof.
      induction l; ss. des_ifs; ss; clarify.
      f_equal. auto.
    Qed.

    Lemma get_wf_mem_delta_idem
          ge cp d
      :
      get_wf_mem_delta ge cp (get_wf_mem_delta ge cp d) = get_wf_mem_delta ge cp d.
    Proof. unfold get_wf_mem_delta. rewrite filter_filter. f_equal. extensionalities k. apply andb_diag. Qed.

    Lemma mem_delta_apply_wf_get_wf_mem_delta
          ge cp d m
      :
      mem_delta_apply_wf ge cp d m = mem_delta_apply_wf ge cp (get_wf_mem_delta ge cp d) m.
    Proof. unfold mem_delta_apply_wf. rewrite get_wf_mem_delta_idem. auto. Qed.

    Lemma wf_mem_delta_kind_is_wf
          ge cp k
          (WF: wf_mem_delta_kind_b ge cp k)
      :
      mem_delta_kind_inj_wf cp (meminj_public ge) k.
    Proof. unfold wf_mem_delta_kind_b in WF. des_ifs. unfold wf_mem_delta_storev_b in WF. ss. des_ifs. apply Pos.eqb_eq in WF. auto. Qed.

    Lemma get_wf_mem_delta_is_wf
          cp ge d
      :
      mem_delta_inj_wf cp (meminj_public ge) (get_wf_mem_delta ge cp d).
    Proof. induction d; ss. des_ifs. econs; auto. apply wf_mem_delta_kind_is_wf; auto. Qed.

    Lemma mem_delta_apply_establish_inject2
          (ge: Senv.t) k m0 m0'
          (INJ: Mem.inject k m0 m0')
          (INCR: inject_incr (meminj_public ge) k)
          (NALLOC: meminj_not_alloc (meminj_public ge) m0)
          d cp m1
          (APPD: mem_delta_apply_wf ge cp d (Some m0) = Some m1)
          (FO: public_first_order ge m1)
      :
      exists m1', mem_delta_apply_wf ge cp d (Some m0') = Some m1' /\ Mem.inject (meminj_public ge) m1 m1'.
    Proof.
      unfold mem_delta_apply_wf in APPD. rewrite mem_delta_apply_wf_get_wf_mem_delta. eapply mem_delta_apply_establish_inject; eauto.
      apply get_wf_mem_delta_is_wf.
      unfold public_first_order in FO. ii. unfold meminj_public in H. des_ifs. apply Senv.invert_find_symbol in Heq.
      eapply FO; eauto.
    Qed.

    Lemma mem_delta_apply_establish_inject_preprocess2
          (ge: Senv.t) (k: meminj) m0 m0'
          (INJ: Mem.inject k m0 m0')
          pch pb pofs pv pcp m0''
          (PRE: Mem.store pch m0' pb pofs pv pcp = Some m0'')
          (PREB: forall b ofs, (meminj_public ge) b <> Some (pb, ofs))
          (INCR: inject_incr (meminj_public ge) k)
          (NALLOC: meminj_not_alloc (meminj_public ge) m0)
          d cp m1
          (APPD: mem_delta_apply_wf ge cp d (Some m0) = Some m1)
          (FO: public_first_order ge m1)
      :
      exists m1', mem_delta_apply_wf ge cp d (Some m0'') = Some m1' /\ Mem.inject (meminj_public ge) m1 m1'.
    Proof.
      unfold mem_delta_apply_wf in APPD. rewrite mem_delta_apply_wf_get_wf_mem_delta.
      eapply mem_delta_apply_establish_inject_preprocess; eauto.
      apply get_wf_mem_delta_is_wf.
      unfold public_first_order in FO. ii. unfold meminj_public in H. des_ifs. apply Senv.invert_find_symbol in Heq.
      eapply FO; eauto.
    Qed.

    TODO

    (* Lemma mem_delta_apply_establish_inject_preprocess2 *)
    (*       (ge: Senv.t) (k: meminj) m0 m0' *)
    (*       (INJ: Mem.inject k m0 m0') *)
    (*       pch pb pofs pv pcp m0'' *)
    (*       (PRE: Mem.store pch m0' pb pofs pv pcp = Some m0'') *)
    (*       (PREB: forall b ofs, (meminj_public ge) b <> Some (pb, ofs)) *)
    (*       (INCR: inject_incr (meminj_public ge) k) *)
    (*       (NALLOC: meminj_not_alloc (meminj_public ge) m0) *)
    (*       d cp m1 *)
    (*       (APPD: mem_delta_apply_wf ge cp d (Some m0) = Some m1) *)
    (*       (FO: public_first_order ge m1) *)
    (*   : *)
    (*   exists m1', mem_delta_apply_wf ge cp d (Some m0'') = Some m1' /\ Mem.inject (meminj_public ge) m1 m1'. *)
    (* Proof. *)
    (*   unfold mem_delta_apply_wf in APPD. rewrite mem_delta_apply_wf_get_wf_mem_delta. *)
    (*   eapply mem_delta_apply_establish_inject_preprocess; eauto. *)
    (*   apply get_wf_mem_delta_is_wf. *)
    (*   unfold public_first_order in FO. ii. unfold meminj_public in H. des_ifs. apply Senv.invert_find_symbol in Heq. *)
    (*   eapply FO; eauto. *)
    (* Qed. *)

  End PROOF.


  Section INVS.

    Definition cnt_ids := PTree.t ident.

    Definition wf_counter (ge: Senv.t) (m: mem) cp (n: nat) (cnt: ident): Prop :=
      (Senv.public_symbol ge cnt = false) /\
        exists b, (Senv.find_symbol ge cnt = Some b) /\
               (Mem.valid_access m Mint64 b 0 Writable (Some cp)) /\
               (Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (nat64 n))).

    Definition wf_counters (ge: Clight.genv) (m: mem) (tr: bundle_trace) (cnts: cnt_ids) :=
      (forall id0 id1 cnt, (cnts ! id0 = Some cnt) -> (cnts ! id1 = Some cnt) -> (id0 = id1)) /\
        (forall id b (f: function),
            (Genv.find_symbol ge id = Some b) -> (Genv.find_funct_ptr ge b = Some (Internal f)) ->
            (exists cnt, (cnts ! id = Some cnt) /\ (wf_counter ge m (comp_of f) (length (get_id_tr tr id)) cnt))).

    Definition not_global_blks (ge: Senv.t) (ebs: list block) :=
      Forall (fun b => Senv.invert_symbol ge b = None) ebs.

    Definition blocks_of_env2 ge e : list block := (map (fun x => fst (fst x)) (blocks_of_env ge e)).

    Inductive wf_c_cont (ge: Clight.genv) : mem -> cont -> Prop :=
    | wf_c_cont_nil
        m
      :
      wf_c_cont ge m Kstop
    | wf_c_cont_cons
        m ck
        f e le s1 s2 m' ck'
        (WFENV: wf_env ge e)
        (NINJ: not_global_blks (ge) (blocks_of_env2 ge e))
        (CK: ck = Kcall None f e le (Kloop1 s1 s2 ck'))
        (FREE: Mem.free_list m (blocks_of_env ge e) (comp_of f) = Some m')
        (IND: wf_c_cont ge m' ck')
      :
      wf_c_cont ge m ck.

    Definition wf_c_stmt (ge: Senv.t) cp cnts id tr stmt :=
      forall cnt, (cnts ! id = Some cnt) -> stmt = code_bundle_trace ge cp cnt (get_id_tr tr id).

    Definition wf_c_nb (ge: Clight.genv) (m: mem) :=
      (Genv.genv_next ge <= Mem.nextblock m)%positive.

    Definition wf_c_state (ge: Clight.genv) (tr ttr: bundle_trace) (cnts: cnt_ids) id (cst: Clight.state) :=
      match cst with
      | State f stmt k_c e le m_c =>
          wf_counters ge m_c tr cnts /\
            (exists m_c', Mem.free_list m_c (blocks_of_env ge e) (comp_of f) = Some m_c' /\ wf_c_cont ge m_c' k_c) /\
            wf_c_stmt ge (comp_of f) cnts id ttr stmt /\
            (wf_env ge e /\ (not_global_blks (ge) (blocks_of_env2 ge e)) /\ (wf_c_nb ge m_c))
            (* (wf_env ge e /\ wf_env_unique_blocks e /\ wf_env_mem ge (comp_of f) e m_c) *)
      | _ => False
      end.

    Definition not_inj_blks (j: meminj) (ebs: list block) :=
      Forall (fun b => j b = None) ebs.

    Lemma not_global_is_not_inj_bloks
          ge l
          (NGB: not_global_blks ge l)
      :
      not_inj_blks (meminj_public ge) l.
    Proof. induction NGB. ss. econs; eauto. unfold meminj_public. des_ifs. Qed.



    Definition eq_policy (ge1: Asm.genv) (ge2: genv) :=
      Genv.genv_policy ge1 = Genv.genv_policy ge2.

    Definition match_genv (ge: Asm.genv) (ge': genv) :=
      (match_symbs ge ge') /\ (eq_policy ge ge').

    Definition match_mem (ge: Senv.t) (k: meminj) (m_i m_c: mem): Prop :=
      let j := meminj_public ge in
      (Mem.inject k m_i m_c) /\ (inject_incr j k) /\ (meminj_not_alloc j m_i).
    (* /\ (public_rev_perm m_i m_c). *)

    Definition match_cur_fun (ge_i: Asm.genv) (ge_c: genv) (cur: block) f (id: ident): Prop :=
      (Genv.find_funct_ptr ge_c cur = Some (Internal f)) /\
        (exists f_i, Genv.find_funct_ptr ge_i cur = Some (AST.Internal f_i)) /\
        (Genv.invert_symbol ge_i cur = Some id).

    Definition match_find_def (ge_i: Asm.genv) (ge_c: Clight.genv) (cnts: cnt_ids) (pars: params_of) tr :=
      forall b gd_i id,
        Genv.find_def ge_i b = Some gd_i ->
        Senv.invert_symbol ge_i b = Some id ->
        match (cnts ! id), (pars ! id) with
        | Some cnt, Some params =>
            Genv.find_def ge_c b = Some (gen_globdef ge_i cnt params (get_id_tr tr id) gd_i)
        | _, _ => False
        end.

    Inductive match_cont (ge: Clight.genv) (tr: bundle_trace) (cnts: cnt_ids) : (cont) -> (ir_conts) -> Prop :=
    | match_cont_nil
        ck ik
        (CK: ck = Kstop)
        (IK: ik = nil)
      :
      match_cont ge tr cnts ck ik
    | match_cont_cons
        ck ik
        f e le cnt id ck'
        b ik'
        (FUN: Genv.find_funct_ptr ge b = Some (Internal f))
        (ID: Genv.invert_symbol ge b = Some id)
        (CNT: cnts ! id = Some cnt)
        (CK: ck = Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge cnt (comp_of f) (get_id_tr tr id))) Sskip ck'))
        (IK: ik = (ir_cont b) :: ik')
        (IND: match_cont ge tr cnts ck' ik')
      :
      match_cont ge tr cnts ck ik.

    Definition match_params pars (ge_c: genv) (ge_i: Asm.genv) :=
      (wf_params_of pars) /\ (wf_params_of_sig pars ge_i) /\ (wf_params_of_symb pars ge_c).

    Definition match_cnts cnts (ge_c: genv) (k: meminj) :=
      forall id cnt cnt_b, (cnts ! id = Some cnt) -> (Genv.find_symbol ge_c cnt = Some cnt_b) ->
                      (forall b ofs, k b <> Some (cnt_b, ofs)).

    Definition match_state (ge_i: Asm.genv) (ge_c: Clight.genv) (k: meminj) tr cnts pars id (ist: ir_state) (cst: Clight.state) :=
      match ist, cst with
      | Some (cur, m_i, k_i), State f _ k_c e le m_c =>
          (match_genv ge_i ge_c) /\ (match_mem ge_i k m_i m_c) /\
            (match_cur_fun ge_i ge_c cur f id) /\ (match_find_def ge_i ge_c cnts pars tr) /\
            (match_cont ge_c tr cnts k_c k_i) /\
            (match_params pars ge_c ge_i) /\
            (match_cnts cnts ge_c k)
      | _, _ => False
      end.

  End INVS.


  Definition meminj_same_block (j : meminj) :=
    forall b1 b2 del, j b1 = Some (b2, del) -> b1 = b2.


  Section PROOF.

    (* Properties *)
    Lemma eventval_match_transl
          (ge: Senv.t)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      eventval_match ge ev (typ_of_type (typ_to_type ty)) (eventval_to_val ge ev).
    Proof.
      inversion EM; subst; simpl; try constructor.
      setoid_rewrite H0. unfold Tptr in *. destruct Archi.ptr64; auto.
    Qed.

    Lemma eventval_match_eventval_to_val
          (ge: Senv.t)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      eventval_to_val ge ev = v.
    Proof. inversion EM; subst; simpl; auto. setoid_rewrite H0. auto. Qed.

    Lemma eventval_list_match_transl
          (ge: Senv.t)
          evs tys vs
          (EM: eventval_list_match ge evs tys vs)
      :
      eventval_list_match ge evs (typlist_of_typelist (list_typ_to_typelist tys)) (list_eventval_to_list_val ge evs).
    Proof. induction EM; simpl. constructor. constructor; auto. eapply eventval_match_transl; eauto. Qed.

    Lemma eventval_list_match_transl_val
          (ge: Senv.t)
          evs tys vs
          (EM: eventval_list_match ge evs tys vs)
      :
      eventval_list_match ge evs tys (list_eventval_to_list_val ge evs).
    Proof. induction EM; simpl. constructor. constructor; auto. erewrite eventval_match_eventval_to_val; eauto. Qed.

    Lemma typ_type_typ
          (ge: Senv.t)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      typ_of_type (typ_to_type ty) = ty.
    Proof. inversion EM; simpl; auto. subst. unfold Tptr. destruct Archi.ptr64; simpl; auto. Qed.

    Lemma eventval_to_expr_val_eval
          (ge: genv) en cp temp m ev ty v
          (WFENV: wf_env ge en)
          (EM: eventval_match ge ev ty v)
          (* (WFGE: wf_eventval_ge ge ev) *)
      :
      eval_expr ge en cp temp m (eventval_to_expr ev) (eventval_to_val ge ev).
    Proof. destruct ev; simpl in *; try constructor. inv EM. setoid_rewrite H4. eapply ptr_of_id_ofs_eval; auto. Qed.

    Lemma sem_cast_eventval_match
          (ge: Senv.t) v ty vv m
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
      { unfold Cop.sem_cast. simpl. rewrite ARCH. simpl. rewrite pred_dec_true; auto. }
      { unfold Cop.sem_cast. simpl. rewrite ARCH. auto. }
    Qed.

    Lemma list_eventval_to_expr_val_eval
          (ge: genv) en cp temp m evs tys
          (* (WFENV: Forall (wf_eventval_env en) evs) *)
          (WFENV: wf_env ge en)
          (EMS: eventval_list_match ge evs (typlist_of_typelist (list_typ_to_typelist tys)) (list_eventval_to_list_val ge evs))
      :
      eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_typ_to_typelist tys) (list_eventval_to_list_val ge evs).
    Proof.
      revert en cp temp m WFENV.
      match goal with | [H: eventval_list_match _ _ ?t ?v |- _] => remember t as tys2; remember v as vs2 end.
      revert tys Heqtys2 Heqvs2. induction EMS; intros; subst; simpl in *.
      { destruct tys; simpl in *. constructor. congruence. }
      inversion Heqvs2; clear Heqvs2; subst; simpl in *.
      destruct tys; simpl in Heqtys2. congruence with Heqtys2.
      inversion Heqtys2; clear Heqtys2; subst; simpl in *.
      econstructor; eauto. eapply eventval_to_expr_val_eval; eauto.
      (* eapply eventval_match_wf_eventval_ge; eauto. *)
      eapply sem_cast_eventval_match; eauto.
    Qed.

    Lemma eventval_match_eventval_to_type
          (ge: Senv.t)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      eventval_match ge ev (typ_of_type (eventval_to_type ev)) v.
    Proof. inversion EM; subst; simpl; auto. Qed.

    Lemma list_eventval_match_eventval_to_type
          (ge: Senv.t)
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
          (ge: Senv.t)
          ev ty v
          (EM: eventval_match ge ev ty v)
      :
      eventval_match ge ev (proj_rettype (rettype_of_type (typ_to_type ty))) v.
    Proof.
      inversion EM; subst; simpl; try constructor.
      unfold Tptr in *. destruct Archi.ptr64; simpl; auto.
    Qed.

    (* Lemma sem_cast_eventval *)
    (*       (ge: cgenv) v m *)
    (*       (WFEV: wf_eventval_ge ge v) *)
    (*   : *)
    (*   Cop.sem_cast (eventval_to_val ge v) (typeof (eventval_to_expr v)) (eventval_to_type v) m = Some (eventval_to_val ge v). *)
    (* Proof. rewrite typeof_eventval_to_expr_type. destruct v; simpl in *; simpl_expr. destruct WFEV. rewrite H. simpl_expr. Qed. *)

    (* Lemma list_eventval_to_expr_val_eval2 *)
    (*       (ge: genv) en cp temp m evs *)
    (*       (WFENV: Forall (wf_eventval_env en) evs) *)
    (*       (WFGE: Forall (wf_eventval_ge ge) evs) *)
    (*   : *)
    (*   eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_eventval_to_typelist evs) (list_eventval_to_list_val ge evs). *)
    (* Proof. *)
    (*   move evs at top. revert ge en cp temp m WFENV WFGE. induction evs; intros; simpl in *. *)
    (*   constructor. *)
    (*   inversion WFENV; clear WFENV; subst. inversion WFGE; clear WFGE; subst. *)
    (*   econstructor; eauto. eapply eventval_to_expr_val_eval; eauto. *)
    (*   apply sem_cast_eventval; auto. *)
    (* Qed. *)

    Lemma eventval_match_sem_cast
          (* F V (ge: Genv.t F V) *)
          (ge: genv)
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

    (* Lemma list_eventval_to_expr_val_eval_typs *)
    (*       (ge: genv) en cp temp m evs tys vs *)
    (*       (WFENV: Forall (wf_eventval_env en) evs) *)
    (*       (EMS: eventval_list_match ge evs tys vs) *)
    (*   : *)
    (*   eval_exprlist ge en cp temp m (list_eventval_to_list_expr evs) (list_typ_to_typelist tys) vs. *)
    (* Proof. *)
    (*   revert en cp temp m WFENV. *)
    (*   induction EMS; intros; subst; simpl in *. constructor. *)
    (*   inversion WFENV; clear WFENV; subst. *)
    (*   econstructor; eauto. 2: eapply eventval_match_sem_cast; eauto. *)
    (*   exploit eventval_match_eventval_to_val. eauto. intros. rewrite <- H0. eapply eventval_to_expr_val_eval; auto. *)
    (*   eapply eventval_match_wf_eventval_ge; eauto. *)
    (* Qed. *)

    Lemma sem_cast_ptr
          b ofs m
      :
      Cop.sem_cast (Vptr b ofs) (Tpointer Tvoid noattr) (typ_to_type Tptr) m = Some (Vptr b ofs).
    Proof.
      unfold Tptr. destruct Archi.ptr64 eqn:ARCH; unfold Cop.sem_cast; simpl; rewrite ARCH; auto.
    Qed.

    Lemma sem_cast_proj_rettype
          (ge: genv) evres rty res m
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

    Lemma type_of_params_eq
          params ts
          (PARSIGS : list_typ_to_list_type ts = map snd params)
      :
      type_of_params params = list_typ_to_typelist ts.
    Proof.
      revert params PARSIGS. induction ts; ii; ss.
      { destruct params; ss. }
      destruct params; ss. destruct p; ss. clarify. f_equal. auto.
    Qed.

    Lemma match_senv_eventval_match
          (ge0 ge1: Senv.t)
          (MS: match_symbs ge0 ge1)
          ev ty v
          (EM: eventval_match ge0 ev ty v)
      :
      eventval_match ge1 ev ty v.
    Proof. destruct MS as (MS0 & MS1 & MS2). inv EM; try econs; auto. rewrite MS0. auto. Qed.

    Lemma match_senv_eventval_list_match
          (ge0 ge1: Senv.t)
          (MS: match_symbs ge0 ge1)
          evs tys vs
          (EM: eventval_list_match ge0 evs tys vs)
      :
      eventval_list_match ge1 evs tys vs.
    Proof. induction EM; ss. econs; auto. econs; auto. eapply match_senv_eventval_match; eauto. Qed.

    Lemma unbundle_trace_app
          tr1 tr2
      :
      unbundle_trace (tr1 ++ tr2) = (unbundle_trace tr1) ++ (unbundle_trace tr2).
    Proof. induction tr1; ss. rewrite <- app_assoc. f_equal. auto. Qed.

    Lemma cur_fun_def
          ge_i (ge_c: genv) cur f (f_i_cur : Asm.function) id_cur cnts pars ttr
          (FINDF_C_CUR : Genv.find_funct_ptr ge_c cur = Some (Internal f))
          (FINDF_I_CUR : Genv.find_funct_ptr ge_i cur = Some (AST.Internal f_i_cur))
          (INV_CUR : Genv.invert_symbol ge_i cur = Some id_cur)
          (MS3 : match_find_def ge_i ge_c cnts pars ttr)
      :
      exists cnt_cur params_cur,
        (cnts ! id_cur = Some cnt_cur) /\ (pars ! id_cur = Some params_cur) /\
          (f = gen_function ge_i cnt_cur params_cur (get_id_tr ttr id_cur) f_i_cur).
    Proof.
      exploit MS3. eapply Genv.find_funct_ptr_iff. eauto. eapply INV_CUR. intros. des_ifs.
      esplits; eauto. apply Genv.find_funct_ptr_iff in FINDF_C_CUR.
      setoid_rewrite FINDF_C_CUR in x0. unfold gen_globdef in x0. clarify.
    Qed.

    Lemma allowed_call_gen_function
          cp (ge_i: Asm.genv) (ge_c: genv) next cnt params tr f_i f_c
          (GE: symbs_find ge_i ge_c)
          (GEPOL: eq_policy ge_i ge_c)
          (GEN: f_c = gen_function ge_i cnt params tr f_i)
          (ALLOW : Genv.allowed_call ge_i cp (Vptr next Ptrofs.zero))
          (FINDF : Genv.find_funct ge_i (Vptr next Ptrofs.zero) = Some (AST.Internal f_i))
          (FINDF_C : Genv.find_funct ge_c (Vptr next Ptrofs.zero) = Some (Internal f_c))
      :
      Genv.allowed_call ge_c cp (Vptr next Ptrofs.zero).
    Proof.
      unfold Genv.allowed_call in *. des; [left | right].
      - subst. unfold Genv.find_comp. rewrite FINDF, FINDF_C. ss.
      - subst. unfold Genv.allowed_cross_call in *. des.
        unfold eq_policy in GEPOL. rewrite GEPOL in ALLOW2, ALLOW3.
        specialize (ALLOW0 _ FINDF). exists i, cp'. splits; auto.
        { apply Genv.invert_find_symbol in ALLOW. apply Genv.find_invert_symbol.
          apply GE. auto.
        }
        { i. rewrite FINDF_C in H. clarify. }
        { unfold Genv.find_comp in *. rewrite FINDF in ALLOW1. rewrite FINDF_C.
          rewrite <- ALLOW1. ss.
        }
    Qed.

    Lemma eventval_list_match_list_eventval_to_list_val
          (ge: Senv.t) evargs tys vargs
          (EVMS: eventval_list_match ge evargs tys vargs)
      :
      list_eventval_to_list_val ge evargs = vargs.
    Proof.
      induction EVMS; ss. f_equal; auto.
      eapply eventval_match_eventval_to_val. eauto.
    Qed.

    Lemma match_symbs_eventval_match
          ge0 ge1 ev ty v
          (MS: match_symbs ge0 ge1)
          (EVM: eventval_match ge0 ev ty v)
      :
      eventval_match ge1 ev ty v.
    Proof.
      destruct MS as (MS0 & MS1 & MS2). inv EVM; econs; auto. rewrite MS0; auto.
    Qed.

    Lemma match_symbs_eventval_list_match
          ge0 ge1 ev ty v
          (MS: match_symbs ge0 ge1)
          (EVM: eventval_list_match ge0 ev ty v)
      :
      eventval_list_match ge1 ev ty v.
    Proof.
      induction EVM. econs. econs; auto. eapply match_symbs_eventval_match; eauto.
    Qed.

    Lemma alloc_variables_exists
          ge cp e m l
      :
      exists e' m', alloc_variables ge cp e m l e' m'.
    Proof.
      revert ge cp e m. induction l; ii.
      { do 2 eexists. econs 1. }
      destruct a as (id & ty).
      destruct (Mem.alloc m cp 0 (sizeof ge ty)) as (m0 & b0) eqn:ALLOC.
      specialize (IHl ge cp (PTree.set id (b0, ty) e) m0). des.
      do 2 eexists. econs 2. eapply ALLOC. eapply IHl.
    Qed.

    Lemma access_mode_typ_to_type
          s
      :
      exists ch, access_mode (typ_to_type s) = By_value ch.
    Proof. destruct s; ss; eauto. Qed.

    Lemma bind_parameters_exists
          (ge: genv) cp (e: env) m params vargs
          (INENV: Forall (fun '(id, ty) =>
                            exists b, (e ! id = Some (b, ty)) /\
                                   (forall ch, access_mode ty = By_value ch ->
                                          Mem.valid_access m ch b 0 Writable (Some cp)))
                         params)
          sg
          (PARSIGS: list_typ_to_list_type sg = map snd params)
          evargs
          (EMS: eventval_list_match ge evargs sg vargs)
      :
      exists m', bind_parameters ge cp e m params vargs m'.
    Proof.
      revert e m vargs INENV sg PARSIGS evargs EMS. induction params; ii.
      { ss. inv EMS; ss. eexists. econs. }
      destruct a as (id & ty). inv INENV. des. ss.
      destruct sg; ss. rename t into s. clarify. inv EMS.
      destruct (access_mode_typ_to_type s) as (ch & ACCM).
      specialize (H0 _ ACCM). hexploit Mem.valid_access_store. apply H0. instantiate (1:=v1).
      intros (m0 & STORE).
      assert 
        (FA: Forall
               (fun '(id, ty) =>
                  exists b : block,
                    e ! id = Some (b, ty) /\
                      (forall ch : memory_chunk, access_mode ty = By_value ch ->
                                            Mem.valid_access m0 ch b 0 Writable (Some cp))) params).
      { clear - H2 STORE. move H2 before cp. revert_until H2. induction H2; ii; ss.
        econs; eauto. des_ifs. des. esplits; eauto. i. eapply Mem.store_valid_access_1; eauto.
      }
      hexploit IHparams. apply FA. 1,2: eauto. intros. des. exists m'.
      econs; eauto. econs; eauto.
    Qed.

    Lemma alloc_variables_wf_id
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
          (WF: list_norepet (var_names params))
      :
      forall id bt, (~ In id (var_names params)) -> (e ! id = Some bt) -> (e' ! id = Some bt).
    Proof.
      revert WF. induction EA; ii; ss.
      apply Classical_Prop.not_or_and in H0. des. inv WF.
      apply IHEA; auto. rewrite PTree.gso; auto.
    Qed.

    Lemma alloc_variables_valid_access
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
      :
      forall b' ch' ofs' p' cp', Mem.valid_access m ch' b' ofs' p' cp' ->
                            Mem.valid_access m' ch' b' ofs' p' cp'.
    Proof.
      i. assert (WF: (b' < Mem.nextblock m)%positive).
      { unfold Mem.valid_access in H. des. destruct (Unusedglob.IS.MSet.Raw.MX.lt_dec b' (Mem.nextblock m)); auto.
        exfalso. unfold Mem.range_perm in H. specialize (H ofs').
        eapply (Mem.nextblock_noaccess _ _ ofs' Cur) in n.
        exploit H.
        { pose proof (size_chunk_pos ch'). lia. }
        i. unfold Mem.perm in x0. rewrite n in x0. ss.
      }
      revert_until EA. induction EA; ii; ss.
      apply IHEA.
      { eapply Mem.valid_access_alloc_other; eauto. }
      { erewrite Mem.nextblock_alloc; eauto. lia. }
    Qed.

    Lemma alloc_variables_forall
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
          (WF: list_norepet (var_names params))
      :
      Forall (fun '(id, ty) =>
                exists b, (e' ! id = Some (b, ty)) /\
                       (forall ch, access_mode ty = By_value ch ->
                              Mem.valid_access m' ch b 0 Writable (Some cp))) params.
    Proof.
      revert WF. induction EA; ii; ss.
      inv WF. econs; eauto.
      hexploit alloc_variables_wf_id. apply EA. auto. apply H2. apply PTree.gss.
      i. esplits; eauto.
      i. eapply alloc_variables_valid_access. apply EA.
      apply Mem.valid_access_freeable_any. eapply Mem.valid_access_alloc_same; eauto. lia.
      { ss. clear - H1. destruct ty; ss; clarify. des_ifs; clarify; ss. des_ifs; clarify; ss. unfold Mptr. des_ifs. }
      exists 0. ss.
    Qed.

    Lemma assign_loc_valid_access
          ge cp ty m b ofs bit v m'
          (AL: assign_loc ge cp ty m b ofs bit v m')
          ch' b' ofs' perm' cp'
          (VA: Mem.valid_access m ch' b' ofs' perm' (Some cp'))
      :
      Mem.valid_access m' ch' b' ofs' perm' (Some cp').
    Proof.
      inv AL.
      - eapply Mem.store_valid_access_1; eauto.
      - eapply Mem.storebytes_valid_access_1; eauto.
      - inv H. eapply Mem.store_valid_access_1; eauto.
    Qed.

    Lemma bind_parameters_valid_access
          (ge: genv) cp (e: env) m params vargs m'
          (BIND: bind_parameters ge cp e m params vargs m')
          ch b ofs perm cp'
          (VA: Mem.valid_access m ch b ofs perm (Some cp'))
      :
      Mem.valid_access m' ch b ofs perm (Some cp').
    Proof.
      revert_until BIND. induction BIND; ii; ss.
      apply IHBIND. eapply assign_loc_valid_access; eauto.
    Qed.

    Lemma mem_delta_apply_wf_valid_access
          ge cp d m m'
          (APPD: mem_delta_apply_wf ge cp d (Some m) = Some m')
          ch b ofs perm cp'
          (VA: Mem.valid_access m ch b ofs perm cp')
      :
      Mem.valid_access m' ch b ofs perm cp'.
    Proof.
      move d before ge. revert_until d. induction d; ii.
      { unfold mem_delta_apply_wf in APPD. ss; clarify. }
      rewrite mem_delta_apply_wf_cons in APPD. des_ifs.
      - destruct a; ss. hexploit mem_delta_apply_wf_some; eauto.
        intros (m0 & STOREV). rewrite STOREV in APPD.
        eapply IHd. apply APPD.
        unfold mem_delta_apply_storev in STOREV. des_ifs.
        unfold Mem.storev in STOREV. des_ifs.
        eapply Mem.store_valid_access_1; eauto.
      - eapply IHd; eauto.
    Qed.

    Lemma bind_parameters_mem_load
          ge cp e m0 params vargs m1
          (BIND: bind_parameters ge cp e m0 params vargs m1)
      :
      forall ch b ofs cp',
        (forall id b_e ty, (e ! id = Some (b_e, ty) -> b <> b_e)) ->
        (Mem.load ch m1 b ofs cp' = Mem.load ch m0 b ofs cp').
    Proof.
      induction BIND; ii; ss.
      rewrite IHBIND; auto.
      inv H0.
      - eapply Mem.load_store_other. eapply H3. left. ii. clarify. specialize (H1 _ _ _ H). clarify.
      - eapply Mem.load_storebytes_other. eapply H7. left. ii. clarify. specialize (H1 _ _ _ H). clarify.
    Qed.

    Lemma alloc_variables_mem_load
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
      :
      forall ch b ofs cp',
        (b < Mem.nextblock m)%positive ->
        (Mem.load ch m' b ofs cp' = Mem.load ch m b ofs cp').
    Proof.
      induction EA; ii; ss.
      rewrite IHEA.
      { eapply Mem.load_alloc_unchanged; eauto. }
      { erewrite Mem.nextblock_alloc; eauto. lia. }
    Qed.

    Lemma alloc_variables_old_blocks
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
      :
      forall b, (b < Mem.nextblock m)%positive ->
           (forall id b' ty, e ! id = Some (b', ty) -> b <> b') ->
           (forall id b' ty, e' ! id = Some (b', ty) -> b <> b').
    Proof.
      induction EA; i.
      { ii; clarify. specialize (H0 _ _ _ H1). clarify. }
      hexploit Mem.alloc_result; eauto. intros; clarify.
      eapply IHEA. 3: eapply H2.
      { erewrite Mem.nextblock_alloc; eauto. lia. }
      { i. destruct (Pos.eq_dec id id1).
        - clarify. rewrite PTree.gss in H3. clarify. lia.
        - rewrite PTree.gso in H3; auto. eapply H1; eauto.
      }
    Qed.

    Lemma mem_delta_apply_wf_mem_load
          ge cp d m m'
          (APPD: mem_delta_apply_wf ge cp d (Some m) = Some m')
      :
      forall id ch b ofs cp',
        Senv.invert_symbol ge b = Some id ->
        Senv.public_symbol ge id = false ->
        (Mem.load ch m' b ofs cp' = Mem.load ch m b ofs cp').
    Proof.
      move d before ge. revert_until d. induction d; ii.
      { unfold mem_delta_apply_wf in APPD. ss. clarify. }
      rewrite mem_delta_apply_wf_cons in APPD. des_ifs.
      { destruct a; ss. unfold wf_mem_delta_storev_b in Heq. des_ifs. ss.
        hexploit mem_delta_apply_wf_some; eauto. intros (m1 & STORE). rewrite STORE in APPD.
        erewrite IHd. 2: eauto. 2: eauto. all: auto.
        destruct (Pos.eq_dec b b0).
        - clarify.
        - erewrite Mem.load_store_other. 2: eauto. all: auto.
      }
      { eapply IHd; eauto. }
    Qed.

    Lemma nat64_int64_add_one
          n
          (BOUND: Z.of_nat n < Int64.modulus)
      :
      Int64.add (nat64 n) Int64.one = nat64 (n + 1).
    Proof.
      unfold nat64. rewrite Nat2Z.inj_add. ss.
      assert (N: Z.of_nat n = Int64.unsigned (Int64.repr (Z.of_nat n))).
      { symmetry. apply Int64.unsigned_repr. split. apply Zle_0_nat.
        unfold Int64.max_unsigned. lia.
      }
      assert (ONE: 1 = (Int64.unsigned (Int64.repr 1))).
      { ss. }
      rewrite N at 2. rewrite ONE. rewrite <- Int64.add_unsigned. ss.
    Qed.

    Lemma mem_free_list_impl1
          blks m cp m_f
          (FREE: Mem.free_list m blks cp = Some m_f)
      :
      Forall (fun '(b, lo, hi) => (Mem.range_perm m b lo hi Cur Freeable) /\ (Mem.can_access_block m b (Some cp))) blks.
    Proof.
      Local Opaque Mem.can_access_block.
      revert_until blks. induction blks; ii; ss. des_ifs. ss. econs.
      2:{ cut (Forall (fun '(b0, lo, hi) => Mem.range_perm m0 b0 lo hi Cur Freeable /\ Mem.can_access_block m0 b0 (Some cp)) blks); cycle 1.
          { eapply IHblks; eauto. }
          clear - Heq. intros FA. revert_until blks. induction blks; ii; ss.
          destruct a as ((ba & loa) & hia). ss. inv FA. des; clarify. econs.
          {
            clear IHblks. split.
            - unfold Mem.range_perm in *. ii. eapply Mem.perm_free_3. eauto. eauto.
            - eapply Mem.free_can_access_block_inj_2; eauto.
          }
          eapply IHblks; eauto.
      }
      split.
      - eapply Mem.free_range_perm; eauto.
      - eapply Mem.free_can_access_block_1; eauto.
        Local Transparent Mem.can_access_block.
    Qed.

    Lemma mem_free_list_impl2
          blks m cp
          (NR: list_norepet (map (fun x => fst (fst x)) blks))
          (FA: Forall (fun '(b, lo, hi) => (Mem.range_perm m b lo hi Cur Freeable) /\ (Mem.can_access_block m b (Some cp))) blks)
      :
      exists m_f, (Mem.free_list m blks cp = Some m_f).
    Proof.
      Local Opaque Mem.can_access_block.
      revert_until blks. induction blks; ii; ss; eauto.
      inv FA. inv NR. des_ifs; des. 
      2:{ exfalso. destruct (Mem.range_perm_free _ _ _ _ _ H1 H0) as (m0 & FREE). clarify. }
      eapply IHblks; clear IHblks; eauto. ss. clear - H2 H3 Heq.
      revert_until blks. induction blks; ii; ss. inv H2. des_ifs; ss. des. econs; eauto.
      clear IHblks H4. apply Classical_Prop.not_or_and in H3. des. split.
      - unfold Mem.range_perm in *. ii. hexploit Mem.perm_free_inv; eauto. ii. des; clarify.
      - eapply Mem.free_can_access_block_inj_1; eauto.
        Local Transparent Mem.can_access_block.
    Qed.

    Lemma list_map_norepet_rev
          A (l: list A) B (f: A -> B)
          (NR: list_norepet (map f l))
      :
      list_norepet l.
    Proof.
      revert NR. induction l; ii; ss. econs. inv NR. econs; eauto.
      ii. apply H1; clear H1. apply in_map; auto.
    Qed.

    Lemma alloc_variables_wunchanged_on
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
      :
      wunchanged_on (fun b _ => Mem.valid_block m b) m m'.
    Proof.
      induction EA. apply wunchanged_on_refl.
      eapply wunchanged_on_implies in IHEA.
      { eapply wunchanged_on_trans. 2: eauto. eapply alloc_wunchanged_on. eauto. }
      { ii. ss. }
    Qed.

    Lemma alloc_variables_exists_free_list
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
          (ENV1: forall id1 id2 b1 b2 t1 t2, (id1 <> id2) -> (e ! id1 = Some (b1, t1)) -> (e ! id2 = Some (b2, t2)) -> (b1 <> b2))
          (ENV2: forall id b t, (e ! id = Some (b, t)) -> (Mem.valid_block m b))
          m_f0
          (FREE: Mem.free_list m' (blocks_of_env ge e) cp = Some m_f0)
      :
      exists m_f, Mem.free_list m' (blocks_of_env ge e') cp = Some m_f.
    Proof.
      revert_until EA. induction EA; ii; ss; eauto.
      assert (exists m_f0, Mem.free_list m2 (blocks_of_env ge (PTree.set id (b1, ty) e)) cp = Some m_f0); cycle 1.
      { des. eapply IHEA; clear IHEA; eauto.
        - i. destruct (Pos.eqb_spec id id1); clarify.
          + rewrite PTree.gss in H2. rewrite PTree.gso in H3; auto. clarify. specialize (ENV2 _ _ _ H3).
            ii. clarify. apply Mem.fresh_block_alloc in H. clarify.
          + destruct (Pos.eqb_spec id id2); clarify.
            * rewrite PTree.gso in H2; auto. rewrite PTree.gss in H3; auto. clarify. specialize (ENV2 _ _ _ H2).
              ii. clarify. apply Mem.fresh_block_alloc in H. clarify.
            * rewrite PTree.gso in H2, H3; auto. hexploit ENV1. 2: eapply H2. 2: eapply H3. all: auto.
        - i. destruct (Pos.eqb_spec id id0); clarify.
          + rewrite PTree.gss in H1. clarify. eapply Mem.valid_new_block; eauto.
          + rewrite PTree.gso in H1; auto. specialize (ENV2 _ _ _ H1). eapply Mem.valid_block_alloc; eauto.
      }
      clear IHEA. eapply mem_free_list_impl2.
      { unfold blocks_of_env. rewrite map_map. apply list_map_norepet.
        { eapply list_map_norepet_rev. apply PTree.elements_keys_norepet. }
        { i. unfold block_of_binding. des_ifs. ss. apply PTree.elements_complete in H0, H1.
          destruct (Pos.eqb_spec id i); clarify.
          - rewrite PTree.gss in H0. clarify. destruct (Pos.eqb_spec i i0); clarify.
            + rewrite PTree.gss in H1; clarify.
            + rewrite PTree.gso in H1; auto. specialize (ENV2 _ _ _ H1). ii; clarify.
              apply Mem.fresh_block_alloc in H. clarify.
          - rewrite PTree.gso in H0; auto. destruct (Pos.eqb_spec id i0); clarify.
            + rewrite PTree.gss in H1. clarify. specialize (ENV2 _ _ _ H0). ii; clarify.
              apply Mem.fresh_block_alloc in H. clarify.
            + rewrite PTree.gso in H1; auto. eapply ENV1. 2: apply H0. 2: apply H1. ii; clarify.
        }
      }
      { apply mem_free_list_impl1 in FREE. rewrite Forall_forall in *. i.
        assert ((x = (b1, 0%Z, sizeof ge ty)) \/ (In x (blocks_of_env ge e))).
        { clear - H0. unfold blocks_of_env in *. apply list_in_map_inv in H0. des.
          destruct x0 as (xid & xb & xt). apply PTree.elements_complete in H1. clarify.
          destruct (Pos.eqb_spec id xid); clarify.
          - rewrite PTree.gss in H1. clarify. left; auto.
          - rewrite PTree.gso in H1; auto. right. apply in_map. apply PTree.elements_correct. auto.
        }
        des.
        - clarify. split.
          + ii. eapply perm_wunchanged_on. eapply alloc_variables_wunchanged_on; eauto.
            { ss. eapply Mem.valid_new_block; eauto. }
            { eapply Mem.perm_alloc_2; eauto. }
          + rewrite <- wunchanged_on_own. 2: eapply alloc_variables_wunchanged_on; eauto.
            eapply Mem.owned_new_block; eauto. eapply Mem.valid_new_block; eauto.
        - eapply FREE. eauto.
      }
    Qed.

    Lemma assign_loc_wunchanged_on
          ge cp ty m b ofs bit v m'
          (AL: assign_loc ge cp ty m b ofs bit v m')
      :
      wunchanged_on (fun _ _ => True) m m'.
    Proof.
      inv AL.
      - eapply store_wunchanged_on; eauto.
      - eapply storebytes_wunchanged_on; eauto.
      - inv H. eapply store_wunchanged_on; eauto.
    Qed.

    Lemma bind_parameters_wunchanged_on
          (ge: genv) cp (e: env) m params vargs m'
          (BIND: bind_parameters ge cp e m params vargs m')
      :
      wunchanged_on (fun _ _ => True) m m'.
    Proof.
      induction BIND. apply wunchanged_on_refl. eapply wunchanged_on_trans. 2: apply IHBIND.
      eapply assign_loc_wunchanged_on; eauto.
    Qed.

    Lemma wunchanged_on_exists_free
          m m'
          (WU: wunchanged_on (fun b _ => Mem.valid_block m b) m m')
          b lo hi cp m_f
          (FREE: Mem.free m b lo hi cp = Some m_f)
      :
      exists m_f', Mem.free m' b lo hi cp = Some m_f'.
    Proof.
      hexploit Mem.free_range_perm; eauto. hexploit Mem.free_can_access_block_1; eauto. i.
      hexploit Mem.range_perm_free.
      3:{ intros (m0 & F). eexists; eapply F. }
      - unfold Mem.range_perm in *. i. eapply perm_wunchanged_on. 3: eauto. eauto. ss. eapply Mem.perm_valid_block; eauto.
      - rewrite <- wunchanged_on_own; eauto. eapply Mem.can_access_block_valid_block. eauto.
    Qed.

    Lemma assign_loc_perm
          ge cp ty m b ofs bit v m'
          (AL: assign_loc ge cp ty m b ofs bit v m')
          b' o' C P
          (PERM: Mem.perm m b' o' C P)
      :
      Mem.perm m' b' o' C P.
    Proof.
      inv AL.
      - eapply Mem.perm_store_1; eauto.
      - eapply Mem.perm_storebytes_1; eauto.
      - inv H. eapply Mem.perm_store_1; eauto.
    Qed.

    Lemma assign_loc_own
          ge cp ty m b ofs bit v m'
          (AL: assign_loc ge cp ty m b ofs bit v m')
          b' cp'
          (OWN: Mem.can_access_block m b' cp')
      :
      Mem.can_access_block m' b' cp'.
    Proof.
      inv AL.
      - rewrite <- Mem.store_can_access_block_inj; eauto.
      - eapply Mem.storebytes_can_access_block_inj_1; eauto.
      - inv H. rewrite <- Mem.store_can_access_block_inj; eauto.
    Qed.

    Lemma assign_loc_exists_free
          ge cp ty m b ofs bit v m'
          (AL: assign_loc ge cp ty m b ofs bit v m')
          b' lo hi cp' m_f
          (FREE: Mem.free m b' lo hi cp' = Some m_f)
      :
      exists m_f, Mem.free m' b' lo hi cp' = Some m_f.
    Proof.
      hexploit Mem.free_range_perm; eauto. hexploit Mem.free_can_access_block_1; eauto. i.
      hexploit Mem.range_perm_free.
      3:{ intros (m0 & F). eexists; eapply F. }
      - unfold Mem.range_perm in *. i. eapply assign_loc_perm; eauto.
      - eapply assign_loc_own; eauto.
    Qed.

    Lemma wunchanged_on_free_preserves
          m m'
          (WU : wunchanged_on (fun (b : block) (_ : Z) => Mem.valid_block m b) m m')
          b lo hi cp m1 m1'
          (FREE: Mem.free m b lo hi cp = Some m1)
          (FREE': Mem.free m' b lo hi cp = Some m1')
      :
      wunchanged_on (fun (b0 : block) (_ : Z) => Mem.valid_block m1 b0) m1 m1'.
    Proof.
      inv WU. econs.
      - rewrite (Mem.nextblock_free _ _ _ _ _ _ FREE). rewrite (Mem.nextblock_free _ _ _ _ _ _ FREE'). auto.
      - i. assert (VB: Mem.valid_block m b0).
        { eapply Mem.valid_block_free_2; eauto. }
        split; i.
        + pose proof (Mem.perm_free_3 _ _ _ _ _ _ FREE _ _ _ _ H1). rewrite wunchanged_on_perm in H2; auto.
          eapply Mem.perm_free_inv in H2. 2: eauto. des; auto. clarify.
          hexploit Mem.perm_free_2. eapply FREE. split; eauto. i. exfalso. apply H2. eapply H1.
        + pose proof (Mem.perm_free_3 _ _ _ _ _ _ FREE' _ _ _ _ H1). rewrite <- wunchanged_on_perm in H2; auto.
          eapply Mem.perm_free_inv in H2. 2: eauto. des; auto. clarify.
          hexploit Mem.perm_free_2. eapply FREE'. split; eauto. i. exfalso. apply H2. eapply H1.
      - i. assert (VB: Mem.valid_block m b0).
        { eapply Mem.valid_block_free_2; eauto. }
        split; i.
        + eapply Mem.free_can_access_block_inj_1; eauto. apply wunchanged_on_own; auto.
          eapply Mem.free_can_access_block_inj_2; eauto.
        + eapply Mem.free_can_access_block_inj_1; eauto. apply wunchanged_on_own; auto.
          eapply Mem.free_can_access_block_inj_2; eauto.
    Qed.

    Lemma wunchanged_on_exists_mem_free_list
          m m'
          (WU: wunchanged_on (fun b _ => Mem.valid_block m b) m m')
          l cp m_f
          (FREE: Mem.free_list m l cp = Some m_f)
      :
      exists m_f', Mem.free_list m' l cp = Some m_f'.
    Proof.
      move l after m. revert_until l. induction l; ii; ss; eauto. des_ifs.
      2:{ exfalso. hexploit wunchanged_on_exists_free. 2: eapply Heq0. 2: auto.
          2:{ intros. des. rewrite H in Heq; clarify. }
          auto.
      }
      hexploit IHl. 2: eapply FREE.
      { instantiate (1:=m0). eapply wunchanged_on_free_preserves; eauto. }
      eauto.
    Qed.

    Lemma mem_free_list_wunchanged_on
          x m l cp m'
          (FL: Mem.free_list m l cp = Some m')
          (WF: Forall (fun '(b, lo, hi) => (x <= b)%positive) l)
      :
      wunchanged_on (fun b _ => (b < x)%positive) m m'.
    Proof.
      move WF before x. revert_until WF. induction WF; i; ss. clarify. apply wunchanged_on_refl. des_ifs.
      hexploit IHWF; eauto. i. eapply wunchanged_on_trans. 2: eauto.
      eapply free_wunchanged_on; eauto.
      i. lia.
    Qed.

    Lemma wunchanged_on_free_list_preserves
          m m'
          (WU: wunchanged_on (fun b _ => Mem.valid_block m b) m m')
          l cp m_f m_f'
          (FREE: Mem.free_list m l cp = Some m_f)
          (FREE': Mem.free_list m' l cp = Some m_f')
      :
      wunchanged_on (fun b _ => Mem.valid_block m_f b) m_f m_f'.
    Proof.
      move l after m. revert_until l. induction l; ii; ss. clarify.
      des_ifs. eapply IHl. 2,3: eauto. eapply wunchanged_on_free_preserves; eauto.
    Qed.

    Lemma mem_delta_apply_wf_wunchanged_on
          ge cp d m m'
          (APPD: mem_delta_apply_wf ge cp d (Some m) = Some m')
          P
      :
      wunchanged_on P m m'.
    Proof.
      revert_until d. induction d; ii; ss.
      { cbn in APPD. clarify. apply wunchanged_on_refl. }
      rewrite mem_delta_apply_wf_cons in APPD. des_ifs.
      - hexploit mem_delta_apply_wf_some; eauto. intros (m0 & ST). rewrite ST in APPD.
        specialize (IHd _ _ APPD). unfold mem_delta_apply_kind in ST. unfold mem_delta_apply_storev in ST. des_ifs.
        ss. des_ifs. ss. eapply wunchanged_on_trans. eapply store_wunchanged_on. eapply ST.
        eapply wunchanged_on_implies. eapply IHd. ss.
      - eauto.
        Unshelve. all: exact 0%nat.
    Qed.

    Lemma alloc_variables_fresh_blocks
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
          x
          (X: (x <= Mem.nextblock m)%positive)
          (FA: Forall (fun '(b0, _, _) => (x <= b0)%positive) (blocks_of_env ge e))
      :
      Forall (fun '(b0, _, _) => (x <= b0)%positive) (blocks_of_env ge e').
    Proof.
      revert_until EA. induction EA; ii; ss. specialize (IHEA x).
      eapply IHEA; clear IHEA.
      { erewrite Mem.nextblock_alloc; eauto. lia. }
      apply Forall_forall. rewrite Forall_forall in FA. ii. specialize (FA x0). des_ifs.
      unfold blocks_of_env in H0. apply list_in_map_inv in H0. des. destruct x0 as (xid & xb & xt).
      apply PTree.elements_complete in H1. destruct (Pos.eqb_spec id xid); clarify.
      - rewrite PTree.gss in H1. ss. clarify. erewrite Mem.alloc_result. 2: eauto. auto.
      - rewrite PTree.gso in H1; auto. apply FA. rewrite H0. unfold blocks_of_env. apply in_map.
        apply PTree.elements_correct; auto.
    Qed.

    Lemma wf_c_cont_wunchanged_on
          ge m k
          (WFC: wf_c_cont ge m k)
          m'
          (WU: wunchanged_on (fun b _ => Mem.valid_block m b) m m')
      :
      wf_c_cont ge m' k.
    Proof.
      revert_until WFC. induction WFC; ii. econs.
      clarify.
      hexploit wunchanged_on_exists_mem_free_list. eapply WU. eapply FREE. intros (m_f & FREE2).
      econs. 1,2,3: eauto. eapply FREE2. eapply IHWFC.
      eapply wunchanged_on_free_list_preserves. eapply WU. all: eauto.
    Qed.

    Lemma alloc_variables_one_fresh_block
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
          (NR: list_norepet (var_names params))
          xid xb xt
          (NOT: e ! xid = None)
          (GET: e' ! xid = Some (xb, xt))
      :
      ~ (Mem.valid_block m xb).
    Proof.
      revert_until EA. induction EA; i. clarify.
      inv NR. destruct (Pos.eqb_spec xid id).
      { subst id. hexploit alloc_variables_wf_id. eauto. auto. eauto. apply PTree.gss.
        i. rewrite GET in H0. clarify. eapply Mem.fresh_block_alloc; eauto. }
      hexploit IHEA. auto. rewrite PTree.gso. eapply NOT. auto. eapply GET. i.
      ii. apply H0. unfold Mem.valid_block in *. erewrite Mem.nextblock_alloc; eauto.
      etransitivity. eapply H1. apply Plt_succ.
    Qed.

    Lemma assign_loc_outside_mem_inject
          ge cp ty m b ofs bf v m'
          (AL: assign_loc ge cp ty m b ofs bf v m')
          k m0
          (INJ: Mem.inject k m0 m)
          (NIB: k b = None)
          (MS: meminj_same_block k)
      :
      Mem.inject k m0 m'.
    Proof.
      inv AL.
      - eapply Mem.store_outside_inject; eauto. i. specialize (MS _ _ _ H1). clarify.
      - eapply Mem.storebytes_outside_inject; eauto. i. specialize (MS _ _ _ H5). clarify.
      - inv H. eapply Mem.store_outside_inject; eauto. i. specialize (MS _ _ _ H). clarify.
    Qed.

    Lemma bind_parameters_outside_mem_inject
          ge cp e m_cur params vargs m_next
          (BIND: bind_parameters ge cp e m_cur params vargs m_next)
          k m
          (INJ: Mem.inject k m m_cur)
          (NIB: forall id b t, e ! id = Some (b, t) -> k b = None)
          (MS: meminj_same_block k)
      (* (NIB: not_inj_blks k (blocks_of_env2 ge e)) *)
      :
      Mem.inject k m m_next.
    Proof.
      revert_until BIND. induction BIND; ii.
      { auto. }
      apply IHBIND; auto. clear IHBIND. specialize (NIB _ _ _ H).
      eapply assign_loc_outside_mem_inject; eauto.
    Qed.

    Lemma not_inj_blks_get_env
          k ge e
          (NIB: not_inj_blks k (blocks_of_env2 ge e))
      :
      forall id b t, e ! id = Some (b, t) -> k b = None.
    Proof.
      rr in NIB. unfold blocks_of_env2, blocks_of_env in NIB. rewrite map_map in NIB.
      rewrite Forall_forall in NIB. i. apply PTree.elements_correct in H.
      apply NIB. eapply (in_map (fun x : ident * (block * type) => fst (fst (block_of_binding ge x)))) in H. ss.
    Qed.

    Lemma not_global_blks_get_env
          (ge: genv) e
          (NIB: not_global_blks ge (blocks_of_env2 ge e))
      :
      forall id b t, e ! id = Some (b, t) -> (meminj_public ge) b = None.
    Proof. eapply not_inj_blks_get_env. eapply not_global_is_not_inj_bloks. eauto. Qed.

    Lemma meminj_public_same_block
          ge
      :
      meminj_same_block (meminj_public ge).
    Proof. rr. unfold meminj_public. i. des_ifs. Qed.

    Lemma alloc_variables_mem_inject
          ge cp e m params e' m'
          (EA: alloc_variables ge cp e m params e' m')
          k m0
          (INJ: Mem.inject k m0 m)
      :
      Mem.inject k m0 m'.
    Proof.
      revert_until EA. induction EA; ii. auto.
      apply IHEA. clear IHEA. eapply Mem.alloc_right_inject; eauto.
    Qed.

    Lemma mem_valid_access_wunchanged_on
          m ch b ofs p cp
          (MV: Mem.valid_access m ch b ofs p cp)
          P m'
          (WU: wunchanged_on P m m')
          (SAT: forall ofs', P b ofs')
      :
      Mem.valid_access m' ch b ofs p cp.
    Proof.
      unfold Mem.valid_access in *. des. splits; auto.
      - unfold Mem.range_perm in *. i. eapply perm_wunchanged_on; eauto.
      - destruct cp. 2: ss. erewrite <- wunchanged_on_own; eauto. eapply Mem.can_access_block_valid_block; eauto.
    Qed.

    Lemma mem_free_list_wunchanged_on_2
          l m cp m'
          (FREE: Mem.free_list m l cp = Some m')
      :
      wunchanged_on (fun b _ => ~ In b (map (fun x => fst (fst x)) l)) m m'.
    Proof.
      revert_until l. induction l; ii.
      { ss. clarify. apply wunchanged_on_refl. }
      ss. des_ifs. eapply wunchanged_on_trans; cycle 1.
      { eapply wunchanged_on_implies. eapply IHl. eauto. ss. i. apply Classical_Prop.not_or_and in H. des. auto. }
      ss. eapply free_wunchanged_on. eapply Heq. ii. apply H0; clear H0. left; auto.
    Qed.

    Lemma not_global_blks_global_not_in
          (ge: genv) id b
          (FIND: Genv.find_symbol ge id = Some b)
          e
          (NGB: not_global_blks ge (blocks_of_env2 ge e))
      :
      ~ In b (map (fun x : block * Z * Z => fst (fst x)) (blocks_of_env ge e)).
    Proof.
      intros CONTRA. unfold not_global_blks in NGB. unfold blocks_of_env2, blocks_of_env in *.
      rewrite map_map in NGB, CONTRA. rewrite Forall_forall in NGB. specialize (NGB _ CONTRA).
      apply Genv.find_invert_symbol in FIND. setoid_rewrite FIND in NGB. inv NGB.
    Qed.

    Lemma mem_free_list_unchanged_on
          l m cp m'
          (FREE: Mem.free_list m l cp = Some m')
      :
      Mem.unchanged_on (fun b _ => ~ In b (map (fun x => fst (fst x)) l)) m m'.
    Proof.
      revert_until l. induction l; ii.
      { ss. clarify. apply Mem.unchanged_on_refl. }
      ss. des_ifs. eapply Mem.unchanged_on_trans; cycle 1.
      { eapply Mem.unchanged_on_implies. eapply IHl. eauto. ss. i. apply Classical_Prop.not_or_and in H. des. auto. }
      ss. eapply Mem.free_unchanged_on. eapply Heq. ii. apply H0; clear H0. left; auto.
    Qed.

    Lemma mem_inject_incr_match_cnts_rev
          k1 k2
          (INCR: inject_incr k1 k2)
          cnts ge
          (MC: match_cnts cnts ge k2)
      :
      match_cnts cnts ge k1.
    Proof.
      unfold match_cnts in *. i. specialize (MC _ _ _ H H0 b ofs). ii. apply MC; clear MC. apply INCR. auto.
    Qed.

    Lemma star_cut_middle
          stepk ge_c cst1 ev pretr ttr cnts ge_i pars ist2
          (CUT: exists tr1 cst',
              (star stepk ge_c cst1 tr1 cst') /\
                exists tr2 cst2,
                  (star stepk ge_c cst' tr2 cst2) /\
                    ((exists id', (wf_c_state ge_c (pretr ++ [ev]) ttr cnts id' cst2) /\
                               exists k, (match_state ge_i ge_c k ttr cnts pars id' ist2 cst2))
                     \/ (ist2 = None)) /\
                    (unbundle ev = tr1 ++ tr2))
      :
      exists cst2, (star stepk ge_c cst1 (unbundle ev) cst2) /\
                ((exists id', (wf_c_state ge_c (pretr ++ [ev]) ttr cnts id' cst2) /\
                           exists k, (match_state ge_i ge_c k ttr cnts pars id' ist2 cst2))
                 \/ (ist2 = None)).
    Proof.
      destruct CUT as (tr1 & cts' & STAR1 & tr2 & cst2 & STAR2 & PROP & TR).
      exists cst2. split; auto. eapply star_trans. eapply STAR1. eapply STAR2. auto.
    Qed.

    Lemma exists_vargs_vres
          (ge1: Senv.t) (ge2: genv)
          (MS: match_symbs ge1 ge2)
          ef m1 vargs tr vretv m2
          (EK: external_call_known_observables ef ge1 m1 vargs tr vretv m2)
          e cp le m_c
          (WFE: wf_env ge2 e)
      :
      exists vargs2 vretv2,
        (eval_exprlist ge2 e cp le m_c (list_eventval_to_list_expr (vals_to_eventvals ge1 vargs))
                       (list_typ_to_typelist (sig_args (ef_sig ef))) vargs2) /\
          (external_call ef ge2 vargs2 m_c tr vretv2 m_c).
    Proof.
      pose proof MS as MS0. destruct MS as (MS1 & MS2 & MS3). move MS0 after MS1.
      unfold external_call_known_observables in *. des_ifs; ss; des. all: try (inv EK; clarify; ss).
      - inv H; clarify. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol; eauto. intros INV. rewrite INV.
        esplits.
        + econs. 3: econs. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. apply sem_cast_ptr.
        + econs. econs; auto. rewrite MS3; auto. eapply match_symbs_eventval_match; eauto.
      - inv H; clarify. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol; eauto. intros INV. rewrite INV.
        esplits.
        + econs. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. apply sem_cast_ptr.
          econs. 3: econs.
          { instantiate (1:=v). destruct v; ss; try (econs; fail).
            - destruct chunk; ss; inv H2; ss.
            - destruct Archi.ptr64 eqn:ARCH.
              + destruct chunk; ss; inv H2; ss; des_ifs.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H7. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
              + destruct chunk; ss; inv H2; ss; des_ifs.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H7. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
          }
          { instantiate (1:=Val.load_result chunk v). rewrite EK1 in H2. rewrite EK1.
            destruct v; ss.
            - destruct chunk; ss; inv H2; ss.
            - destruct chunk; ss. all: simpl_expr. inv H2.
            - destruct chunk; ss. all: simpl_expr.
            - destruct chunk; ss. inv H2.
            - destruct chunk; ss. all: inv H2.
            - inv H2. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. apply H7. intros INV2. rewrite INV2.
              rewrite ptr_of_id_ofs_typeof. unfold Tptr. des_ifs; ss; simpl_expr.
              + unfold Cop.sem_cast. ss. rewrite Heq. auto.
              + unfold Cop.sem_cast. ss. rewrite Heq. auto.
          }
        + econs. econs; auto. rewrite MS3; auto. rewrite EK1. eapply match_symbs_eventval_match; eauto.
      - esplits.
        + erewrite eventval_list_match_vals_to_eventvals. 2: eapply H.
          eapply list_eventval_to_expr_val_eval; auto. eapply eventval_list_match_transl.
          eapply match_senv_eventval_list_match; eauto.
        + econs. eapply eventval_list_match_transl_val. eapply match_senv_eventval_list_match; eauto.
      - esplits.
        + econs. 3: econs.
          * erewrite eventval_match_val_to_eventval. 2: eapply H. eapply eventval_to_expr_val_eval; auto.
            eapply match_senv_eventval_match; eauto.
          * erewrite eventval_match_val_to_eventval. 2: eapply H. eapply eventval_match_sem_cast.
            erewrite eventval_match_eventval_to_val.
            eapply match_senv_eventval_match. eauto. eapply H. eapply match_senv_eventval_match. eauto. eapply H.
        + econs. erewrite eventval_match_eventval_to_val.
          eapply match_senv_eventval_match. eauto. eapply H. eapply match_senv_eventval_match. eauto. eapply H.
    Qed.

    Lemma eventval_list_match_eval_exprlist
          (ge: genv) args targs vargs
          (EMS: eventval_list_match ge args targs vargs)
          e cp le m
          (WF: wf_env ge e)
      :
      eval_exprlist ge e cp le m (list_eventval_to_list_expr args)
                    (list_eventval_to_typelist args) vargs.
    Proof.
      revert_until EMS. induction EMS; i; ss. econs.
      econs; auto.
      { clear dependent evl. clear tyl vl. inv H; try (simpl_expr; fail).
        ss. eapply ptr_of_id_ofs_eval; auto.
      }
      { clear dependent evl. clear tyl vl. inv H; ss; try (simpl_expr; fail).
        rewrite ptr_of_id_ofs_typeof. ss.
      }
    Qed.

    Lemma exists_vargs_vres_2
          (ge1: Senv.t) (ge2: genv)
          (MS: match_symbs ge1 ge2)
          ef m1 vargs tr vretv m2
          (EK: external_call_known_observables ef ge1 m1 vargs tr vretv m2)
          e cp le m_c
          (WFE: wf_env ge2 e)
      :
      exists vargs2 vretv2,
        (eval_exprlist ge2 e cp le m_c (list_eventval_to_list_expr (vals_to_eventvals ge1 vargs))
                       (list_eventval_to_typelist (vals_to_eventvals ge1 vargs)) vargs2) /\
          (external_call ef ge2 vargs2 m_c tr vretv2 m_c).
    Proof.
      pose proof MS as MS0. destruct MS as (MS1 & MS2 & MS3). move MS0 after MS1.
      unfold external_call_known_observables in *. des_ifs; ss; des. all: try (inv EK; clarify; ss).
      - inv H; clarify. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol; eauto. intros INV. rewrite INV.
        esplits.
        + econs. 3: econs. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. simpl_expr.
        + econs. econs; auto. rewrite MS3; auto. eapply match_symbs_eventval_match; eauto.
      - inv H; clarify. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol; eauto. intros INV. rewrite INV.
        esplits.
        + econs. eapply ptr_of_id_ofs_eval; eauto. rewrite ptr_of_id_ofs_typeof. simpl_expr.
          econs. 3: econs.
          { instantiate (1:=v). destruct v; ss; try (econs; fail).
            - destruct chunk; ss; inv H2; ss.
            - destruct Archi.ptr64 eqn:ARCH.
              + destruct chunk; ss; inv H2; ss; des_ifs.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H7. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
              + destruct chunk; ss; inv H2; ss; des_ifs.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H6. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
                * unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. eapply H7. intros INV2. rewrite INV2.
                  eapply ptr_of_id_ofs_eval; eauto.
          }
          { instantiate (1:=Val.load_result chunk v). rewrite EK1 in H2. rewrite EK1.
            destruct v; ss.
            - destruct chunk; ss; inv H2; ss.
            - destruct chunk; ss. all: simpl_expr.
            - destruct chunk; ss. all: simpl_expr.
            - inv H2. unfold senv_invert_symbol_total. hexploit Senv.find_invert_symbol. apply H7. intros INV2. rewrite INV2.
              rewrite ptr_of_id_ofs_typeof. simpl_expr.
          }
        + econs. econs; auto. rewrite MS3; auto. rewrite EK1. eapply match_symbs_eventval_match; eauto.
      - esplits.
        + erewrite eventval_list_match_vals_to_eventvals. 2: eapply H.
          eapply eventval_list_match_eval_exprlist; eauto.
          eapply match_senv_eventval_list_match; eauto.
        + econs. eapply match_senv_eventval_list_match; eauto.
      - esplits.
        + econs. 3: econs.
          * erewrite eventval_match_val_to_eventval. 2: eapply H. eapply eventval_to_expr_val_eval; auto.
            eapply match_senv_eventval_match; eauto.
          * inv H; ss; try (simpl_expr; fail). apply MS2 in H1. setoid_rewrite H1.
            rewrite ptr_of_id_ofs_typeof. ss.
        + econs. eapply match_senv_eventval_match; eauto.
    Qed.

    Lemma known_obs_preserves_mem
          ef ge m vargs tr vretv m'
          (EK: external_call_known_observables ef ge m vargs tr vretv m')
      :
      m' = m.
    Proof.
      unfold external_call_known_observables in EK. des_ifs; des; inv EK; clarify. inv H; clarify.
    Qed.

    Lemma meminj_first_order_public_first_order
          ge m
          (MFO: meminj_first_order (meminj_public ge) m)
      :
      public_first_order ge m.
    Proof.
      ii. apply MFO; auto. unfold meminj_public. apply Senv.find_invert_symbol in FIND.
      rewrite FIND. rewrite PUBLIC. ss.
    Qed.

    Lemma vals_public_eval_to_vargs
          (ge: genv) ef vargs
          (VP: vals_public ge (sig_args (ef_sig ef)) vargs)
          e cp le m
          (WFE: wf_env ge e)
      :
      eval_exprlist ge e cp le m
                    (list_eventval_to_list_expr (vals_to_eventvals ge vargs))
                    (list_typ_to_typelist (sig_args (ef_sig ef))) vargs.
    Proof.
      induction VP. ss. econs. ss. rename x into ty, y into v. econs. 3: auto.
      - clear dependent l. clear dependent l'.
        inv H; ss; try (simpl_expr; fail).
        destruct H0 as (id & BP1 & BP2).
        unfold senv_invert_symbol_total. rewrite BP1.
        apply ptr_of_id_ofs_eval; auto. apply Senv.invert_find_symbol; auto.
      - clear dependent l. clear dependent l'.
        inv H; ss; try (simpl_expr; fail).
        destruct H0 as (id & BP1 & BP2).
        unfold senv_invert_symbol_total. rewrite BP1.
        rewrite ptr_of_id_ofs_typeof. unfold Tptr. des_ifs; ss.
        + unfold Cop.sem_cast. ss. rewrite Heq. ss.
        + unfold Cop.sem_cast. ss. rewrite Heq. ss.
    Qed.

    Lemma vals_public_eval_to_vargs_2
          (ge: genv) ef vargs
          (VP: vals_public ge (sig_args (ef_sig ef)) vargs)
          e cp le m
          (WFE: wf_env ge e)
      :
      eval_exprlist ge e cp le m
                    (list_eventval_to_list_expr (vals_to_eventvals ge vargs))
                    (list_eventval_to_typelist (vals_to_eventvals ge vargs)) vargs.
    Proof.
      induction VP. ss. econs. ss. rename x into ty, y into v. econs. 3: auto.
      - clear dependent l. clear dependent l'.
        inv H; ss; try (simpl_expr; fail).
        destruct H0 as (id & BP1 & BP2).
        unfold senv_invert_symbol_total. rewrite BP1.
        apply ptr_of_id_ofs_eval; auto. apply Senv.invert_find_symbol; auto.
      - clear dependent l. clear dependent l'.
        inv H; ss; try (simpl_expr; fail).
        destruct H0 as (id & BP1 & BP2).
        unfold senv_invert_symbol_total. rewrite BP1.
        rewrite ptr_of_id_ofs_typeof. ss.
    Qed.

    Lemma match_symbs_block_public
          ge1 ge2
          (MS: match_symbs ge1 ge2)
          b
          (BP: block_public ge1 b)
      :
      block_public ge2 b.
    Proof.
      destruct MS as (MS1 & MS2 & MS3). destruct BP as (id & BP1 & BP2).
      apply Senv.invert_find_symbol in BP1. apply MS2 in BP1. rewrite <- MS1 in BP2.
      unfold block_public. esplits; eauto. apply Senv.find_invert_symbol; auto.
    Qed.

    Lemma match_symbs_vals_public
          ge1 ge2
          (MS: match_symbs ge1 ge2)
          tys vargs
          (VP: vals_public ge1 tys vargs)
      :
      vals_public ge2 tys vargs.
    Proof.
      induction VP; ss. econs; auto. clear VP IHVP. inv H; econs; auto.
      eapply match_symbs_block_public; eauto.
    Qed.

    Lemma match_symbs_vals_public_vals_to_eventvals
          ge1 ge2
          (MS: match_symbs ge1 ge2)
          tys vargs
          (VP: vals_public ge1 tys vargs)
      :
      vals_to_eventvals ge1 vargs = vals_to_eventvals ge2 vargs.
    Proof.
      induction VP; ss. f_equal; auto. clear dependent l. clear dependent l'.
      inv H; ss. destruct H0 as (id & BP1 & BP2).
      unfold senv_invert_symbol_total at 1. des_ifs.
      destruct MS as (MS0 & MS1 & MS2).
      apply Senv.invert_find_symbol in Heq. apply MS1 in Heq.
      unfold senv_invert_symbol_total at 1. apply Senv.find_invert_symbol in Heq.
      rewrite Heq. auto.
    Qed.

    Lemma match_symbs_vals_public_eval_to_vargs
          ge1 (ge2: genv)
          (MS: match_symbs ge1 ge2)
          ef vargs
          (VP: vals_public ge1 (sig_args (ef_sig ef)) vargs)
          e cp le m
          (WFE: wf_env ge2 e)
      :
      eval_exprlist ge2 e cp le m
                    (list_eventval_to_list_expr (vals_to_eventvals ge1 vargs))
                    (list_typ_to_typelist (sig_args (ef_sig ef))) vargs.
    Proof.
      erewrite match_symbs_vals_public_vals_to_eventvals; eauto.
      eapply vals_public_eval_to_vargs; auto. eapply match_symbs_vals_public; eauto.
    Qed.

    Lemma match_symbs_vals_public_eval_to_vargs_2
          ge1 (ge2: genv)
          (MS: match_symbs ge1 ge2)
          ef vargs
          (VP: vals_public ge1 (sig_args (ef_sig ef)) vargs)
          e cp le m
          (WFE: wf_env ge2 e)
      :
      eval_exprlist ge2 e cp le m
                    (list_eventval_to_list_expr (vals_to_eventvals ge1 vargs))
                    (list_eventval_to_typelist (vals_to_eventvals ge1 vargs)) vargs.
    Proof.
      erewrite match_symbs_vals_public_vals_to_eventvals; eauto.
      eapply vals_public_eval_to_vargs_2; auto. eapply match_symbs_vals_public; eauto.
    Qed.

    Lemma extcall_unkowns_vals_public
          ef ge m vargs
          (EC: external_call_unknowns ef ge m vargs)
      :
      vals_public ge (sig_args (ef_sig ef)) vargs.
    Proof.
      unfold external_call_unknowns in EC. des_ifs; ss; auto.
      all: destruct EC as (EC1 & EC2); auto.
    Qed.


    Lemma mem_unchanged_wunchanged
          P m m'
          (UCH: Mem.unchanged_on P m m')
      :
      wunchanged_on P m m'.
    Proof. inv UCH. econs; eauto. Qed.

    Lemma meminj_public_not_public_not_mapped
          ge cnt_cur
          (NP: Senv.public_symbol ge cnt_cur = false)
          cnt_cur_b
          (FIND: Senv.find_symbol ge cnt_cur = Some cnt_cur_b)
      :
      forall b ofs, meminj_public ge b <> Some (cnt_cur_b, ofs).
    Proof.
      ii. unfold meminj_public in H. des_ifs.
      assert (i = cnt_cur).
      { eapply Senv.find_symbol_injective; eauto. apply Senv.invert_find_symbol; auto. }
      subst i. rewrite NP in Heq0. ss.
    Qed.


    Lemma wunchanged_on_exists_mem_free_gen
          m1 b lo hi cp m2
          (FREE: Mem.free m1 b lo hi cp = Some m2)
          (P: block -> Prop) m_c
          (WCH: wunchanged_on (fun b _ => P b) m1 m_c)
          (NGB: P b)
      :
      exists m_c', Mem.free m_c b lo hi cp = Some m_c'.
    Proof.
      hexploit Mem.free_range_perm; eauto. hexploit Mem.free_can_access_block_1; eauto. i.
      hexploit Mem.range_perm_free.
      3:{ intros (m0 & F). eexists; eapply F. }
      - unfold Mem.range_perm in *. i. eapply perm_wunchanged_on. 3: eauto. eauto. ss.
      - rewrite <- wunchanged_on_own; eauto. eapply Mem.can_access_block_valid_block. eauto.
    Qed.

    Lemma wunchanged_on_exists_mem_free_2
          m1 b lo hi cp m2
          (FREE: Mem.free m1 b lo hi cp = Some m2)
          ge m_c
          (WCH: wunchanged_on (fun b _ => Senv.invert_symbol ge b = None) m1 m_c)
          (NGB: Senv.invert_symbol ge b = None)
      :
      exists m_c', Mem.free m_c b lo hi cp = Some m_c'.
    Proof. eapply wunchanged_on_exists_mem_free_gen; eauto. eapply WCH. ss. Qed.

    Lemma wunchanged_on_free_preserves_gen
          P m m'
          (WU : wunchanged_on P m m')
          b lo hi cp m1 m1'
          (FREE: Mem.free m b lo hi cp = Some m1)
          (FREE': Mem.free m' b lo hi cp = Some m1')
      :
      wunchanged_on P m1 m1'.
    Proof.
      inv WU. econs.
      - rewrite (Mem.nextblock_free _ _ _ _ _ _ FREE). rewrite (Mem.nextblock_free _ _ _ _ _ _ FREE'). auto.
      - i. assert (VB: Mem.valid_block m b0).
        { eapply Mem.valid_block_free_2; eauto. }
        split; i.
        + pose proof (Mem.perm_free_3 _ _ _ _ _ _ FREE _ _ _ _ H1). rewrite wunchanged_on_perm in H2; auto.
          eapply Mem.perm_free_inv in H2. 2: eauto. des; auto. clarify.
          hexploit Mem.perm_free_2. eapply FREE. split; eauto. i. exfalso. apply H2. eapply H1.
        + pose proof (Mem.perm_free_3 _ _ _ _ _ _ FREE' _ _ _ _ H1). rewrite <- wunchanged_on_perm in H2; auto.
          eapply Mem.perm_free_inv in H2. 2: eauto. des; auto. clarify.
          hexploit Mem.perm_free_2. eapply FREE'. split; eauto. i. exfalso. apply H2. eapply H1.
      - i. assert (VB: Mem.valid_block m b0).
        { eapply Mem.valid_block_free_2; eauto. }
        split; i.
        + eapply Mem.free_can_access_block_inj_1; eauto. apply wunchanged_on_own; auto.
          eapply Mem.free_can_access_block_inj_2; eauto.
        + eapply Mem.free_can_access_block_inj_1; eauto. apply wunchanged_on_own; auto.
          eapply Mem.free_can_access_block_inj_2; eauto.
    Qed.

    Lemma wunchanged_on_exists_mem_free_list_gen
          l m1 cp m2
          (FREE: Mem.free_list m1 l cp = Some m2)
          (P: block -> Prop) m_c
          (WCH: wunchanged_on (fun b _ => P b) m1 m_c)
          (NGB: Forall P (map (fun x => fst (fst x)) l))
      :
      exists m_c', Mem.free_list m_c l cp = Some m_c'.
    Proof.
      revert_until l. induction l; i; ss. eauto.
      destruct a as ((b & lo) & hi). ss. inv NGB. des_ifs; ss.
      2:{ exfalso. hexploit wunchanged_on_exists_mem_free_gen. 2: eapply WCH. all: eauto.
          intros. des. rewrite H in Heq; clarify.
      }
      hexploit IHl. eapply FREE. 2: eapply H2.
      { instantiate (1:=m). eapply wunchanged_on_free_preserves_gen; eauto. }
      eauto.
    Qed.

    Lemma wunchanged_on_exists_mem_free_list_2
          l m1 cp m2
          (FREE: Mem.free_list m1 l cp = Some m2)
          ge m_c
          (WCH: wunchanged_on (fun b _ => Senv.invert_symbol ge b = None) m1 m_c)
          (NGB: not_global_blks ge (map (fun x => fst (fst x)) l))
      :
      exists m_c', Mem.free_list m_c l cp = Some m_c'.
    Proof. eapply wunchanged_on_exists_mem_free_list_gen; eauto. ss. Qed.

    Lemma wunchanged_on_free_list_preserves_gen
          P m m'
          (WU: wunchanged_on P m m')
          l cp m_f m_f'
          (FREE: Mem.free_list m l cp = Some m_f)
          (FREE': Mem.free_list m' l cp = Some m_f')
      :
      wunchanged_on P m_f m_f'.
    Proof.
      move l after m. revert_until l. induction l; ii; ss. clarify.
      des_ifs. eapply IHl. 2,3: eauto. eapply wunchanged_on_free_preserves_gen; eauto.
    Qed.

    Lemma wf_c_cont_wunchanged_on_2
          ge m k
          (WF: wf_c_cont ge m k)
          m'
          (WCH: wunchanged_on (fun b _ => Senv.invert_symbol ge b = None) m m')
      :
      wf_c_cont ge m' k.
    Proof.
      revert_until WF. induction WF; i; ss. econs.
      clarify. hexploit wunchanged_on_exists_mem_free_list_2.
      eapply FREE. instantiate (2:=ge). eapply WCH. auto.
      intros (m_c' & FREE2).
      econs. eauto. auto. eauto. eapply FREE2. eapply IHWF.
      eapply wunchanged_on_free_list_preserves_gen. 2,3: eauto. auto.
    Qed.

    Lemma wf_c_nb_wunchanged_on
          P m1 m2
          (WCH: wunchanged_on P m1 m2)
          ge
          (WFNB: wf_c_nb ge m1)
      :
      wf_c_nb ge m2.
    Proof.
      unfold wf_c_nb in *. hexploit wunchanged_on_nextblock. eapply WCH.
      intros. etransitivity. eapply WFNB. auto.
    Qed.

    Lemma meminj_not_alloc_external_call
          j m1
          (NA: meminj_not_alloc j m1)
          ef ge vargs tr vretv m2
          (EC: external_call ef ge vargs m1 tr vretv m2)
      :
      meminj_not_alloc j m2.
    Proof.
      unfold meminj_not_alloc in *. i. apply NA. clear NA.
      eapply external_call_nextblock in EC. etransitivity. 2: eapply H. auto.
    Qed.


    Lemma ir_to_clight_step_cce_1
          (ge_i: Asm.genv) (ge_c: genv)
          (WFGE : wf_ge ge_i)
          cnts pars k_i cur m_i pretr btr (tr : trace) id0 evargs ef id_cur d
          (BOUND : Z.of_nat
                     (Datatypes.length
                        (pretr ++ (id_cur, Bundle_call tr id0 evargs (ef_sig ef) d) :: btr)) <
                     Int64.modulus)
          k_c id f stmt k0 e le m_c
          (MS0 : match_genv ge_i ge_c)
          (MS1 : match_mem ge_i k_c m_i m_c)
          (MS2 : match_cur_fun ge_i ge_c cur f id)
          (MS4 : match_cont ge_c (pretr ++ (id_cur, Bundle_call tr id0 evargs (ef_sig ef) d) :: btr) cnts
                            k0 k_i)
          (MS3 : match_find_def ge_i ge_c cnts pars
                                (pretr ++ (id_cur, Bundle_call tr id0 evargs (ef_sig ef) d) :: btr))
          (MS5 : match_params pars ge_c ge_i)
          (MCNTS : match_cnts cnts ge_c k_c)
          (CNT_INJ : forall (id0 id1 : positive) (cnt : ident),
              cnts ! id0 = Some cnt -> cnts ! id1 = Some cnt -> id0 = id1)
          (WFC0 : forall (id : ident) (b : block) (f : function),
              Genv.find_symbol ge_c id = Some b ->
              Genv.find_funct_ptr ge_c b = Some (Internal f) ->
              exists cnt : ident,
                cnts ! id = Some cnt /\
                  wf_counter ge_c m_c (comp_of f) (Datatypes.length (get_id_tr pretr id)) cnt)
          m_freeenv
          (FREEENV : Mem.free_list m_c (blocks_of_env ge_c e) (comp_of f) = Some m_freeenv)
          (WFC1 : wf_c_cont ge_c m_freeenv k0)
          (WFC2 : wf_c_stmt ge_c (comp_of f) cnts id
                            (pretr ++ (id_cur, Bundle_call tr id0 evargs (ef_sig ef) d) :: btr) stmt)
          (WFC3 : wf_env ge_c e)
          (WFC4 : not_global_blks ge_c (blocks_of_env2 ge_c e))
          (WFNB : wf_c_nb ge_c m_c)
          vargs b
          (FINDB : Genv.find_symbol ge_i id0 = Some b)
          (FINDF : Genv.find_funct ge_i (Vptr b Ptrofs.zero) = Some (AST.External ef))
          (NPTR : crossing_comp ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) (comp_of ef) ->
                  Forall not_ptr vargs)
          (ALLOW : Genv.allowed_call ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))
                                     (Vptr b Ptrofs.zero))
          (TR : call_trace_cross ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) 
                                 (comp_of ef) b vargs (sig_args (ef_sig ef)) tr id0 evargs)
          (IDCUR : Genv.invert_symbol ge_i cur = Some id_cur)
          m2
          (DELTA: mem_delta_apply_wf ge_i (Genv.find_comp ge_i (Vptr cur Ptrofs.zero)) d (Some m_i) = Some m2)
          (DELTA_CASES: (public_first_order ge_i m2) \/ (d = []))
      :
      exists cnt_cur cnt_cur_b,
        (cnts ! id_cur = Some cnt_cur /\ Senv.find_symbol ge_c cnt_cur = Some cnt_cur_b) /\
          let dsg := from_sig_fun_data (ef_sig ef) in
          let fd_next := (External ef (dargs dsg) (dret dsg) (dcc dsg)) in
          exists m_c',
            (star step1 ge_c (State f stmt k0 e le m_c)
                  (unbundle (id_cur, Bundle_call tr id0 evargs (ef_sig ef) d))
                  (Callstate fd_next vargs
                             (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr (pretr ++ (id_cur, Bundle_call tr id0 evargs (ef_sig ef) d) :: btr) id_cur))) Sskip k0)) m_c'))
            /\
              (exists m_cu,
                  (Mem.storev Mint64 m_c (Vptr cnt_cur_b Ptrofs.zero) (Vlong (Int64.add (nat64 (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr pretr id_cur)))) Int64.one)) (comp_of f) = Some m_cu) /\
                    (d = [] -> m_c' = m_cu) /\
                    ((public_first_order ge_i m2) ->
                     (mem_delta_apply_wf ge_i (comp_of f) d (Some m_cu) = Some m_c') /\
                       (Mem.inject (meminj_public ge_i) m2 m_c')))
    .
    Proof.
      assert (id = id_cur).
      { unfold match_cur_fun in MS2. desH MS2. rewrite MS7 in IDCUR. clarify. }
      subst id.

      exploit MS3.
      { eapply Genv.find_funct_ptr_iff. erewrite <- Genv.find_funct_find_funct_ptr. eapply FINDF. }
      { eapply Genv.find_invert_symbol; eauto. }
      intros FINDF_C. des_ifs. rename id0 into id_next, i into cnt_next, Heq into CNTS_NEXT, l into params_next, Heq0 into PARS_NEXT. simpl in FINDF_C.
      set (pretr ++ (id_cur, Bundle_call tr id_next evargs (ef_sig ef) d) :: btr) as ttr in *.
      assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
      { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.invert_find_symbol in IDCUR. apply MSENV1 in IDCUR. auto. }
      assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
      { destruct MS2 as (MFUN0 & MFUN1). auto. }

      exploit WFC0. eapply FIND_CUR_C. eapply FIND_FUN_C. intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
      destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).
      exists cnt_cur, cnt_cur_b. split. auto.
      set (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)) as kc_next.
      assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_call tr id_next evargs (ef_sig ef) d) :: (get_id_tr btr id_cur)).
      { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
      assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
      { rewrite map_length. etransitivity. 2: eauto. unfold get_id_tr. admit. (* ez *) }

      destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).
      hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply INV_CUR. eauto.
      intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
      rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
      assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
      { unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss. }

      hexploit switch_spec.
      { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
      { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3. }
      eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
      { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
      instantiate (1:=le).
      instantiate (1:=(Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)).
      instantiate (1:=Sreturn None).
      intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).

      TODO
      assert (DELTA_C: exists m_c',
                 (mem_delta_apply_wf ge_i (comp_of f) d (Some m_cu) = Some m_c') /\
                   (((public_first_order ge_i m2) -> (Mem.inject (meminj_public ge_i) m2 m_c')))).
      { desH DELTA_CASES.

        move MS1 after CUR_SWITCH_STAR. destruct MS1 as (MINJ & INJINCR & NALLOC).
        move DELTA after NALLOC. move PUB after NALLOC.
        hexploit mem_delta_apply_establish_inject_preprocess2.
        apply MINJ. eapply CNT_CUR_STORE.
        { instantiate (1:=ge_i). erewrite match_symbs_meminj_public. 2: destruct MS0 as (MS & _); apply MS.
          ii. unfold meminj_public in H. des_ifs. apply Senv.find_invert_symbol in FIND_CNT_CUR.
          rewrite FIND_CNT_CUR in Heq. clarify.
        }
        apply INJINCR. apply NALLOC. apply DELTA. apply PUB.
        intros (m_c' & DELTA' & INJ'). exists m_c'. splits; auto.
        rewrite CP_CUR. auto.
      }
      des. rename DELTA_C0 into MEMINJ_CNT.
      assert (ENV_ALLOC: exists e_next m_c_next0, alloc_variables ge_c (comp_of f_next) empty_env m_c' (fn_params f_next ++ fn_vars f_next) e_next m_c_next0).
      { eapply alloc_variables_exists. }
      des.
      assert (ENV_BIND: exists m_c_next, bind_parameters ge_c (comp_of f_next) e_next m_c_next0 (fn_params f_next) vargs m_c_next).
      { move PARSIGS after ENV_ALLOC. inv TR; ss.
        eapply bind_parameters_exists. 2: apply PARSIGS.
        2:{ eapply match_senv_eventval_list_match. 2: apply H1. destruct MS0 as (MS0 & _); auto. }
        rewrite app_nil_r in ENV_ALLOC. eapply alloc_variables_forall. apply ENV_ALLOC.
        { move MS5 after H1. destruct MS5. specialize (H2 _ _ PARS_NEXT). auto. }
      }
      des.
      set (create_undef_temps (fn_temps f_next)) as le_next.
      set (State f_next (fn_body f_next)
                 (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0))
                 e_next le_next m_c_next) as cst2.

      assert (ENV_NGLOB: not_global_blks (ge_c) (blocks_of_env2 ge_c e_next)).
      { clear CUR_SWITCH_STAR. move MS5 after le_next. destruct MS5 as (MP1 & MP2 & MP3).
        apply Forall_forall. i.
        unfold blocks_of_env2, blocks_of_env in H. rewrite map_map in H.
        apply list_in_map_inv in H. des. destruct x0 as (xid & xb & xt).
        apply PTree.elements_complete in H0. move WFNB after H0.
        destruct (Senv.invert_symbol ge_c x) eqn:CASES; auto. exfalso.
        unfold wf_c_nb in WFNB. apply Senv.invert_find_symbol in CASES. apply Senv.find_symbol_below in CASES.
        hexploit alloc_variables_one_fresh_block. eapply ENV_ALLOC.
        { ss. rewrite app_nil_r. eapply MP1. eauto. }
        { ss. }
        eapply H0. intros. apply H1; clear H1. ss. clarify. unfold Mem.valid_block.
        eapply mem_delta_apply_wf_wunchanged_on in DELTA_C. eapply store_wunchanged_on in CNT_CUR_STORE.
        eapply wunchanged_on_nextblock in CNT_CUR_STORE, DELTA_C. revert_until H0. clear; i.
        eapply Plt_Ple_trans. eapply CASES. etransitivity. eapply WFNB. etransitivity; eauto.
        Unshelve. all: exact (fun _ _ => True).
      }

      assert (ENV_NINJ: not_inj_blks (meminj_public ge_c) (blocks_of_env2 ge_c e_next)).
      { eapply not_global_is_not_inj_bloks. auto. }

      (* assert (ENV_NINJ: not_inj_blks (meminj_public ge_c) (blocks_of_env2 ge_c e_next)). *)
      (* { clear CUR_SWITCH_STAR. move MS5 after le_next. destruct MS5 as (MP1 & MP2 & MP3). *)
      (*   apply Forall_forall. i. *)
      (*   unfold blocks_of_env2, blocks_of_env in H. rewrite map_map in H. *)
      (*   apply list_in_map_inv in H. des. destruct x0 as (xid & xb & xt). *)
      (*   apply PTree.elements_complete in H0. *)
      (*   unfold meminj_public. des_ifs. exfalso. simpl in Heq. *)
      (*   move MS1 after Heq0. destruct MS1 as (MM1 & MM2 & MM3). *)
      (*   erewrite match_symbs_meminj_public in MEMINJ_CNT. *)
      (*   2:{ destruct MS0 as (MS0 & _). apply MS0. } *)
      (*   hexploit Mem.valid_block_inject_2. 2: eapply MEMINJ_CNT. *)
      (*   { unfold meminj_public. setoid_rewrite Heq. rewrite Heq0. eauto. } *)
      (*   eapply alloc_variables_one_fresh_block. eapply ENV_ALLOC. *)
      (*   { rewrite app_nil_r. eapply MP1. eauto. } *)
      (*   ss. eapply H0. *)
      (* } *)

      assert (WFC_NEXT: wf_c_state ge_c (pretr ++ [(id_cur, Bundle_call tr id_next evargs (fn_sig fi_next) d)]) ttr cnts id_next cst2).
      { subst cst2; ss. splits; auto.
        - unfold wf_counters. splits; auto.
          clear CUR_SWITCH_STAR. move WFC0 after le_next.
          ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
          unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
          exists b1. splits; auto.
          + eapply bind_parameters_valid_access. eapply ENV_BIND.
            eapply alloc_variables_valid_access. eapply ENV_ALLOC.
            eapply mem_delta_apply_wf_valid_access. eapply DELTA_C.
            eapply Mem.store_valid_access_1. eapply CNT_CUR_STORE.
            auto.
          + destruct (Pos.eq_dec id id_cur).
            * subst id. clarify. ss. rewrite FIND_CNT_CUR in WFC6. clarify.
              erewrite bind_parameters_mem_load. 2: eapply ENV_BIND.
              2:{ eapply alloc_variables_old_blocks. eapply ENV_ALLOC. 2: ii; ss. admit. (*ez*) }
              erewrite alloc_variables_mem_load. 2: eapply ENV_ALLOC.
              2:{ admit. (* same ez *) }
              erewrite mem_delta_apply_wf_mem_load.
              2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. apply DELTA_C. destruct MS0 as (MS & _). eauto. }
              2:{ eapply Genv.find_invert_symbol. eapply FIND_CNT_CUR. }
              2:{ auto. }
              erewrite Mem.load_store_same. 2: eapply CNT_CUR_STORE.
              ss. rewrite map_length. rewrite get_id_tr_app. ss.
              rewrite Pos.eqb_refl. rewrite app_length. ss.
              do 2 f_equal. apply nat64_int64_add_one.
              admit. (*ez*)
            * ss. erewrite bind_parameters_mem_load. 2: eapply ENV_BIND.
              2:{ eapply alloc_variables_old_blocks. eapply ENV_ALLOC. 2: ii; ss. admit. (*ez*) }
              erewrite alloc_variables_mem_load. 2: eapply ENV_ALLOC.
              2:{ admit. (* same ez *) }
              erewrite mem_delta_apply_wf_mem_load.
              2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. apply DELTA_C. destruct MS0 as (MS & _). eauto. }
              2:{ eapply Genv.find_invert_symbol. eapply WFC6. }
              2:{ auto. }
              erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
              2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                  rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                  specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
              }
              rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r.
              rewrite WFC8. auto.

        - clear CUR_SWITCH_STAR. move WFC1 after le_next. move WFC4 after WFC1. move FREEENV after WFC4.
          hexploit alloc_variables_exists_free_list. eapply ENV_ALLOC. ss. ss. ss. intros; des.
          hexploit wunchanged_on_exists_mem_free_list. 2: eapply H.
          { eapply wunchanged_on_implies. eapply bind_parameters_wunchanged_on. apply ENV_BIND. ss. }
          intros (m_f' & FREE).
          assert (WU: wunchanged_on (fun b _ => Mem.valid_block m_c b) m_c m_f').
          { eapply wunchanged_on_trans. eapply store_wunchanged_on. eapply CNT_CUR_STORE.
            eapply wunchanged_on_trans. eapply wunchanged_on_implies. eapply mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. ss.
            eapply wunchanged_on_trans. eapply wunchanged_on_implies. eapply alloc_variables_wunchanged_on. eapply ENV_ALLOC. ss.
            eapply wunchanged_on_trans. eapply wunchanged_on_implies. eapply bind_parameters_wunchanged_on. eapply ENV_BIND. ss.
            eapply mem_free_list_wunchanged_on. eapply FREE.
            eapply alloc_variables_fresh_blocks. eapply ENV_ALLOC.
            2:{ unfold blocks_of_env, empty_env. ss. }
            hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. i. eapply wunchanged_on_nextblock in H0.
            etransitivity. 2: eapply H0. erewrite <- Mem.nextblock_store. 2: eapply CNT_CUR_STORE. lia.
          }
          hexploit wunchanged_on_exists_mem_free_list. eapply WU. eapply FREEENV. intros (m_freeenv' & FREEENV').
          exists m_f'. splits; auto. econs. 1,2,3: eauto. eapply FREEENV'.
          hexploit wunchanged_on_free_list_preserves. eapply WU. eapply FREEENV. eapply FREEENV'. intros WUFREE.
          move WFC1 after FREEENV'.
          eapply wf_c_cont_wunchanged_on. eapply WFC1. apply WUFREE.

        - move WFC2 after le_next. unfold wf_c_stmt in *. clear CUR_SWITCH_STAR.
          i. rewrite CNTS_NEXT in H. inv H. rename cnt into cnt_next.
          subst f_next. unfold comp_of. ss. apply match_symbs_code_bundle_trace.
          destruct MS0 as (MS0 & _); auto.

        - clear CUR_SWITCH_STAR. move MS5 after le_next. destruct MS5 as (MP1 & MP2 & MP3).
          eapply alloc_variables_wf_params_of_symb. eapply ENV_ALLOC. eapply MP3.
          rewrite app_nil_r. apply PARS_NEXT.

        - clear CUR_SWITCH_STAR. move WFNB after ENV_NINJ. unfold wf_c_nb in *.
          eapply bind_parameters_wunchanged_on in ENV_BIND. eapply alloc_variables_wunchanged_on in ENV_ALLOC.
          eapply mem_delta_apply_wf_wunchanged_on in DELTA_C. eapply store_wunchanged_on in CNT_CUR_STORE.
          eapply wunchanged_on_nextblock in CNT_CUR_STORE, DELTA_C, ENV_ALLOC, ENV_BIND.
          clear - CNT_CUR_STORE DELTA_C ENV_ALLOC ENV_BIND WFNB.
          do 5 (etransitivity; eauto).
      }

      assert (MS_NEXT: match_state ge_i ge_c (meminj_public ge_i) ttr cnts pars id_next (Some (b, m2, ir_cont cur :: k_i)) cst2).
      { clear CUR_SWITCH_STAR WFC_NEXT. subst cst2. ss.
        rewrite app_nil_r in ENV_ALLOC. splits; auto.
        - unfold match_mem. splits; auto.
          + eapply bind_parameters_outside_mem_inject. eapply ENV_BIND.
            2:{ eapply not_inj_blks_get_env. erewrite match_symbs_meminj_public. eapply ENV_NINJ. destruct MS0 as (MS0 & _). apply MS0.
            }
            2: apply meminj_public_same_block.
            eapply alloc_variables_mem_inject. eapply ENV_ALLOC. auto.
          + move MS1 after ENV_NINJ. destruct MS1 as (MM1 & MM2 & MM3).
            move DELTA after ENV_NINJ. eapply meminj_not_alloc_delta. eapply MM3. eapply DELTA.
        - unfold match_cur_fun. splits; auto.
          + rewrite Genv.find_funct_ptr_iff. eapply FINDF_C.
          + eexists. eapply FINDF.
          + apply Genv.find_invert_symbol. apply FINDB.
        - move MS4 after ENV_NINJ. econs 2. 4,5,6: eauto. all: auto.
          apply Genv.find_invert_symbol. apply FIND_CUR_C.
        - move MS1 after ENV_NINJ. move MCNTS after MS1. destruct MS1 as (MM1 & MM2 & MM3).
          eapply mem_inject_incr_match_cnts_rev. eapply MM2. auto.
      }

      exists cst2. split.
      2:{ left. exists id_next. split. apply WFC_NEXT. eexists. eapply MS_NEXT. }
      unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
      eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
      unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
      rewrite ! (match_symbs_code_bundle_call ge_i ge_c) in CUR_SWITCH_STAR. rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
      eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: auto.
      clear BOUND2 CUR_SWITCH_STAR.
      unfold code_bundle_call. eapply star_trans. eapply code_mem_delta_correct. auto.
      { erewrite <- match_symbs_mem_delta_apply_wf. eapply DELTA_C.
        destruct MS0 as (MSYMB & _). auto. }
      2: ss. 2,3: destruct MS0 as (MSENV & _); apply MSENV.
      unfold unbundle. simpl. rename b into next.

      assert (CP_NEXT:
               (Genv.find_comp ge_c (Vptr next Ptrofs.zero)) =
                 (comp_of fi_next)).
      { unfold Genv.find_comp. apply Genv.find_funct_ptr_iff in FINDF_C. setoid_rewrite FINDF_C. subst f_next. ss. }
      assert (EVARGS: list_eventval_to_list_val ge_c evargs = vargs).
      { destruct MS0 as (MSENV & MGENV). inv TR.
        eapply eventval_list_match_list_eventval_to_list_val. eapply match_symbs_eventval_list_match; eauto.
      }

      econs 2.
      { eapply step_call. ss.
        { econs. assert (FSN_C: Senv.find_symbol ge_c id_next = Some next).
          { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1. auto. }
          eapply eval_Evar_global.
          - unfold wf_env in WFC3. specialize (WFC3 id_next). rewrite FSN_C in WFC3. apply WFC3.
          - eapply FSN_C.
          - econs 2. ss.
        }
        { eapply list_eventval_to_expr_val_eval. auto. inv TR. eapply eventval_list_match_transl. eapply match_senv_eventval_list_match; eauto. destruct MS0 as (MSENV & _); auto. }
        { unfold match_find_def in MS3. hexploit MS3.
          unfold Genv.find_funct in FINDF. rewrite pred_dec_true in FINDF; auto. unfold Genv.find_funct_ptr in FINDF. des_ifs. eapply Heq.
          eapply Senv.find_invert_symbol; eapply FINDB.
          rewrite CNTS_NEXT, PARS_NEXT. intros. unfold Genv.find_funct. rewrite pred_dec_true. unfold Genv.find_funct_ptr. rewrite H. ss. ss.
        }
        { ss. unfold type_of_function, gen_function. ss. f_equal. apply type_of_params_eq. apply PARSIGS. }
        { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV).
          subst f. setoid_rewrite CP_CUR.
          eapply allowed_call_gen_function; eauto.
          { setoid_rewrite Genv.find_funct_ptr_iff. rewrite FINDF_C. subst f_next. eauto. }
        }
        { move NPTR after MS_NEXT. move TR after NPTR. i.
          rewrite EVARGS. apply NPTR. unfold crossing_comp. rewrite <- H.
          setoid_rewrite CP_CUR. rewrite CP_NEXT. auto.
        }
        { move TR after MS_NEXT. instantiate (1:=tr). inv TR.
          setoid_rewrite CP_CUR. rewrite CP_NEXT.
          econs 2.
          { rewrite <- H. ss. }
          eauto.
          { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.find_invert_symbol. apply MSENV1. auto. }
          { eapply eventval_list_match_transl. eapply match_senv_eventval_list_match; eauto. destruct MS0 as (MSENV & _); auto. }
        }
      }
      { econs 2. 2: econs 1. eapply step_internal_function. 2: ss.
        econs; eauto.
        { destruct MS5 as (MPARS & _). specialize (MPARS _ _ PARS_NEXT). subst f_next. ss. rewrite app_nil_r. auto. }
        { rewrite EVARGS. auto. }
      }
      traceEq.
      


    (* WIP *)
    Lemma ir_to_clight_step
          (ge_i: Asm.genv) (ge_c: Clight.genv)
          (WFGE: wf_ge ge_i)
          cnts pars ist1 ev ist2
          (STEP: ir_step ge_i ist1 ev ist2)
          ttr pretr btr
          (BOUND: Z.of_nat (Datatypes.length ttr) < Int64.modulus)
          (TOTAL: ttr = pretr ++ ev :: btr)
          cst1 k id
          (WFC: wf_c_state ge_c pretr ttr cnts id cst1)
          (MS: match_state ge_i ge_c k ttr cnts pars id ist1 cst1)
      :
      exists cst2, (star step1 ge_c cst1 (unbundle ev) cst2) /\
                ((exists id', (wf_c_state ge_c (pretr ++ [ev]) ttr cnts id' cst2) /\
                           exists k, (match_state ge_i ge_c k ttr cnts pars id' ist2 cst2))
                 \/ (ist2 = None)).
    Proof.
      (* REMOVE *)
      Set Nested Proofs Allowed.

      unfold wf_c_state in WFC. des_ifs. rename s into stmt, k into k_c, m into m_c.
      destruct WFC as ((CNT_INJ & WFC0) & (m_freeenv & FREEENV & WFC1) & WFC2 & WFC3 & WFC4 & WFNB).
      unfold match_state in MS. des_ifs. rename i into k_i, b into cur, m into m_i.
      destruct MS as (MS0 & MS1 & MS2 & MS3 & MS4 & MS5 & MCNTS).
      move STEP after WFC4. inv STEP.

      (** Case 1: Cross Call *)
      - assert (id = id_cur).
        { unfold match_cur_fun in MS2. des. rewrite MS7 in IDCUR. clarify. }
        subst id.
        rename f_next into fi_next.

        exploit MS3.
        { eapply Genv.find_funct_ptr_iff. erewrite <- Genv.find_funct_find_funct_ptr. eapply FINDF. }
        { eapply Genv.find_invert_symbol; eauto. }
        intros FINDF_C. des_ifs. rename id0 into id_next, i into cnt_next, Heq into CNTS_NEXT, l into params_next, Heq0 into PARS_NEXT. simpl in FINDF_C.
        set (pretr ++ (id_cur, Bundle_call tr id_next evargs (fn_sig fi_next) d) :: btr) as ttr in *.
        set (gen_function ge_i cnt_next params_next (get_id_tr ttr id_next) fi_next) as f_next in *.
        set (fn_body f_next) as stmt_next.
        assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
        { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.invert_find_symbol in IDCUR. apply MSENV1 in IDCUR. auto. }
        assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
        { destruct MS2 as (MFUN0 & MFUN1). auto. }

        exploit WFC0. eapply FIND_CUR_C. eapply FIND_FUN_C. intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
        set (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)) as kc_next.
        assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_call tr id_next evargs (fn_sig fi_next) d) :: (get_id_tr btr id_cur)).
        { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
        assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
        { rewrite map_length. etransitivity. 2: eauto. unfold get_id_tr. admit. (* ez *) }
        destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).
        assert (PARSIGS: list_typ_to_list_type (sig_args (fn_sig fi_next)) = map snd params_next).
        { destruct MS5 as (_ & WFP1 & _). exploit WFP1. apply FINDF. apply FINDB. apply PARS_NEXT. ss. }

        destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).
        hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply INV_CUR. eauto.
        intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
        rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
        assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
        { unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss. }

        hexploit switch_spec.
        { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
        { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3. }
        eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
        { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
        instantiate (1:=le).
        instantiate (1:=(Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)).
        instantiate (1:=Sreturn None).
        intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).

        assert (DELTA_C: exists m_c', (mem_delta_apply_wf ge_i (comp_of f) d (Some m_cu) = Some m_c') /\
                                   (Mem.inject (meminj_public ge_i) m2 m_c')).
        { move MS1 after CUR_SWITCH_STAR. destruct MS1 as (MINJ & INJINCR & NALLOC).
          move DELTA after NALLOC. move PUB after NALLOC.
          hexploit mem_delta_apply_establish_inject_preprocess2.
          apply MINJ. eapply CNT_CUR_STORE.
          { instantiate (1:=ge_i). erewrite match_symbs_meminj_public. 2: destruct MS0 as (MS & _); apply MS.
            ii. unfold meminj_public in H. des_ifs. apply Senv.find_invert_symbol in FIND_CNT_CUR.
            rewrite FIND_CNT_CUR in Heq. clarify.
          }
          apply INJINCR. apply NALLOC. apply DELTA. apply PUB.
          intros (m_c' & DELTA' & INJ'). exists m_c'. splits; auto.
          rewrite CP_CUR. auto.
        }
        des. rename DELTA_C0 into MEMINJ_CNT.
        assert (ENV_ALLOC: exists e_next m_c_next0, alloc_variables ge_c (comp_of f_next) empty_env m_c' (fn_params f_next ++ fn_vars f_next) e_next m_c_next0).
        { eapply alloc_variables_exists. }
        des.
        assert (ENV_BIND: exists m_c_next, bind_parameters ge_c (comp_of f_next) e_next m_c_next0 (fn_params f_next) vargs m_c_next).
        { move PARSIGS after ENV_ALLOC. inv TR; ss.
          eapply bind_parameters_exists. 2: apply PARSIGS.
          2:{ eapply match_senv_eventval_list_match. 2: apply H1. destruct MS0 as (MS0 & _); auto. }
          rewrite app_nil_r in ENV_ALLOC. eapply alloc_variables_forall. apply ENV_ALLOC.
          { move MS5 after H1. destruct MS5. specialize (H2 _ _ PARS_NEXT). auto. }
        }
        des.
        set (create_undef_temps (fn_temps f_next)) as le_next.
        set (State f_next (fn_body f_next)
                   (Kcall None f e le (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0))
                   e_next le_next m_c_next) as cst2.

        assert (ENV_NGLOB: not_global_blks (ge_c) (blocks_of_env2 ge_c e_next)).
        { clear CUR_SWITCH_STAR. move MS5 after le_next. destruct MS5 as (MP1 & MP2 & MP3).
          apply Forall_forall. i.
          unfold blocks_of_env2, blocks_of_env in H. rewrite map_map in H.
          apply list_in_map_inv in H. des. destruct x0 as (xid & xb & xt).
          apply PTree.elements_complete in H0. move WFNB after H0.
          destruct (Senv.invert_symbol ge_c x) eqn:CASES; auto. exfalso.
          unfold wf_c_nb in WFNB. apply Senv.invert_find_symbol in CASES. apply Senv.find_symbol_below in CASES.
          hexploit alloc_variables_one_fresh_block. eapply ENV_ALLOC.
          { ss. rewrite app_nil_r. eapply MP1. eauto. }
          { ss. }
          eapply H0. intros. apply H1; clear H1. ss. clarify. unfold Mem.valid_block.
          eapply mem_delta_apply_wf_wunchanged_on in DELTA_C. eapply store_wunchanged_on in CNT_CUR_STORE.
          eapply wunchanged_on_nextblock in CNT_CUR_STORE, DELTA_C. revert_until H0. clear; i.
          eapply Plt_Ple_trans. eapply CASES. etransitivity. eapply WFNB. etransitivity; eauto.
          Unshelve. all: exact (fun _ _ => True).
        }

        assert (ENV_NINJ: not_inj_blks (meminj_public ge_c) (blocks_of_env2 ge_c e_next)).
        { eapply not_global_is_not_inj_bloks. auto. }

        (* assert (ENV_NINJ: not_inj_blks (meminj_public ge_c) (blocks_of_env2 ge_c e_next)). *)
        (* { clear CUR_SWITCH_STAR. move MS5 after le_next. destruct MS5 as (MP1 & MP2 & MP3). *)
        (*   apply Forall_forall. i. *)
        (*   unfold blocks_of_env2, blocks_of_env in H. rewrite map_map in H. *)
        (*   apply list_in_map_inv in H. des. destruct x0 as (xid & xb & xt). *)
        (*   apply PTree.elements_complete in H0. *)
        (*   unfold meminj_public. des_ifs. exfalso. simpl in Heq. *)
        (*   move MS1 after Heq0. destruct MS1 as (MM1 & MM2 & MM3). *)
        (*   erewrite match_symbs_meminj_public in MEMINJ_CNT. *)
        (*   2:{ destruct MS0 as (MS0 & _). apply MS0. } *)
        (*   hexploit Mem.valid_block_inject_2. 2: eapply MEMINJ_CNT. *)
        (*   { unfold meminj_public. setoid_rewrite Heq. rewrite Heq0. eauto. } *)
        (*   eapply alloc_variables_one_fresh_block. eapply ENV_ALLOC. *)
        (*   { rewrite app_nil_r. eapply MP1. eauto. } *)
        (*   ss. eapply H0. *)
        (* } *)

        assert (WFC_NEXT: wf_c_state ge_c (pretr ++ [(id_cur, Bundle_call tr id_next evargs (fn_sig fi_next) d)]) ttr cnts id_next cst2).
        { subst cst2; ss. splits; auto.
          - unfold wf_counters. splits; auto.
            clear CUR_SWITCH_STAR. move WFC0 after le_next.
            ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
            unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
            exists b1. splits; auto.
            + eapply bind_parameters_valid_access. eapply ENV_BIND.
              eapply alloc_variables_valid_access. eapply ENV_ALLOC.
              eapply mem_delta_apply_wf_valid_access. eapply DELTA_C.
              eapply Mem.store_valid_access_1. eapply CNT_CUR_STORE.
              auto.
            + destruct (Pos.eq_dec id id_cur).
              * subst id. clarify. ss. rewrite FIND_CNT_CUR in WFC6. clarify.
                erewrite bind_parameters_mem_load. 2: eapply ENV_BIND.
                2:{ eapply alloc_variables_old_blocks. eapply ENV_ALLOC. 2: ii; ss. admit. (*ez*) }
                erewrite alloc_variables_mem_load. 2: eapply ENV_ALLOC.
                2:{ admit. (* same ez *) }
                erewrite mem_delta_apply_wf_mem_load.
                2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. apply DELTA_C. destruct MS0 as (MS & _). eauto. }
                2:{ eapply Genv.find_invert_symbol. eapply FIND_CNT_CUR. }
                2:{ auto. }
                erewrite Mem.load_store_same. 2: eapply CNT_CUR_STORE.
                ss. rewrite map_length. rewrite get_id_tr_app. ss.
                rewrite Pos.eqb_refl. rewrite app_length. ss.
                do 2 f_equal. apply nat64_int64_add_one.
                admit. (*ez*)
              * ss. erewrite bind_parameters_mem_load. 2: eapply ENV_BIND.
                2:{ eapply alloc_variables_old_blocks. eapply ENV_ALLOC. 2: ii; ss. admit. (*ez*) }
                erewrite alloc_variables_mem_load. 2: eapply ENV_ALLOC.
                2:{ admit. (* same ez *) }
                erewrite mem_delta_apply_wf_mem_load.
                2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. apply DELTA_C. destruct MS0 as (MS & _). eauto. }
                2:{ eapply Genv.find_invert_symbol. eapply WFC6. }
                2:{ auto. }
                erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
                2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                    rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                    specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
                }
                rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r.
                rewrite WFC8. auto.

          - clear CUR_SWITCH_STAR. move WFC1 after le_next. move WFC4 after WFC1. move FREEENV after WFC4.
            hexploit alloc_variables_exists_free_list. eapply ENV_ALLOC. ss. ss. ss. intros; des.
            hexploit wunchanged_on_exists_mem_free_list. 2: eapply H.
            { eapply wunchanged_on_implies. eapply bind_parameters_wunchanged_on. apply ENV_BIND. ss. }
            intros (m_f' & FREE).
            assert (WU: wunchanged_on (fun b _ => Mem.valid_block m_c b) m_c m_f').
            { eapply wunchanged_on_trans. eapply store_wunchanged_on. eapply CNT_CUR_STORE.
              eapply wunchanged_on_trans. eapply wunchanged_on_implies. eapply mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. ss.
              eapply wunchanged_on_trans. eapply wunchanged_on_implies. eapply alloc_variables_wunchanged_on. eapply ENV_ALLOC. ss.
              eapply wunchanged_on_trans. eapply wunchanged_on_implies. eapply bind_parameters_wunchanged_on. eapply ENV_BIND. ss.
              eapply mem_free_list_wunchanged_on. eapply FREE.
              eapply alloc_variables_fresh_blocks. eapply ENV_ALLOC.
              2:{ unfold blocks_of_env, empty_env. ss. }
              hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. i. eapply wunchanged_on_nextblock in H0.
              etransitivity. 2: eapply H0. erewrite <- Mem.nextblock_store. 2: eapply CNT_CUR_STORE. lia.
            }
            hexploit wunchanged_on_exists_mem_free_list. eapply WU. eapply FREEENV. intros (m_freeenv' & FREEENV').
            exists m_f'. splits; auto. econs. 1,2,3: eauto. eapply FREEENV'.
            hexploit wunchanged_on_free_list_preserves. eapply WU. eapply FREEENV. eapply FREEENV'. intros WUFREE.
            move WFC1 after FREEENV'.
            eapply wf_c_cont_wunchanged_on. eapply WFC1. apply WUFREE.

          - move WFC2 after le_next. unfold wf_c_stmt in *. clear CUR_SWITCH_STAR.
            i. rewrite CNTS_NEXT in H. inv H. rename cnt into cnt_next.
            subst f_next. unfold comp_of. ss. apply match_symbs_code_bundle_trace.
            destruct MS0 as (MS0 & _); auto.

          - clear CUR_SWITCH_STAR. move MS5 after le_next. destruct MS5 as (MP1 & MP2 & MP3).
            eapply alloc_variables_wf_params_of_symb. eapply ENV_ALLOC. eapply MP3.
            rewrite app_nil_r. apply PARS_NEXT.

          - clear CUR_SWITCH_STAR. move WFNB after ENV_NINJ. unfold wf_c_nb in *.
            eapply bind_parameters_wunchanged_on in ENV_BIND. eapply alloc_variables_wunchanged_on in ENV_ALLOC.
            eapply mem_delta_apply_wf_wunchanged_on in DELTA_C. eapply store_wunchanged_on in CNT_CUR_STORE.
            eapply wunchanged_on_nextblock in CNT_CUR_STORE, DELTA_C, ENV_ALLOC, ENV_BIND.
            clear - CNT_CUR_STORE DELTA_C ENV_ALLOC ENV_BIND WFNB.
            do 5 (etransitivity; eauto).
        }

        assert (MS_NEXT: match_state ge_i ge_c (meminj_public ge_i) ttr cnts pars id_next (Some (b, m2, ir_cont cur :: k_i)) cst2).
        { clear CUR_SWITCH_STAR WFC_NEXT. subst cst2. ss.
          rewrite app_nil_r in ENV_ALLOC. splits; auto.
          - unfold match_mem. splits; auto.
            + eapply bind_parameters_outside_mem_inject. eapply ENV_BIND.
              2:{ eapply not_inj_blks_get_env. erewrite match_symbs_meminj_public. eapply ENV_NINJ. destruct MS0 as (MS0 & _). apply MS0.
              }
              2: apply meminj_public_same_block.
              eapply alloc_variables_mem_inject. eapply ENV_ALLOC. auto.
            + move MS1 after ENV_NINJ. destruct MS1 as (MM1 & MM2 & MM3).
              move DELTA after ENV_NINJ. eapply meminj_not_alloc_delta. eapply MM3. eapply DELTA.
          - unfold match_cur_fun. splits; auto.
            + rewrite Genv.find_funct_ptr_iff. eapply FINDF_C.
            + eexists. eapply FINDF.
            + apply Genv.find_invert_symbol. apply FINDB.
          - move MS4 after ENV_NINJ. econs 2. 4,5,6: eauto. all: auto.
            apply Genv.find_invert_symbol. apply FIND_CUR_C.
          - move MS1 after ENV_NINJ. move MCNTS after MS1. destruct MS1 as (MM1 & MM2 & MM3).
            eapply mem_inject_incr_match_cnts_rev. eapply MM2. auto.
        }

        exists cst2. split.
        2:{ left. exists id_next. split. apply WFC_NEXT. eexists. eapply MS_NEXT. }
        unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
        eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
        unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
        rewrite ! (match_symbs_code_bundle_call ge_i ge_c) in CUR_SWITCH_STAR. rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
        eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: auto.
        clear BOUND2 CUR_SWITCH_STAR.
        unfold code_bundle_call. eapply star_trans. eapply code_mem_delta_correct. auto.
        { erewrite <- match_symbs_mem_delta_apply_wf. eapply DELTA_C.
          destruct MS0 as (MSYMB & _). auto. }
        2: ss. 2,3: destruct MS0 as (MSENV & _); apply MSENV.
        unfold unbundle. simpl. rename b into next.

        assert (CP_NEXT:
                 (Genv.find_comp ge_c (Vptr next Ptrofs.zero)) =
                   (comp_of fi_next)).
        { unfold Genv.find_comp. apply Genv.find_funct_ptr_iff in FINDF_C. setoid_rewrite FINDF_C. subst f_next. ss. }
        assert (EVARGS: list_eventval_to_list_val ge_c evargs = vargs).
        { destruct MS0 as (MSENV & MGENV). inv TR.
          eapply eventval_list_match_list_eventval_to_list_val. eapply match_symbs_eventval_list_match; eauto.
        }

        econs 2.
        { eapply step_call. ss.
          { econs. assert (FSN_C: Senv.find_symbol ge_c id_next = Some next).
            { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1. auto. }
            eapply eval_Evar_global.
            - unfold wf_env in WFC3. specialize (WFC3 id_next). rewrite FSN_C in WFC3. apply WFC3.
            - eapply FSN_C.
            - econs 2. ss.
          }
          { eapply list_eventval_to_expr_val_eval. auto. inv TR. eapply eventval_list_match_transl. eapply match_senv_eventval_list_match; eauto. destruct MS0 as (MSENV & _); auto. }
          { unfold match_find_def in MS3. hexploit MS3.
            unfold Genv.find_funct in FINDF. rewrite pred_dec_true in FINDF; auto. unfold Genv.find_funct_ptr in FINDF. des_ifs. eapply Heq.
            eapply Senv.find_invert_symbol; eapply FINDB.
            rewrite CNTS_NEXT, PARS_NEXT. intros. unfold Genv.find_funct. rewrite pred_dec_true. unfold Genv.find_funct_ptr. rewrite H. ss. ss.
          }
          { ss. unfold type_of_function, gen_function. ss. f_equal. apply type_of_params_eq. apply PARSIGS. }
          { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV).
            subst f. setoid_rewrite CP_CUR.
            eapply allowed_call_gen_function; eauto.
            { setoid_rewrite Genv.find_funct_ptr_iff. rewrite FINDF_C. subst f_next. eauto. }
          }
          { move NPTR after MS_NEXT. move TR after NPTR. i.
            rewrite EVARGS. apply NPTR. unfold crossing_comp. rewrite <- H.
            setoid_rewrite CP_CUR. rewrite CP_NEXT. auto.
          }
          { move TR after MS_NEXT. instantiate (1:=tr). inv TR.
            setoid_rewrite CP_CUR. rewrite CP_NEXT.
            econs 2.
            { rewrite <- H. ss. }
            eauto.
            { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.find_invert_symbol. apply MSENV1. auto. }
            { eapply eventval_list_match_transl. eapply match_senv_eventval_list_match; eauto. destruct MS0 as (MSENV & _); auto. }
          }
        }
        { econs 2. 2: econs 1. eapply step_internal_function. 2: ss.
          econs; eauto.
          { destruct MS5 as (MPARS & _). specialize (MPARS _ _ PARS_NEXT). subst f_next. ss. rewrite app_nil_r. auto. }
          { rewrite EVARGS. auto. }
        }
        traceEq.

      (** Case 2: Cross Return *)
      - assert (id = id_cur).
        { unfold match_cur_fun in MS2. des. rewrite MS7 in IDCUR. clarify. }
        subst id. rename f_next into fi_next.
        assert (INV_ID_NEXT: exists id_next, Genv.invert_symbol ge_i next = Some id_next).
        { rewrite Genv.find_funct_ptr_iff in INTERNAL. eapply wf_ge_block_to_id. auto. eauto. }
        des.

        exploit MS3.
        { eapply Genv.find_funct_ptr_iff. eapply INTERNAL. }
        { eapply INV_ID_NEXT. }
        intros FINDF_C. des_ifs. rename i into cnt_next, Heq into CNTS_NEXT, l into params_next, Heq0 into PARS_NEXT. simpl in FINDF_C.
        set (pretr ++ (id_cur, Bundle_return tr evretv d) :: btr) as ttr in *.
        set (gen_function ge_i cnt_next params_next (get_id_tr ttr id_next) fi_next) as f_next in *.
        set (fn_body f_next) as stmt_next.
        assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
        { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.invert_find_symbol in IDCUR. apply MSENV1 in IDCUR. auto. }
        assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
        { destruct MS2 as (MFUN0 & MFUN1). auto. }

        exploit WFC0. eapply FIND_CUR_C. eapply FIND_FUN_C. intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
        inv WFC1.
        { inv MS4. inv IK. inv CK. }
        assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_return tr evretv d) :: (get_id_tr btr id_cur)).
        { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
        assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
        { rewrite map_length. etransitivity. 2: eauto. unfold get_id_tr. admit. (* ez *) }
        destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).
        assert (PARSIGS: list_typ_to_list_type (sig_args (fn_sig fi_next)) = map snd params_next).
        { destruct MS5 as (_ & WFP1 & _). exploit WFP1. apply INTERNAL. apply Genv.invert_find_symbol. apply INV_ID_NEXT. apply PARS_NEXT. ss. }

        inv MS4.
        { inv IK. }
        clarify.

        destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).
        hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply INV_CUR. eauto.
        intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
        rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
        assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
        { unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss. }

        rename ck'0 into ck_next. rename e1 into e_next. rename le1 into le_next.
        hexploit switch_spec.
        { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
        { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3. }
        eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
        { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
        instantiate (1:=le).
        instantiate (1:= (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur)))
          Sskip
          (Kcall None f_next e_next le_next (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_next (comp_of f_next) (get_id_tr ttr id_next))) Sskip ck_next)))).
        instantiate (1:=Sreturn None).
        intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).

        assert (DELTA_C: exists m_c', (mem_delta_apply_wf ge_i (comp_of f) d (Some m_cu) = Some m_c') /\
                                   (Mem.inject (meminj_public ge_i) m2 m_c')).
        { move MS1 after CUR_SWITCH_STAR. destruct MS1 as (MINJ & INJINCR & NALLOC).
          move DELTA after NALLOC. move PUB after NALLOC.
          hexploit mem_delta_apply_establish_inject_preprocess2.
          apply MINJ. eapply CNT_CUR_STORE.
          { instantiate (1:=ge_i). erewrite match_symbs_meminj_public. 2: destruct MS0 as (MS & _); apply MS.
            ii. unfold meminj_public in H. des_ifs. apply Senv.find_invert_symbol in FIND_CNT_CUR.
            rewrite FIND_CNT_CUR in Heq. clarify.
          }
          apply INJINCR. apply NALLOC. apply DELTA. apply PUB.
          intros (m_c' & DELTA' & INJ'). exists m_c'. splits; auto.
          rewrite CP_CUR. auto.
        }
        des. rename DELTA_C0 into MEMINJ_CNT.

        assert (f1 = f_next).
        { rewrite <- Genv.find_funct_ptr_iff in FINDF_C. rewrite FINDF_C in FUN. clarify. }
        subst f1. clear INV_CUR.
        assert (id = id_next).
        { apply Genv.invert_find_symbol in INV_ID_NEXT. destruct MS0 as ((_ & MS & _) & _). apply MS in INV_ID_NEXT.
          apply Senv.find_invert_symbol in INV_ID_NEXT. setoid_rewrite INV_ID_NEXT in ID. clarify.
        }
        subst id.
        assert (cnt = cnt_next).
        { rewrite CNTS_NEXT in CNT. clarify. }
        subst cnt. clear ID CNT.

        assert (WCHG1: wunchanged_on (fun b _ => Mem.valid_block m_c b) m_c m_c').
        { eapply wunchanged_on_trans. eapply store_wunchanged_on. eapply CNT_CUR_STORE.
          eapply wunchanged_on_implies. eapply mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. ss.
        }
        assert (FREENEXT: exists m_c_next, Mem.free_list m_c' (blocks_of_env ge_c e) (comp_of f) = Some m_c_next).
        { eapply wunchanged_on_exists_mem_free_list. eapply WCHG1. eapply FREEENV. }
        des.

        set (State f_next (fn_body f_next) ck_next e_next le_next m_c_next) as cst2.

        assert (WFC_NEXT: wf_c_state ge_c (pretr ++ [(id_cur, Bundle_return tr evretv d)]) ttr cnts id_next cst2).
        { clear CUR_SWITCH_STAR. ss. splits; auto.
          - unfold wf_counters. split. auto.
            move WFC0 after cst2.
            ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
            unfold wf_counter in WFC1. des. unfold wf_counter. splits; auto.
            exists b1. splits; auto.
            + eapply mem_valid_access_wunchanged_on. eapply WFC6.
              eapply wunchanged_on_trans; cycle 1. eapply mem_free_list_wunchanged_on_2. eapply FREENEXT.
              eapply wunchanged_on_trans; cycle 1. eapply mem_delta_apply_wf_wunchanged_on. eapply DELTA_C.
              eapply store_wunchanged_on. eapply CNT_CUR_STORE. ss. i.
              move MS5 after H0. destruct MS5 as (MP0 & MP1 & MP). specialize (MP _ _ WFC5). move WFC4 after MP.
              eapply not_global_blks_global_not_in; eauto.
            + move WFNB after CP_CUR. move WFC4 after WFNB.
              eapply Mem.load_unchanged_on. eapply mem_free_list_unchanged_on. eapply FREENEXT.
              { ss. i. eapply not_global_blks_global_not_in; eauto. }
              erewrite mem_delta_apply_wf_mem_load; cycle 1.
              { erewrite match_symbs_mem_delta_apply_wf in DELTA_C. apply DELTA_C. destruct MS0 as (MS & _). eauto. }
              { eapply Genv.find_invert_symbol. apply WFC5. }
              { auto. }
              destruct (Pos.eq_dec id id_cur).
              * subst id. assert (cnt_cur = cnt).
                { rewrite WFC0 in CNTS_CUR. clarify. }
                subst cnt. assert (b1 = cnt_cur_b).
                { setoid_rewrite WFC5 in FIND_CNT_CUR. clarify. }
                subst b1. assert (b0 = cur).
                { rewrite FIND_CUR_C in H. clarify. }
                subst b0. assert (f0 = f).
                { rewrite FINDF_C_CUR in H0. clarify. }
                subst f0. erewrite Mem.load_store_same. 2: eapply CNT_CUR_STORE.
                ss. rewrite map_length. rewrite get_id_tr_app. ss.
                rewrite Pos.eqb_refl. rewrite app_length. ss.
                do 2 f_equal. apply nat64_int64_add_one.
                admit. (*ez*)
              * ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
                2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC5.
                    rewrite FIND_CNT_CUR in WFC5. clarify. rename cnt into cnt_cur.
                    specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
                }
                rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. rewrite WFC7. auto.

          - move IND after cst2. move FREE after cst2. move FREEENV after cst2.
            hexploit wunchanged_on_free_list_preserves. eapply WCHG1. all: eauto. intros WCHG2.
            hexploit wunchanged_on_exists_mem_free_list. eapply WCHG2. eapply FREE. intros (m_c_next2 & FREE2).
            exists m_c_next2. splits; auto.
            hexploit wunchanged_on_free_list_preserves. eapply WCHG2. all: eauto. intros WCHG3.
            eapply wf_c_cont_wunchanged_on. eapply IND. auto.

          - move WFC2 after cst2. unfold wf_c_stmt in *. i. rewrite CNTS_NEXT in H. inv H. rename cnt into cnt_next.
            subst f_next. unfold comp_of. ss. apply match_symbs_code_bundle_trace. destruct MS0 as (MS0 & _); auto.

          - move WFNB after cst2. unfold wf_c_nb in *.
            apply SimplLocalsproof.free_list_nextblock in FREENEXT. rewrite FREENEXT.
            eapply mem_delta_apply_wf_wunchanged_on in DELTA_C. eapply store_wunchanged_on in CNT_CUR_STORE.
            eapply wunchanged_on_nextblock in CNT_CUR_STORE, DELTA_C.
            clear - WFNB CNT_CUR_STORE DELTA_C.
            do 5 (etransitivity; eauto).
            Unshelve. all: try (exact 0%nat). all: try (exact (fun _ _ => True)).
        }

        assert (MS_NEXT: match_state ge_i ge_c (meminj_public ge_i) ttr cnts pars id_next (Some (b, m2, ik')) cst2).
        { clear CUR_SWITCH_STAR WFC_NEXT. ss. splits; auto.
          - unfold match_mem. splits; auto.
            + eapply SimplLocalsproof.free_list_right_inject. eapply MEMINJ_CNT. eapply FREENEXT.
              i. move WFC4 after cst2. apply not_global_is_not_inj_bloks in WFC4. setoid_rewrite Forall_forall in WFC4.
              assert (b2 = b1).
              { clear - H. unfold meminj_public in H. des_ifs. }
              subst b2. hexploit (WFC4 b1).
              { unfold blocks_of_env2, blocks_of_env in *. rewrite map_map.
                eapply (in_map (fun x => fst (fst x))) in H0. ss. rewrite map_map in H0. ss.
              }
              intros. erewrite <- match_symbs_meminj_public in H3. rewrite H in H3. clarify.
              destruct MS0 as (MS & _). apply MS.
            + move MS1 after cst2. destruct MS1 as (MM1 & MM2 & MM3).
              move DELTA after cst2. eapply meminj_not_alloc_delta. eapply MM3. eapply DELTA.
          - unfold match_cur_fun. splits; auto. eauto.
          - destruct MS1 as (MM1 & MM2 & MM3). eapply mem_inject_incr_match_cnts_rev; eauto.
        }
        exists cst2. split.
        2:{ left. exists id_next. split. apply WFC_NEXT. eexists. eapply MS_NEXT. }

        unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
        eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
        unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
        rewrite ! (match_symbs_code_bundle_return ge_i ge_c) in CUR_SWITCH_STAR. rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
        eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
        clear BOUND2 CUR_SWITCH_STAR.
        unfold code_bundle_return. eapply star_trans. eapply code_mem_delta_correct. auto.
        { erewrite <- match_symbs_mem_delta_apply_wf. eapply DELTA_C. destruct MS0 as (MSYMB & _). auto. }
        2: ss.
        unfold unbundle. simpl. rename b into next.

        assert (CP_NEXT: (Genv.find_comp ge_c (Vptr next Ptrofs.zero)) = (comp_of fi_next)).
        { unfold Genv.find_comp. apply Genv.find_funct_ptr_iff in FINDF_C. setoid_rewrite FINDF_C. subst f_next. ss. }
        assert (EVRETV: eventval_to_val ge_c evretv = vretv).
        { destruct MS0 as (MSENV & MGENV). inv TR.
          eapply eventval_match_eventval_to_val. eapply match_symbs_eventval_match; eauto.
        }

        econs 2.
        { inv TR. eapply match_senv_eventval_match in H0. 2: destruct MS0 as (MS0 & _); apply MS0.
          eapply step_return_1.
          - eapply eventval_to_expr_val_eval. auto. eapply H0.
          - ss. assert (fd_cur = AST.Internal f_i_cur).
            { rewrite FINDFD in FINDF_I_CUR; clarify. }
            subst fd_cur. eapply sem_cast_proj_rettype. ss. eapply H0.
          - eapply FREENEXT.
        }
        ss. econs 2.
        { assert (CPEQ1: comp_of f_next = (Genv.find_comp ge_i (Vptr next Ptrofs.zero))).
          { subst f_next. unfold comp_of, gen_function. ss. unfold Genv.find_comp. setoid_rewrite INTERNAL. ss. }
          assert (CPEQ2: (comp_of (gen_function ge_i cnt_cur params_cur (get_id_tr ttr id_cur) f_i_cur)) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
          { unfold comp_of, gen_function. ss. unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. ss. }
          eapply step_returnstate.
          - move NPTR after EVRETV. i. rewrite EVRETV. apply NPTR. rr. rewrite CPEQ1 in H. setoid_rewrite CPEQ2 in H. apply H.
          - move TR after EVRETV. instantiate (1:=tr). inv TR. setoid_rewrite CPEQ2. rewrite CPEQ1. econs; auto.
            assert (fd_cur = AST.Internal f_i_cur).
            { rewrite FINDFD in FINDF_I_CUR; clarify. }
            subst fd_cur. ss. erewrite proj_rettype_to_type_rettype_of_type_eq. 2: eapply H0.
            eapply match_senv_eventval_match. 2: eapply H0. destruct MS0 as (MS0 & _). auto.
        }
        ss. econs 2.
        { eapply step_skip_or_continue_loop1. auto. }
        econs 2.
        { eapply step_skip_loop2. }
        { subst cst2. unfold code_bundle_trace. unfold Swhile. destruct MS0 as (MS0 & _).
          erewrite (match_symbs_switch_bundle_events _ _ MS0).
          setoid_rewrite <- CP_NEXT. unfold Genv.find_comp. setoid_rewrite FUN.
          replace (comp_of (Internal f_next)) with (comp_of f_next). econs 1. ss.
        }
        all: traceEq. traceEq.

      (** Case 3: Internal-External Call *)
      - assert (id = id_cur).
        { unfold match_cur_fun in MS2. desH MS2. rewrite MS7 in IDCUR. clarify. }
        subst id. rename id0 into id_next. 

        set (pretr ++ (id_cur, Bundle_call tr id_next (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: btr) as ttr in *.
        assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
        { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.invert_find_symbol in IDCUR. apply MSENV1 in IDCUR. auto. }
        assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
        { destruct MS2 as (MFUN0 & MFUN1). auto. }

        exploit WFC0. eapply FIND_CUR_C. eapply FIND_FUN_C. intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
        assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_call tr id_next (vals_to_eventvals ge_i vargs) (ef_sig ef) d) :: (get_id_tr btr id_cur)).
        { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
        assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
        { rewrite map_length. etransitivity. 2: eauto. unfold get_id_tr. admit. (* ez *) }
        destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).

        destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).
        hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply INV_CUR. eauto.
        intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
        rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
        assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
        { unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss. }

        hexploit switch_spec.
        { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
        { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3. }
        eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
        { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
        instantiate (1:=le).
        instantiate (1:= (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)).
        instantiate (1:=Sreturn None).
        intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).
        rename MEM into DELTA. move ECCASES after CUR_SWITCH_STAR.

        assert (FIND_F_C: Genv.find_funct ge_c (Vptr b_ext Ptrofs.zero) =
                            Some (External ef (list_typ_to_typelist (sig_args (ef_sig ef))) (rettype_to_type (sig_res (ef_sig ef))) (sig_cc (ef_sig ef)))).
        { unfold match_find_def in MS3. hexploit MS3.
          unfold Genv.find_funct in FINDF. rewrite pred_dec_true in FINDF; auto. unfold Genv.find_funct_ptr in FINDF. des_ifs. eapply Heq.
          eapply Senv.find_invert_symbol; eapply FINDB.
          intros. des_ifs. ss. rewrite pred_dec_true; auto. rewrite Genv.find_funct_ptr_iff. auto.
        }
        assert (COMP_F_C: comp_of f = Genv.find_comp ge_c (Vptr b_ext Ptrofs.zero)).
        { unfold Genv.type_of_call in INTRA. des_ifs.
          setoid_rewrite CP_CUR. apply Peqb_true_eq in Heq. rewrite Heq.
          unfold Genv.find_comp. setoid_rewrite FIND_F_C. ss.
        }

        desH ECCASES; cycle 1.

        (* Case 3-1: observable defined external calls *)
        { subst d. unfold mem_delta_apply_wf in DELTA. simpl in DELTA. inversion DELTA; clear DELTA. subst m1'.
          hexploit exists_vargs_vres. eapply MS0. eapply ECCASES. eauto. intros (vargs2 & vretv2 & EVALS & EXT2).
          eapply star_cut_middle. exists E0.
          eexists. split.
          { unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
            eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
            unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
            rewrite ! (match_symbs_code_bundle_call ge_i ge_c) in CUR_SWITCH_STAR.
            rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
            eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
            clear BOUND2 CUR_SWITCH_STAR.
            unfold code_bundle_call. eapply star_trans. eapply code_mem_delta_correct. auto.
            { unfold mem_delta_apply_wf. simpl. reflexivity. }
            2: ss. econs 2. 2: econs 1. 2: traceEq.
            eapply step_call. ss.
            { econs. assert (FSN_C: Senv.find_symbol ge_c id_next = Some b_ext).
              { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1. auto. }
              eapply eval_Evar_global.
              - unfold wf_env in WFC3. specialize (WFC3 id_next). rewrite FSN_C in WFC3. apply WFC3.
              - eapply FSN_C.
              - econs 2. ss.
            }
            { eapply EVALS. }
            { eapply FIND_F_C. }
            { ss. }
            { left. apply COMP_F_C. }
            { i. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_F_C. rewrite COMP_F_C in H. inv H. }
            { econs 1. ii. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_F_C. rewrite COMP_F_C in H. inv H. }
          }
          clear BOUND2 CUR_SWITCH_STAR.
          assert (COMP_SAME: comp_of f = comp_of ef).
          { rewrite COMP_F_C. unfold Genv.find_comp. rewrite FIND_F_C. ss. }
          do 2 eexists. split.
          { econs 2. eapply step_external_function. eapply EXT2.
            econs 2. eapply step_returnstate.
            { i. exfalso. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_SAME. rewrite COMP_SAME in H. ss. }
            { econs 1. rewrite COMP_SAME. unfold Genv.type_of_call. rewrite Pos.eqb_refl. ss. }
            econs 2. eapply step_skip_or_continue_loop1. left; auto. econs 2. eapply step_skip_loop2.
            econs 1. all: ss.
          }
          splits.
          2:{ unfold unbundle. ss. traceEq. }

          left. exists id_cur. split.
          { ss. splits; auto.
            - unfold wf_counters. split; auto.
              move WFC0 after COMP_SAME. ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
              unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
              exists b0. splits; auto.
              + eapply mem_valid_access_wunchanged_on. eapply WFC7.
                eapply store_wunchanged_on. eapply CNT_CUR_STORE. instantiate (1:= fun _ _ => True). ss.
              + destruct (Pos.eq_dec id id_cur).
                * subst id. assert (cnt_cur = cnt).
                  { rewrite WFC0 in CNTS_CUR. clarify. }
                  subst cnt. assert (b0 = cnt_cur_b).
                  { setoid_rewrite WFC6 in FIND_CNT_CUR. clarify. }
                  subst b0. assert (b = cur).
                  { rewrite FIND_CUR_C in H. clarify. }
                  subst b. assert (f0 = f).
                  { rewrite FINDF_C_CUR in H0. clarify. }
                  subst f0. ss. erewrite Mem.load_store_same. 2: eapply CNT_CUR_STORE.
                  ss. rewrite map_length. rewrite get_id_tr_app. ss.
                  rewrite Pos.eqb_refl. rewrite app_length. ss.
                  do 2 f_equal. apply nat64_int64_add_one.
                  admit. (*ez*)
                * ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
                  2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                      rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                      specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
                  }
                  rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. rewrite WFC8. auto.
            - hexploit wunchanged_on_exists_mem_free_list.
              { eapply store_wunchanged_on. eapply CNT_CUR_STORE. }
              eapply FREEENV. intros (m_f & FREE2). esplits. eapply FREE2.
              eapply wf_c_cont_wunchanged_on. eapply WFC1. 
              hexploit wunchanged_on_free_list_preserves. 2: eapply FREEENV. 2: eapply FREE2. 2: auto.
              eapply store_wunchanged_on. eapply CNT_CUR_STORE.
            - move WFC2 after COMP_SAME. unfold wf_c_stmt in *. i. rewrite CNTS_CUR in H. inv H. rename cnt into cnt_cur. ss.
            - move WFNB after COMP_SAME. unfold wf_c_nb in *. erewrite Mem.nextblock_store. eapply WFNB. eapply CNT_CUR_STORE.
          }
          { ss. exists k_c. splits; auto.
            2:{ unfold match_cur_fun. splits; eauto. }
            move MS1 after COMP_SAME. move MCNTS after COMP_SAME. destruct MS1 as (MM0 & MM1 & MM2).
            assert (m2 = m_i).
            { eapply known_obs_preserves_mem. eapply ECCASES. }
            subst m2. unfold match_mem. splits; auto.
            { eapply Mem.store_outside_inject. eapply MM0. 2: eapply CNT_CUR_STORE. ss. i.
              unfold match_cnts in MCNTS. eapply MCNTS. 3: eapply H. all: eauto.
            }
          }
        }

        (* Case 3-2: observables unknown external calls *)
        { hexploit external_call_unknowns_fo. eapply ECCASES. intros FO_I.
          hexploit external_call_unknowns_val_inject_list. eapply ECCASES. intros ARGS_INJ.
          move MS1 after ARGS_INJ. destruct MS1 as (MM0 & MM1 & MM2).
          hexploit mem_delta_apply_establish_inject_preprocess2.
          eapply MM0. eapply CNT_CUR_STORE. 2: eapply MM1. 2: eapply MM2.
          2: eapply DELTA.
          2:{ apply meminj_first_order_public_first_order. auto. }
          { clear CUR_SWITCH_STAR CNT_CUR_STORE. ii. erewrite match_symbs_meminj_public in H.
            2:{ destruct MS0 as (MS & _). apply MS. }
            unfold meminj_public in H. des_ifs.
            eapply Senv.find_invert_symbol in FIND_CNT_CUR. rewrite FIND_CNT_CUR in Heq. clarify.
          }
          intros (m_next0 & DELTA_C & INJ0).
          hexploit external_call_mem_inject_gen.
          { eapply match_symbs_symbols_inject. destruct MS0 as (MS & _). apply MS. }
          apply EC. apply INJ0. apply ARGS_INJ.
          intros (j2 & vres2 & m_next & EC2 & RET_INJ & INJ2 & UCH0 & UCH1 & INCR2 & INJ_SEP).
          assert (COMP_SAME: comp_of f = comp_of ef).
          { rewrite COMP_F_C. unfold Genv.find_comp. rewrite FIND_F_C. ss. }

          exists (State f stmt k0 e le m_next). split.
          { unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
            eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
            unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
            rewrite ! (match_symbs_code_bundle_call ge_i ge_c) in CUR_SWITCH_STAR.
            rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
            eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
            clear BOUND2 CUR_SWITCH_STAR CNT_CUR_STORE.
            unfold code_bundle_call. eapply star_trans. eapply code_mem_delta_correct. auto.
            { erewrite <- match_symbs_mem_delta_apply_wf. rewrite CP_CUR. eapply DELTA_C.
              destruct MS0 as (MSYMB & _). auto.
            }
            2: ss. unfold unbundle. simpl.
            econs 2. eapply step_call. ss.
            { econs. assert (FSN_C: Senv.find_symbol ge_c id_next = Some b_ext).
              { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply MSENV1. auto. }
              eapply eval_Evar_global.
              - unfold wf_env in WFC3. specialize (WFC3 id_next). rewrite FSN_C in WFC3. apply WFC3.
              - eapply FSN_C.
              - econs 2. ss.
            }
            { eapply match_symbs_vals_public_eval_to_vargs; auto.
              destruct MS0 as (MS0 & _). auto.
              eapply extcall_unkowns_vals_public; eauto.
            }
            { eapply FIND_F_C. }
            { ss. }
            { left. apply COMP_F_C. }
            { i. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_F_C. rewrite COMP_F_C in H. inv H. }
            { econs 1. ii. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_F_C. rewrite COMP_F_C in H. inv H. }

            econs 2. eapply step_external_function. eapply EC2.
            econs 2. eapply step_returnstate.
            { i. exfalso. unfold Genv.type_of_call in H. rewrite <- Pos.eqb_eq in COMP_SAME. rewrite COMP_SAME in H. ss. }
            { econs 1. rewrite COMP_SAME. unfold Genv.type_of_call. rewrite Pos.eqb_refl. ss. }
            econs 2. eapply step_skip_or_continue_loop1. left; auto. econs 2. eapply step_skip_loop2.
            econs 1. all: ss. traceEq.
          }

          clear CUR_SWITCH_STAR BOUND2.
          assert (UCH2: Mem.unchanged_on (fun b _ => forall b0 ofs0, (meminj_public ge_i) b0 <> Some (b, ofs0)) m_next0 m_next).
          { eapply Mem.unchanged_on_implies. eapply UCH1. ii. eapply H; eauto. }
          assert (UCH3: Mem.unchanged_on (fun b _ => Senv.invert_symbol ge_c b = None) m_next0 m_next).
          { eapply Mem.unchanged_on_implies. eapply UCH2. ss. i. unfold meminj_public. des_ifs. ii. clarify.
            apply Senv.invert_find_symbol in Heq. destruct MS0 as ((MSE1 & MSE2 & MSE3) & _). apply MSE2 in Heq.
            apply Senv.find_invert_symbol in Heq. setoid_rewrite H in Heq. ss.
          }
          eapply mem_unchanged_wunchanged in UCH3.
          hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros UCH4.
          hexploit wunchanged_on_trans. eapply UCH4. eapply UCH3. intros UCH5.
          hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros UCH6.
          hexploit wunchanged_on_trans. eapply UCH6. eapply UCH5. intros UCH7.
          clear UCH3 UCH4 UCH5 UCH6.
          left. exists id_cur. split.
          { ss. splits; auto.
            - unfold wf_counters. split; auto.
              move WFC0 after COMP_SAME. ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
              unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
              exists b0. splits; auto.
              + move MCNTS after COMP_SAME.
                eapply mem_valid_access_wunchanged_on. 2: eapply mem_unchanged_wunchanged; eapply UCH2.
                eapply mem_delta_apply_wf_valid_access. eapply DELTA_C.
                eapply mem_valid_access_wunchanged_on. 2: eapply store_wunchanged_on; eapply CNT_CUR_STORE.
                auto. instantiate (1:= fun _ _ => True). ss.
                ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto.
              + destruct (Pos.eq_dec id id_cur).
                * subst id. assert (cnt_cur = cnt).
                  { rewrite WFC0 in CNTS_CUR. clarify. }
                  subst cnt. assert (b0 = cnt_cur_b).
                  { setoid_rewrite WFC6 in FIND_CNT_CUR. clarify. }
                  subst b0. assert (b = cur).
                  { rewrite FIND_CUR_C in H. clarify. }
                  subst b. assert (f0 = f).
                  { rewrite FINDF_C_CUR in H0. clarify. }
                  subst f0. ss.
                  eapply Mem.load_unchanged_on. eapply UCH2.
                  { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
                  erewrite mem_delta_apply_wf_mem_load.
                  2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
                  2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
                  2:{ auto. }
                  erewrite Mem.load_store_same. 2: eapply CNT_CUR_STORE.
                  { ss. rewrite map_length. rewrite get_id_tr_app. ss. rewrite Pos.eqb_refl. rewrite app_length. ss.
                    do 2 f_equal. apply nat64_int64_add_one.
                    admit. (*ez*)
                  }
                * eapply Mem.load_unchanged_on. eapply UCH2.
                  { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
                  erewrite mem_delta_apply_wf_mem_load.
                  2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
                  2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
                  2:{ auto. }
                  ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
                  { rewrite WFC8. rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. auto. }
                  { left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                    rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                    specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
                  }

            - move FREEENV after COMP_SAME. move WFC1 after FREEENV. move WFC4 after FREEENV.
              hexploit wunchanged_on_exists_mem_free_list_2. eapply FREEENV.
              instantiate (2:=ge_c). eapply UCH7. ss.
              intros (m_c' & FREE2). esplits. eapply FREE2.
              eapply wf_c_cont_wunchanged_on_2. eapply WFC1.
              eapply wunchanged_on_free_list_preserves_gen. 2,3: eauto. auto.
            - move WFNB after UCH7. eapply wf_c_nb_wunchanged_on; eauto.
          }
          { ss. exists j2. splits; auto.
            2:{ unfold match_cur_fun. splits; eauto. }
            { unfold match_mem. splits; auto. move DELTA after UCH7. move EC after UCH7.
              eapply meminj_not_alloc_delta in MM2. 2: eapply DELTA.
              eapply meminj_not_alloc_external_call. eapply MM2. eauto.
            }
            { ii. assert (NINJP: (meminj_public ge_i) b = None).
              { move MCNTS after UCH7. specialize (MCNTS _ _ _ H H0 b ofs).
                destruct (meminj_public ge_i b) eqn:CASES; ss. exfalso.
                destruct p. move MM1 after UCH7. move INCR2 after UCH7.
                unfold inject_incr in *. hexploit MM1. apply CASES. hexploit INCR2. apply CASES.
                i. rewrite H1 in H2. clarify.
              }
              specialize (INJ_SEP _ _ _ NINJP H1). des. apply INJ_SEP0.
              hexploit Genv.genv_symb_range. eapply H0. intros RANGE.
              move WFNB before RANGE.
              hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros T1.
              hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros T2.
              eapply wunchanged_on_nextblock in T1, T2. revert_until NINJP. clear. i.
              unfold wf_c_nb in WFNB. unfold Mem.valid_block. eapply Plt_Ple_trans. eauto.
              etransitivity. eapply WFNB. etransitivity; eauto.
            }
          }
        }

      (** Case 4: Builtins *)
      - assert (id = id_cur).
        { unfold match_cur_fun in MS2. desH MS2. rewrite MS7 in IDCUR. clarify. }
        subst id.

        set (pretr ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: btr) as ttr in *.
        assert (FIND_CUR_C: Genv.find_symbol ge_c id_cur = Some cur).
        { destruct MS0 as ((MSENV0 & MSENV1 & MSENV2) & MGENV). apply Genv.invert_find_symbol in IDCUR. apply MSENV1 in IDCUR. auto. }
        assert (FIND_FUN_C: Genv.find_funct_ptr ge_c cur = Some (Internal f)).
        { destruct MS2 as (MFUN0 & MFUN1). auto. }

        exploit WFC0. eapply FIND_CUR_C. eapply FIND_FUN_C. intros (cnt_cur & CNTS_CUR & WF_CNT_CUR).
        assert (CUR_TR: get_id_tr ttr id_cur = (get_id_tr pretr id_cur) ++ (id_cur, Bundle_builtin tr ef (vals_to_eventvals ge_i vargs) d) :: (get_id_tr btr id_cur)).
        { subst ttr. clear. rewrite get_id_tr_app. rewrite get_id_tr_cons. ss. rewrite Pos.eqb_refl. auto. }
        assert (BOUND2: Z.of_nat (Datatypes.length (map (fun ib : ident * bundle_event => code_bundle_event ge_i (comp_of f) (snd ib)) (get_id_tr ttr id_cur))) < Int64.modulus).
        { rewrite map_length. etransitivity. 2: eauto. unfold get_id_tr. admit. (* ez *) }
        destruct WF_CNT_CUR as (CNT_CUR_NPUB & cnt_cur_b & FIND_CNT_CUR & CNT_CUR_MEM_VA & CNT_CUR_MEM_LOAD).

        destruct MS2 as (FINDF_C_CUR & (f_i_cur & FINDF_I_CUR) & INV_CUR).
        hexploit cur_fun_def. eapply FINDF_C_CUR. eapply FINDF_I_CUR. eapply INV_CUR. eauto.
        intros (cnt_cur0 & params_cur & CNT_CUR0 & PARAMS_CUR & CUR_F).
        rewrite CNTS_CUR in CNT_CUR0. inversion CNT_CUR0. subst cnt_cur0. clear CNT_CUR0.
        assert (CP_CUR: (comp_of f) = (Genv.find_comp ge_i (Vptr cur Ptrofs.zero))).
        { unfold Genv.find_comp. setoid_rewrite FINDF_I_CUR. subst f. ss. }

        hexploit switch_spec.
        { subst ttr. rewrite CUR_TR in BOUND2. rewrite map_app in BOUND2. ss. eapply BOUND2. }
        { unfold wf_env in WFC3. specialize (WFC3 cnt_cur). des_ifs. eapply WFC3. }
        eapply FIND_CNT_CUR. eapply CNT_CUR_MEM_VA.
        { rewrite CNT_CUR_MEM_LOAD. rewrite map_length. auto. }
        instantiate (1:=le).
        instantiate (1:= (Kloop1 (Ssequence (Sifthenelse one_expr Sskip Sbreak) (switch_bundle_events ge_c cnt_cur (comp_of f) (get_id_tr ttr id_cur))) Sskip k0)).
        instantiate (1:=Sreturn None).
        intros (m_cu & CNT_CUR_STORE & CUR_SWITCH_STAR).
        assert (COMP_SAME: comp_of f = comp_of ef).
        { rewrite ALLOWED. apply CP_CUR. }
        rename MEM into DELTA. move ECCASES after CUR_SWITCH_STAR.

        desH ECCASES; cycle 1.

        (* Case 4-1: observable defined external calls *)
        { subst d. unfold mem_delta_apply_wf in DELTA. simpl in DELTA. inversion DELTA; clear DELTA. subst m1'.
          hexploit exists_vargs_vres_2. eapply MS0. eapply ECCASES. eauto. intros (vargs2 & vretv2 & EVALS & EXT2).
          eapply star_cut_middle. exists E0.
          eexists. split.
          { unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
            eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
            unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
            rewrite ! (match_symbs_code_bundle_builtin ge_i ge_c) in CUR_SWITCH_STAR.
            rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
            eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
            clear BOUND2 CUR_SWITCH_STAR.
            unfold code_bundle_builtin. eapply star_trans. eapply code_mem_delta_correct. auto.
            { unfold mem_delta_apply_wf. simpl. reflexivity. }
            econs 1. ss.
          }
          clear BOUND2 CUR_SWITCH_STAR.
          do 2 eexists. split. econs 2.
          { eapply step_builtin. ss.
            { eapply EVALS. }
            { auto. }
            { eapply EXT2. }
          }
          econs 2. eapply step_skip_or_continue_loop1. left; auto.
          econs 2. eapply step_skip_loop2.
          econs 1. all: ss.
          splits.
          2:{ unfold unbundle. ss. traceEq. }

          left. exists id_cur. split.
          { splits; auto.
            - unfold wf_counters. split; auto.
              move WFC0 after COMP_SAME. ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
              unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
              exists b0. splits; auto.
              + eapply mem_valid_access_wunchanged_on. eapply WFC7.
                eapply store_wunchanged_on. eapply CNT_CUR_STORE. instantiate (1:= fun _ _ => True). ss.
              + destruct (Pos.eq_dec id id_cur).
                * subst id. assert (cnt_cur = cnt).
                  { rewrite WFC0 in CNTS_CUR. clarify. }
                  subst cnt. assert (b0 = cnt_cur_b).
                  { setoid_rewrite WFC6 in FIND_CNT_CUR. clarify. }
                  subst b0. assert (b = cur).
                  { rewrite FIND_CUR_C in H. clarify. }
                  subst b. assert (f0 = f).
                  { rewrite FINDF_C_CUR in H0. clarify. }
                  subst f0. ss. erewrite Mem.load_store_same. 2: eapply CNT_CUR_STORE.
                  ss. rewrite map_length. rewrite get_id_tr_app. ss.
                  rewrite Pos.eqb_refl. rewrite app_length. ss.
                  do 2 f_equal. apply nat64_int64_add_one.
                  admit. (*ez*)
                * ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
                  2:{ left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                      rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                      specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
                  }
                  rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. rewrite WFC8. auto.
            - hexploit wunchanged_on_exists_mem_free_list.
              { eapply store_wunchanged_on. eapply CNT_CUR_STORE. }
              eapply FREEENV. intros (m_f & FREE2). esplits. eapply FREE2.
              eapply wf_c_cont_wunchanged_on. eapply WFC1. 
              hexploit wunchanged_on_free_list_preserves. 2: eapply FREEENV. 2: eapply FREE2. 2: auto.
              eapply store_wunchanged_on. eapply CNT_CUR_STORE.
            - move WFC2 after COMP_SAME. unfold wf_c_stmt in *. i. rewrite CNTS_CUR in H. inv H. rename cnt into cnt_cur. ss.
            - move WFNB after COMP_SAME. unfold wf_c_nb in *. erewrite Mem.nextblock_store. eapply WFNB. eapply CNT_CUR_STORE.
          }
          { ss. exists k_c. splits; auto.
            2:{ unfold match_cur_fun. splits; eauto. }
            move MS1 after COMP_SAME. move MCNTS after COMP_SAME. destruct MS1 as (MM0 & MM1 & MM2).
            assert (m2 = m_i).
            { eapply known_obs_preserves_mem. eapply ECCASES. }
            subst m2. unfold match_mem. splits; auto.
            { eapply Mem.store_outside_inject. eapply MM0. 2: eapply CNT_CUR_STORE. ss. i.
              unfold match_cnts in MCNTS. eapply MCNTS. 3: eapply H. all: eauto.
            }
          }
        }

        (* Case 4-2: observables unknown external calls *)
        { hexploit external_call_unknowns_fo. eapply ECCASES. intros FO_I.
          hexploit external_call_unknowns_val_inject_list. eapply ECCASES. intros ARGS_INJ.
          move MS1 after ARGS_INJ. destruct MS1 as (MM0 & MM1 & MM2).
          hexploit mem_delta_apply_establish_inject_preprocess2.
          eapply MM0. eapply CNT_CUR_STORE. 2: eapply MM1. 2: eapply MM2.
          2: eapply DELTA.
          2:{ apply meminj_first_order_public_first_order. auto. }
          { clear CUR_SWITCH_STAR CNT_CUR_STORE. ii. erewrite match_symbs_meminj_public in H.
            2:{ destruct MS0 as (MS & _). apply MS. }
            unfold meminj_public in H. des_ifs.
            eapply Senv.find_invert_symbol in FIND_CNT_CUR. rewrite FIND_CNT_CUR in Heq. clarify.
          }
          intros (m_next0 & DELTA_C & INJ0).
          hexploit external_call_mem_inject_gen.
          { eapply match_symbs_symbols_inject. destruct MS0 as (MS & _). apply MS. }
          apply EC. apply INJ0. apply ARGS_INJ.
          intros (j2 & vres2 & m_next & EC2 & RET_INJ & INJ2 & UCH0 & UCH1 & INCR2 & INJ_SEP).

          exists (State f stmt k0 e le m_next). split.
          { unfold wf_c_stmt in WFC2. specialize (WFC2 _ CNTS_CUR). subst stmt.
            eapply star_trans. eapply code_bundle_trace_spec. 2: ss.
            unfold switch_bundle_events at 1. rewrite CUR_TR at 1. rewrite map_app. simpl.
            rewrite ! (match_symbs_code_bundle_builtin ge_i ge_c) in CUR_SWITCH_STAR.
            rewrite ! (match_symbs_code_bundle_events ge_i ge_c) in CUR_SWITCH_STAR.
            eapply star_trans. eapply CUR_SWITCH_STAR. 2: ss. 2,3: destruct MS0 as (MS & _); auto.
            clear BOUND2 CUR_SWITCH_STAR CNT_CUR_STORE.
            unfold code_bundle_builtin. eapply star_trans. eapply code_mem_delta_correct. auto.
            { erewrite <- match_symbs_mem_delta_apply_wf. rewrite CP_CUR. eapply DELTA_C.
              destruct MS0 as (MSYMB & _). auto.
            }
            2: ss. unfold unbundle. simpl.
            econs 2. eapply step_builtin.
            { eapply match_symbs_vals_public_eval_to_vargs_2; auto.
              destruct MS0 as (MS0 & _). auto. eapply extcall_unkowns_vals_public; eauto.
            }
            { auto. }
            { eapply EC2. }
            econs 2. eapply step_skip_or_continue_loop1. left; auto.
            econs 2. eapply step_skip_loop2. econs 1. all: ss. traceEq.
          }

          clear CUR_SWITCH_STAR BOUND2.
          assert (UCH2: Mem.unchanged_on (fun b _ => forall b0 ofs0, (meminj_public ge_i) b0 <> Some (b, ofs0)) m_next0 m_next).
          { eapply Mem.unchanged_on_implies. eapply UCH1. ii. eapply H; eauto. }
          assert (UCH3: Mem.unchanged_on (fun b _ => Senv.invert_symbol ge_c b = None) m_next0 m_next).
          { eapply Mem.unchanged_on_implies. eapply UCH2. ss. i. unfold meminj_public. des_ifs. ii. clarify.
            apply Senv.invert_find_symbol in Heq. destruct MS0 as ((MSE1 & MSE2 & MSE3) & _). apply MSE2 in Heq.
            apply Senv.find_invert_symbol in Heq. setoid_rewrite H in Heq. ss.
          }
          eapply mem_unchanged_wunchanged in UCH3.
          hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros UCH4.
          hexploit wunchanged_on_trans. eapply UCH4. eapply UCH3. intros UCH5.
          hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros UCH6.
          hexploit wunchanged_on_trans. eapply UCH6. eapply UCH5. intros UCH7.
          clear UCH3 UCH4 UCH5 UCH6.
          left. exists id_cur. split.
          { ss. splits; auto.
            - unfold wf_counters. split; auto.
              move WFC0 after COMP_SAME. ii. specialize (WFC0 _ _ _ H H0). des. exists cnt. splits; auto.
              unfold wf_counter in WFC5. des. unfold wf_counter. splits; auto.
              exists b0. splits; auto.
              + move MCNTS after COMP_SAME.
                eapply mem_valid_access_wunchanged_on. 2: eapply mem_unchanged_wunchanged; eapply UCH2.
                eapply mem_delta_apply_wf_valid_access. eapply DELTA_C.
                eapply mem_valid_access_wunchanged_on. 2: eapply store_wunchanged_on; eapply CNT_CUR_STORE.
                auto. instantiate (1:= fun _ _ => True). ss.
                ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto.
              + destruct (Pos.eq_dec id id_cur).
                * subst id. assert (cnt_cur = cnt).
                  { rewrite WFC0 in CNTS_CUR. clarify. }
                  subst cnt. assert (b0 = cnt_cur_b).
                  { setoid_rewrite WFC6 in FIND_CNT_CUR. clarify. }
                  subst b0. assert (b = cur).
                  { rewrite FIND_CUR_C in H. clarify. }
                  subst b. assert (f0 = f).
                  { rewrite FINDF_C_CUR in H0. clarify. }
                  subst f0. ss.
                  eapply Mem.load_unchanged_on. eapply UCH2.
                  { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
                  erewrite mem_delta_apply_wf_mem_load.
                  2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
                  2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
                  2:{ auto. }
                  erewrite Mem.load_store_same. 2: eapply CNT_CUR_STORE.
                  { ss. rewrite map_length. rewrite get_id_tr_app. ss. rewrite Pos.eqb_refl. rewrite app_length. ss.
                    do 2 f_equal. apply nat64_int64_add_one.
                    admit. (*ez*)
                  }
                * eapply Mem.load_unchanged_on. eapply UCH2.
                  { ss. i. erewrite match_symbs_meminj_public. 2: eapply MS0. eapply meminj_public_not_public_not_mapped; eauto. }
                  erewrite mem_delta_apply_wf_mem_load.
                  2:{ erewrite match_symbs_mem_delta_apply_wf in DELTA_C. eapply DELTA_C. eapply MS0. }
                  2:{ eapply Genv.find_invert_symbol in WFC6. eapply WFC6. }
                  2:{ auto. }
                  ss. erewrite Mem.load_store_other. 2: eapply CNT_CUR_STORE.
                  { rewrite WFC8. rewrite get_id_tr_app. ss. apply Pos.eqb_neq in n. rewrite n. rewrite app_nil_r. auto. }
                  { left. ii. clarify. apply Genv.find_invert_symbol in FIND_CNT_CUR, WFC6.
                    rewrite FIND_CNT_CUR in WFC6. clarify. rename cnt into cnt_cur.
                    specialize (CNT_INJ _ _ _ CNTS_CUR WFC0). clarify.
                  }

            - move FREEENV after COMP_SAME. move WFC1 after FREEENV. move WFC4 after FREEENV.
              hexploit wunchanged_on_exists_mem_free_list_2. eapply FREEENV.
              instantiate (2:=ge_c). eapply UCH7. ss.
              intros (m_c' & FREE2). esplits. eapply FREE2.
              eapply wf_c_cont_wunchanged_on_2. eapply WFC1.
              eapply wunchanged_on_free_list_preserves_gen. 2,3: eauto. auto.
            - move WFNB after UCH7. eapply wf_c_nb_wunchanged_on; eauto.
          }
          { ss. exists j2. splits; auto.
            2:{ unfold match_cur_fun. splits; eauto. }
            { unfold match_mem. splits; auto. move DELTA after UCH7. move EC after UCH7.
              eapply meminj_not_alloc_delta in MM2. 2: eapply DELTA.
              eapply meminj_not_alloc_external_call. eapply MM2. eauto.
            }
            { ii. assert (NINJP: (meminj_public ge_i) b = None).
              { move MCNTS after UCH7. specialize (MCNTS _ _ _ H H0 b ofs).
                destruct (meminj_public ge_i b) eqn:CASES; ss. exfalso.
                destruct p. move MM1 after UCH7. move INCR2 after UCH7.
                unfold inject_incr in *. hexploit MM1. apply CASES. hexploit INCR2. apply CASES.
                i. rewrite H1 in H2. clarify.
              }
              specialize (INJ_SEP _ _ _ NINJP H1). des. apply INJ_SEP0.
              hexploit Genv.genv_symb_range. eapply H0. intros RANGE.
              move WFNB before RANGE.
              hexploit mem_delta_apply_wf_wunchanged_on. eapply DELTA_C. intros T1.
              hexploit store_wunchanged_on. eapply CNT_CUR_STORE. intros T2.
              eapply wunchanged_on_nextblock in T1, T2. revert_until NINJP. clear. i.
              unfold wf_c_nb in WFNB. unfold Mem.valid_block. eapply Plt_Ple_trans. eauto.
              etransitivity. eapply WFNB. etransitivity; eauto.
            }
          }
        }

      (** Case 5: Cross Call External 1 *)
      -


        TODO




    Admitted.

    Lemma ir_to_clight_aux
          (ge_i: Asm.genv) (ge_c: Clight.genv)
          (pretr: bundle_trace)
          pist ist
          (PREIR: istar (ir_step) ge_i pist pretr ist)
          pcst cst
          (PREC: star step1 ge_c pcst (unbundle_trace pretr) cst)
          ttr cnts pars k id
          (BOUND: Z.of_nat (Datatypes.length ttr) < Int64.modulus)
          (WFC: wf_c_state ge_c pretr ttr cnts id cst)
          (MS: match_state ge_i ge_c k ttr cnts pars id ist cst)
          btr ist'
          (TOTAL: ttr = pretr ++ btr)
          (STAR: istar (ir_step) ge_i ist btr ist')
      :
      exists cst', star step1 ge_c cst (unbundle_trace btr) cst'.
    Proof.
      revert pretr PREIR cst PREC k id WFC MS TOTAL. induction STAR; intros.
      { ss. eexists. econs 1. }
      rename H into STEP. subst t. ss.
      hexploit ir_to_clight_step; eauto. intros; des.
      - hexploit IHSTAR.
        { eapply istar_trans. eapply PREIR. econs 2. eapply STEP. econs 1. all: ss. }
        { rewrite unbundle_trace_app. eapply star_trans. eapply PREC. eapply H. ss. rewrite app_nil_r. ss. }
        eauto. eauto.
        { rewrite <- app_assoc. ss. }
        intros (cst' & INDSTAR).
        exists cst'. eapply star_trans. eapply H. eapply INDSTAR. ss.
      - subst s2. inv STAR.
        + ss. rewrite app_nil_r. eauto.
        + inv H0.
    Qed.

    Theorem ir_to_clight
          (ge_i: Asm.genv) (ge_c: Clight.genv)
          (WFCG: wf_c_genv ge_c)
          ist cst
          ttr cnts k id
          (WFC: wf_c_state ge_c [] ttr cnts id cst)
          (MS: match_state ge_i ge_c k ttr cnts id ist cst)
          ist'
          (STAR: istar (ir_step) ge_i ist ttr ist')
      :
      exists cst', star step1 ge_c cst (unbundle_trace ttr) cst'.
    Proof. eapply ir_to_clight_aux. 4,5,6,7: eauto. all: eauto. econs 1. ss. econs 1. Qed.

  End PROOF.

(* Genv.initmem_inject: forall [F V : Type] {CF : has_comp F} (p : AST.program F V) [m : mem], Genv.init_mem p = Some m -> Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m *)
(* Genv.alloc_globals_neutral: *)
(*   forall [F V : Type] {CF : has_comp F} (ge : Genv.t F V) [thr : block], *)
(*   (forall (id : ident) (b : block), Genv.find_symbol ge id = Some b -> Plt b thr) -> *)
(*   forall (gl : list (ident * globdef F V)) (m m' : mem), Genv.alloc_globals ge m gl = Some m' -> Mem.inject_neutral thr m -> Ple (Mem.nextblock m') thr -> Mem.inject_neutral thr m' *)



  Section STEPPROP.

    (* Variant external_call_event_match_common *)
    (*         (ef: external_function) (ev: event) (ge: Senv.t) (cp: compartment) (m1: mem) *)
    (*   : val -> mem -> Prop := *)
    (*   | ext_match_vload *)
    (*       ch *)
    (*       (EF: ef = EF_vload ch) *)
    (*       id ofs evv *)
    (*       (EV: ev = Event_vload ch id ofs evv) *)
    (*       b res m2 *)
    (*       (SEM: volatile_load_sem ch ge cp (Vptr b ofs :: nil) m1 (ev :: nil) res m2) *)
    (*     : *)
    (*     external_call_event_match_common ef ev ge cp m1 res m2 *)
    (*   | ext_match_vstore *)
    (*       ch *)
    (*       (EF: ef = EF_vstore ch) *)
    (*       id ofs evv *)
    (*       (EV: ev = Event_vstore ch id ofs evv) *)
    (*       b argv m2 *)
    (*       (SEM: volatile_store_sem ch ge cp (Vptr b ofs :: argv :: nil) m1 (ev :: nil) Vundef m2) *)
    (*     : *)
    (*     external_call_event_match_common ef ev ge cp m1 Vundef m2 *)
    (*   | ext_match_annot *)
    (*       len text targs *)
    (*       (EF: ef = EF_annot len text targs) *)
    (*       evargs *)
    (*       (EV: ev = Event_annot text evargs) *)
    (*       vargs m2 *)
    (*       (SEM: extcall_annot_sem text targs ge cp vargs m1 (ev :: nil) Vundef m2) *)
    (*     : *)
    (*     external_call_event_match_common ef ev ge cp m1 Vundef m2 *)
    (*   | ext_match_external *)
    (*       name excp sg *)
    (*       (EF: ef = EF_external name excp sg) *)
    (*       evname evargs evres *)
    (*       (EV: ev = Event_syscall evname evargs evres) *)
    (*       vargs vres m2 *)
    (*       (SEM: external_functions_sem name sg ge cp vargs m1 (ev :: nil) vres m2) *)
    (*       (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs) *)
    (*     : *)
    (*     external_call_event_match_common ef ev ge cp m1 vres m2 *)
    (*   | ext_match_builtin *)
    (*       name sg *)
    (*       (EF: (ef = EF_builtin name sg) \/ (ef = EF_runtime name sg)) *)
    (*       evname evargs evres *)
    (*       (EV: ev = Event_syscall evname evargs evres) *)
    (*       (ISEXT: Builtins.lookup_builtin_function name sg = None) *)
    (*       vargs vres m2 *)
    (*       (SEM: external_functions_sem name sg ge cp vargs m1 (ev :: nil) vres m2) *)
    (*       (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs) *)
    (*     : *)
    (*     external_call_event_match_common ef ev ge cp m1 vres m2 *)
    (*   | ext_match_inline_asm *)
    (*       txt sg strs *)
    (*       (EF: ef = EF_inline_asm txt sg strs) *)
    (*       evname evargs evres *)
    (*       (EV: ev = Event_syscall evname evargs evres) *)
    (*       vargs vres m2 *)
    (*       (SEM: inline_assembly_sem txt sg ge cp vargs m1 (ev :: nil) vres m2) *)
    (*       (ARGS: eventval_list_match ge evargs sg.(sig_args) vargs) *)
    (*     : *)
    (*     external_call_event_match_common ef ev ge cp m1 vres m2 *)
    (* . *)

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


  (* Section WELLFORMED. *)

  (*   Definition empty_te: temp_env := PTree.empty val. *)

  (*   (* Variant sf_cont_type : Type := | sf_cont: block -> signature -> sf_cont_type. *) *)
  (*   Variant sf_cont_type : Type := | sf_cont: block -> sf_cont_type. *)
  (*   Definition sf_conts := list sf_cont_type. *)

  (*   (* wf_sem: from asm, wf_st: proof invariant for Clight states *) *)
  (*   Inductive from_info_asm_wf (ge: Asm.genv) : block -> mem -> sf_conts -> itrace -> Prop := *)
  (*   | from_info_asm_wf_intra_call_external *)
  (*       cur m1 sf ev ik tl *)
  (*       cp *)
  (*       (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero)) *)
  (*       ef res m2 *)
  (*       (EXTEV: external_call_event_match_common ef ev ge cp m1 res m2) *)
  (*       fb *)
  (*       (IK: ik = info_external fb (ef_sig ef)) *)
  (*       fid *)
  (*       (INV: Genv.invert_symbol ge fb = Some fid) *)
  (*       (ISEXT: Genv.find_funct_ptr ge fb = Some (AST.External ef)) *)
  (*       (ALLOWED: Genv.allowed_call ge cp (Vptr fb Ptrofs.zero)) *)
  (*       (INTRA: Genv.type_of_call ge cp (Genv.find_comp ge (Vptr fb Ptrofs.zero)) <> Genv.CrossCompartmentCall) *)
  (*       (NEXT: from_info_asm_wf ge cur m2 sf tl) *)
  (*     : *)
  (*     from_info_asm_wf ge cur m1 sf ((ev, ik) :: tl) *)
  (*   | from_info_asm_wf_builtin *)
  (*       cur m1 sf ev ik tl *)
  (*       cp *)
  (*       (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero)) *)
  (*       ef res m2 *)
  (*       (EXT: external_call_event_match_common ef ev ge cp m1 res m2) *)
  (*       (IK: ik = info_builtin ef) *)
  (*       (NEXT: from_info_asm_wf ge cur m2 sf tl) *)
  (*     : *)
  (*     from_info_asm_wf ge cur m1 sf ((ev, ik) :: tl) *)
  (*   | from_info_asm_wf_cross_call_internal *)
  (*       cur m1 sf ev ik tl *)
  (*       cp *)
  (*       (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero)) *)
  (*       cp' fid evargs *)
  (*       (EV: ev = Event_call cp cp' fid evargs) *)
  (*       sg *)
  (*       (IK: ik = info_call not_cross_ext sg) *)
  (*       b *)
  (*       (FINDB: Genv.find_symbol ge fid = Some b) *)
  (*       fd *)
  (*       (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd) *)
  (*       (CP': cp' = comp_of fd) *)
  (*       (CROSS: Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall) *)
  (*       args *)
  (*       (NPTR: Forall not_ptr args) *)
  (*       (ALLOW: Genv.allowed_cross_call ge cp (Vptr b Ptrofs.zero)) *)
  (*       (ESM: eventval_list_match ge evargs (sig_args sg) args) *)
  (*       callee_f *)
  (*       (INTERNAL: fd = AST.Internal callee_f) *)
  (*       (* TODO: separate this;  *)
  (*          might be better to upgrade Asm semantics to actually refer to its fn_sig. *)
  (*          Note that it's not possible to recover Clight fun type data from trace since *)
  (*          there can be conflicts, since Asm semantics actually allows non-fixed sigs. *)
  (*        *) *)
  (*       (SIG: sg = Asm.fn_sig callee_f) *)
  (*       (* internal call: memory changes in Clight-side, so need inj-relation *) *)
  (*       (NEXT: from_info_asm_wf ge b m1 ((sf_cont cur) :: sf) tl) *)
  (*     : *)
  (*     from_info_asm_wf ge cur m1 sf ((ev, ik) :: tl) *)
  (*   | from_info_asm_wf_cross_return_internal *)
  (*       cur m1 ev ik tl *)
  (*       cp *)
  (*       (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero)) *)
  (*       cp_c evres *)
  (*       (EV: ev = Event_return cp_c cp evres) *)
  (*       sg *)
  (*       (IK: ik = info_return sg) *)
  (*       cur_f *)
  (*       (INTERNAL: Genv.find_funct_ptr ge cur = Some (AST.Internal cur_f)) *)
  (*       (* TODO: separate this *) *)
  (*       (SIG: sg = Asm.fn_sig cur_f) *)
  (*       (CROSS: Genv.type_of_call ge cp_c cp = Genv.CrossCompartmentCall) *)
  (*       res *)
  (*       (EVM: eventval_match ge evres (proj_rettype (sig_res sg)) res) *)
  (*       (NPTR: not_ptr res) *)
  (*       b_c sf_tl *)
  (*       (CPC: cp_c = Genv.find_comp ge (Vptr b_c Ptrofs.zero)) *)
  (*       (* internal return: memory changes in Clight-side, so need inj-relation *) *)
  (*       (NEXT: from_info_asm_wf ge b_c m1 sf_tl tl) *)
  (*     : *)
  (*     from_info_asm_wf ge cur m1 ((sf_cont b_c) :: sf_tl) ((ev, ik) :: tl) *)
  (*   | from_info_asm_wf_cross_call_external1 *)
  (*       (* early cut at call event *) *)
  (*       cur m1 sf ev ik *)
  (*       cp *)
  (*       (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero)) *)
  (*       cp' fid evargs *)
  (*       (EV: ev = Event_call cp cp' fid evargs) *)
  (*       sg *)
  (*       (IK: ik = info_call is_cross_ext sg) *)
  (*       b *)
  (*       (FINDB: Genv.find_symbol ge fid = Some b) *)
  (*       fd *)
  (*       (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd) *)
  (*       (CP': cp' = comp_of fd) *)
  (*       (CROSS: Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall) *)
  (*       args *)
  (*       (NPTR: Forall not_ptr args) *)
  (*       (ALLOW: Genv.allowed_cross_call ge cp (Vptr b Ptrofs.zero)) *)
  (*       (ESM: eventval_list_match ge evargs (sig_args sg) args) *)
  (*       ef *)
  (*       (EXTERNAL: fd = AST.External ef) *)
  (*       (* TODO: separate this *) *)
  (*       (SIG: sg = ef_sig ef) *)
  (*     : *)
  (*     from_info_asm_wf ge cur m1 sf ((ev, ik) :: nil) *)
  (*   | from_info_asm_wf_cross_call_external2 *)
  (*       (* early cut at call-ext_call event *) *)
  (*       cur m1 sf ev1 ik1 *)
  (*       cp *)
  (*       (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero)) *)
  (*       cp' fid evargs *)
  (*       (EV: ev1 = Event_call cp cp' fid evargs) *)
  (*       sg *)
  (*       (IK: ik1 = info_call is_cross_ext sg) *)
  (*       b *)
  (*       (FINDB: Genv.find_symbol ge fid = Some b) *)
  (*       fd *)
  (*       (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd) *)
  (*       (CP': cp' = comp_of fd) *)
  (*       (CROSS: Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall) *)
  (*       args *)
  (*       (NPTR: Forall not_ptr args) *)
  (*       (ALLOW: Genv.allowed_cross_call ge cp (Vptr b Ptrofs.zero)) *)
  (*       (ESM: eventval_list_match ge evargs (sig_args sg) args) *)
  (*       ef *)
  (*       (EXTERNAL: fd = AST.External ef) *)
  (*       (* TODO: separate this *) *)
  (*       (SIG: sg = ef_sig ef) *)
  (*       (* external call part *) *)
  (*       tr vres m2 *)
  (*       (EXTCALL: external_call ef ge cp args m1 tr vres m2) *)
  (*       itr *)
  (*       (INFO: itr = map (fun e => (e, info_external b (ef_sig ef))) tr) *)
  (*     : *)
  (*     from_info_asm_wf ge cur m1 sf ((ev1, ik1) :: itr) *)
  (*   | from_info_asm_wf_cross_call_external3 *)
  (*       (* full call-ext_call-return event *) *)
  (*       cur m1 sf ev1 ik1 *)
  (*       cp *)
  (*       (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero)) *)
  (*       cp' fid evargs *)
  (*       (EV: ev1 = Event_call cp cp' fid evargs) *)
  (*       sg *)
  (*       (IK: ik1 = info_call is_cross_ext sg) *)
  (*       b *)
  (*       (FINDB: Genv.find_symbol ge fid = Some b) *)
  (*       fd *)
  (*       (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd) *)
  (*       (CP': cp' = comp_of fd) *)
  (*       (CROSS: Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall) *)
  (*       args *)
  (*       (NPTR: Forall not_ptr args) *)
  (*       (ALLOW: Genv.allowed_cross_call ge cp (Vptr b Ptrofs.zero)) *)
  (*       (ESM: eventval_list_match ge evargs (sig_args sg) args) *)
  (*       ef *)
  (*       (EXTERNAL: fd = AST.External ef) *)
  (*       (* TODO: separate this *) *)
  (*       (SIG: sg = ef_sig ef) *)
  (*       (* external call part *) *)
  (*       tr vres m2 *)
  (*       (EXTCALL: external_call ef ge cp args m1 tr vres m2) *)
  (*       itr *)
  (*       (INFO: itr = map (fun e => (e, info_external b (ef_sig ef))) tr) *)
  (*       (* return part *) *)
  (*       ev3 ik3 tl *)
  (*       evres *)
  (*       (EV: ev3 = Event_return cp cp' evres) *)
  (*       sg *)
  (*       (IK: ik3 = info_return sg) *)
  (*       (EVM: eventval_match ge evres (proj_rettype (sig_res sg)) vres) *)
  (*       (NPTR: not_ptr vres) *)
  (*       (NEXT: from_info_asm_wf ge cur m2 sf tl) *)
  (*     : *)
  (*     from_info_asm_wf ge cur m1 sf ((ev1, ik1) :: (itr ++ ((ev3, ik3) :: tl))) *)
  (*   . *)

  (*   (* TODO *) *)
  (*   (* we need a more precise invariant for the proof; counters, mem_inj, env, cont, state *) *)

  (* End WELLFORMED. *)


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
