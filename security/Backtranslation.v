Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import Tactics.
Require Import riscV.Asm.
Require Import BtBasics BtInfoAsm MemoryDelta MemoryWeak.
Require Import Ctypes Clight.



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

  (* Ltac simpl_expr' := *)
  (*   unfold type_counter; unfold type_bool; simpl; simpl_expr. *)

  (* Ltac take_step' := econstructor; [econstructor; simpl_expr' | | traceEq]; simpl. *)

  (* Lemma switch_clause_spec (ge: genv) (cnt: ident) f e le m b k (n: int64) (n': Z) s_then s_else: *)
  (*   let cp := comp_of f in *)
  (*   e ! cnt = None -> *)
  (*   Genv.find_symbol ge cnt = Some b -> *)
  (*   Mem.valid_access m Mint64 b 0 Writable (Some cp) -> *)
  (*   Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong n) -> *)
  (*   if Int64.eq n (Int64.repr n') then *)
  (*     exists m', *)
  (*       Mem.storev Mint64 m (Vptr b Ptrofs.zero) (Vlong (Int64.add n Int64.one)) cp = Some m' /\ *)
  (*         star (step1) ge (State f (switch_clause cnt n' s_then s_else) k e le m) E0 (State f s_then k e le m') *)
  (*   else *)
  (*     star (step1) ge (State f (switch_clause cnt n' s_then s_else) k e le m) E0 (State f s_else k e le m). *)
  (* Proof. *)
  (*   intros; subst cp. *)
  (*   destruct (Int64.eq n (Int64.repr n')) eqn:eq_n_n'. *)
  (*   - simpl. *)
  (*     destruct (Mem.valid_access_store m Mint64 b 0%Z (comp_of f) (Vlong (Int64.add n Int64.one))) as [m' m_m']; try assumption. *)
  (*     exists m'. split; eauto. *)
  (*     do 4 take_step'. *)
  (*     now apply star_refl. *)
  (*   - (* take_steps. *) *)
  (*     take_step'. rewrite Int.eq_true; simpl. *)
  (*     now apply star_refl. *)
  (* Qed. *)


  Definition switch_add_statement cnt s res :=
    (Z.pred (fst res), switch_clause cnt (Z.pred (fst res)) s (snd res)).

  Definition switch (cnt: ident) (ss: list statement) (s_else: statement): statement :=
    snd (fold_right (switch_add_statement cnt) (Z.of_nat (length ss), s_else) ss).

  (* Lemma fst_switch (cnt: ident) n (s_else: statement) (ss : list statement) : *)
  (*   fst (fold_right (switch_add_statement cnt) (n, s_else) ss) = (n - Z.of_nat (length ss))%Z. *)
  (* Proof. *)
  (*   induction ss as [|s' ss IH]; try now rewrite Z.sub_0_r. *)
  (*   simpl; lia. *)
  (* Qed. *)

  (* Lemma switch_spec_else *)
  (*       (ge: genv) (cnt: ident) f (e: env) le m b k (n: Z) ss s_else *)
  (*       (WF: Z.of_nat (length ss) < Int64.modulus) *)
  (*       (RANGE: Z.of_nat (length ss) <= n < Int64.modulus) *)
  (*   : *)
  (*   let cp := comp_of f in *)
  (*   e ! cnt = None -> *)
  (*   Genv.find_symbol ge cnt = Some b -> *)
  (*   Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (Int64.repr n)) -> *)
  (*   star (step1) ge *)
  (*        (State f (switch cnt ss s_else) k e le m) *)
  (*        E0 *)
  (*        (State f s_else k e le m). *)
  (* Proof. *)
  (*   intros; subst cp. unfold switch. destruct RANGE as [RA1 RA2]. *)
  (*   assert (G: forall n', *)
  (*              (Z.of_nat (length ss)) <= n' -> *)
  (*              n' <= n -> *)
  (*              star (step1) ge *)
  (*                   (State f (snd (fold_right (switch_add_statement cnt) (n', s_else) ss)) k e le m) *)
  (*                   E0 *)
  (*                   (State f s_else k e le m)). *)
  (*   { intros n' LE1 LE2. *)
  (*     induction ss as [|s ss IH]; try apply star_refl. *)
  (*     simpl. simpl in RA1, LE1. rewrite fst_switch, <- Z.sub_succ_r. *)
  (*     take_step'. *)
  (*     { rewrite Int64.eq_false. reflexivity. clear - WF RA1 RA2 LE1 LE2. *)
  (*       destruct (Z.eqb_spec n (n' - Z.of_nat (S (length ss)))) as [n_eq_0|?]; simpl. *)
  (*       - lia. *)
  (*       - intros EQ. apply n0; clear n0. *)
  (*         rewrite <- (Int64.unsigned_repr n). *)
  (*         rewrite EQ. rewrite Int64.unsigned_repr. lia. *)
  (*         1: split. *)
  (*         all: unfold Int64.max_unsigned; try lia. *)
  (*     } *)
  (*     rewrite Int.eq_true; simpl. *)
  (*     eapply IH; lia. *)
  (*   } *)
  (*   now apply G; lia. *)
  (* Qed. *)

  Definition nat64 n := Int64.repr (Z.of_nat n).

  (* Lemma switch_spec *)
  (*       (ge: genv) (cnt: ident) f (e: env) le m b k *)
  (*       ss s ss' s_else *)
  (*       (WF: Z.of_nat (length (ss ++ s :: ss')) < Int64.modulus) *)
  (*   : *)
  (*   let cp := comp_of f in *)
  (*   e ! cnt = None -> *)
  (*   Genv.find_symbol ge cnt = Some b -> *)
  (*   Mem.valid_access m Mint64 b 0 Writable (Some cp) -> *)
  (*   Mem.loadv Mint64 m (Vptr b Ptrofs.zero) (Some cp) = Some (Vlong (nat64 (length ss))) -> *)
  (*   exists m', *)
  (*     Mem.storev Mint64 m (Vptr b Ptrofs.zero) (Vlong (Int64.add (nat64 (length ss)) Int64.one)) cp = Some m' /\ *)
  (*       star (step1) ge *)
  (*            (State f (switch cnt (ss ++ s :: ss') s_else) k e le m) *)
  (*            E0 *)
  (*            (State f s k e le m'). *)
  (* Proof. *)
  (*   intros. *)
  (*   assert (Eswitch : *)
  (*            exists s_else', *)
  (*              switch cnt (ss ++ s :: ss') s_else = *)
  (*                switch cnt ss (switch_clause cnt (Z.of_nat (length ss)) s s_else')). *)
  (*   { unfold switch. rewrite fold_right_app, app_length. simpl. *)
  (*     exists (snd (fold_right (switch_add_statement cnt) (Z.of_nat (length ss + S (length ss')), s_else) ss')). *)
  (*     repeat f_equal. rewrite -> surjective_pairing at 1. simpl. *)
  (*     rewrite fst_switch, Nat.add_succ_r. *)
  (*     assert (A: Z.pred (Z.of_nat (S (Datatypes.length ss + Datatypes.length ss')) - Z.of_nat (Datatypes.length ss')) = Z.of_nat (Datatypes.length ss)) by lia. *)
  (*     rewrite A. reflexivity. *)
  (*   } *)
  (*   destruct Eswitch as [s_else' ->]. clear s_else. rename s_else' into s_else. *)
  (*   exploit (switch_clause_spec ge cnt f e le m b k (nat64 (length ss)) (Z.of_nat (length ss)) s s_else); auto. *)
  (*   unfold nat64. rewrite Int64.eq_true. intro Hcont. *)
  (*   destruct Hcont as (m' & Hstore & Hstar2). *)
  (*   exists m'. split; trivial. *)
  (*   apply (fun H => @star_trans _ _ _ _ _ E0 _ H E0 _ _ Hstar2); trivial. *)
  (*   assert (WF2: Z.of_nat (Datatypes.length ss) < Int64.modulus). *)
  (*   { clear - WF. rewrite app_length in WF. lia. } *)
  (*   eapply switch_spec_else; eauto. split; auto. reflexivity. *)
  (* Qed. *)

End SWITCH.


Section CONV.
  (** converting event to data **)

  Variable ge: Senv.t.

  (* Definition not_in_env (e: env) id := e ! id = None. *)

  (* Definition wf_env (e: env) := *)
  (*   forall id, match Senv.find_symbol ge id with *)
  (*         | Some _ => not_in_env e id *)
  (*         | _ => True *)
  (*         end. *)

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

  (* Lemma ptr_of_id_ofs_typeof *)
  (*       i i0 *)
  (*   : *)
  (*   typeof (ptr_of_id_ofs i i0) = Tpointer Tvoid noattr. *)
  (* Proof. unfold ptr_of_id_ofs. destruct Archi.ptr64; simpl; auto. Qed. *)

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

  (* Lemma typeof_eventval_to_expr_type *)
  (*       v *)
  (*   : *)
  (*   typeof (eventval_to_expr v) = eventval_to_type v. *)
  (* Proof. destruct v; simpl; auto. apply ptr_of_id_ofs_typeof. Qed. *)

  (* Definition wf_eventval_pub (v: eventval): Prop := *)
  (*   match v with *)
  (*   | EVptr_global id _ => (Senv.public_symbol ge id = true) *)
  (*   | _ => True *)
  (*   end. *)

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

  (* Lemma proj_rettype_to_type_rettype_of_type_eq *)
  (*       ge evres rt res *)
  (*       (EVM: eventval_match ge evres (proj_rettype rt) res) *)
  (*   : *)
  (*   proj_rettype (rettype_of_type (rettype_to_type rt)) = proj_rettype rt. *)
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
  Record fun_data : Type := mkfundata { dargs: typelist; dret: type; dcc: calling_convention }.
  Definition funs_data : Type := (PTree.tree fun_data).

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
  Definition from_clfd_fun_data (fd: Clight.fundef): fun_data :=
    match fd with | Ctypes.Internal cf => from_clfun_fun_data cf | Ctypes.External ef _ _ _ => from_extfun_fun_data ef end.
  Definition from_clgd_fun_data (gd: globdef Clight.fundef type): option fun_data :=
    match gd with | Gfun fd => Some (from_clfd_fun_data fd) | Gvar _ => None end.

  Definition from_cl_funs_data (cl: Clight.program): funs_data :=
    let defs := Genv.genv_defs (genv_genv (globalenv cl)) in
    PTree.map_filter1 from_clgd_fun_data defs.

End CODEAUX.


Section CONV.

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

  (* Lemma access_mode_chunk_to_type_wf *)
  (*       ch ty *)
  (*       (CT: chunk_to_type ch = Some ty) *)
  (*   : *)
  (*   access_mode ty = By_value ch. *)
  (* Proof. destruct ch; inv CT; ss. Qed. *)

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
                if ((Senv.public_symbol ge id) && (cp0 =? cp)%positive)
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

Section GEN.

  Definition list_typ_to_list_type (ts: list typ): list type := map typ_to_type ts.

  Definition gen_function (ge: Senv.t) (cnt: ident) (params: list (ident * type)) (tr: bundle_trace) (a_f: Asm.function): function :=
    let a_sg := Asm.fn_sig a_f in
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
    let gds' := map (fun '(id, gd) => (id, (Pos.add id m, gen_counter (comp_of gd)))) gds in
    PTree_Properties.of_list gds'.

  Definition params_of := PTree.t (list (ident * type)).

  Fixpoint numbering {A} (i: ident) (l: list A): list (ident * A) :=
    match l with
    | [] => []
    | hd :: tl => (i, hd) :: (numbering (Pos.succ i) tl)
    end.

  Definition funsig (fd: Asm.fundef) :=
    match fd with
    | AST.Internal f => fn_sig f
    | AST.External ef => ef_sig ef
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
    let params' := map (fun '(id, gd) => match gen_params_one m gd with
                                         | Some ps => (id, ps)
                                         | None => (id, [])
                                         end) gds
    in
    PTree_Properties.of_list params'.


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


Section AUX.

  Definition wf_keys {A} (l: list (ident * A)) := list_norepet (map fst l).

  Definition wf_params_of (pars: params_of) :=
    (forall id params, (pars ! id = Some params) -> list_norepet (var_names params)).

  Definition wf_params_of_sig (pars: params_of) (ge: Asm.genv) :=
    forall b f id params, (Genv.find_funct_ptr ge b = Some f) -> (Genv.find_symbol ge id = Some b) -> (pars ! id = Some params) ->
                     (list_typ_to_list_type (sig_args (funsig f)) = map snd params).

  Definition wf_params_of_symb (pars: params_of) (ge: Clight.genv) :=
    forall id b, (Senv.find_symbol ge id = Some b) ->
            forall fid ps, pars ! fid = Some ps -> ~ (In id (map fst ps)).

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

  (* Lemma alloc_variables_wf_params_of_symb0 *)
  (*       ge cp e m params e' m' *)
  (*       (AE: alloc_variables ge cp e m params e' m') *)
  (*       (WFE: wf_env ge e) *)
  (*       (pars: params_of) *)
  (*       (WFP: wf_params_of_symb pars ge) *)
  (*       fid vars *)
  (*       (PAR: pars ! fid = Some vars) *)
  (*       (INCL: forall x, In x params -> In x vars) *)
  (*   : *)
  (*   wf_env ge e'. *)
  (* Proof. *)
  (*   revert_until AE. induction AE; ii. *)
  (*   { eapply WFE. } *)
  (*   eapply IHAE. 3: eapply PAR. *)
  (*   3:{ i. eapply INCL. ss. right; auto. } *)
  (*   2: auto. *)
  (*   clear IHAE id0. unfold wf_env in *. i. specialize (WFE id0). des_ifs. *)
  (*   unfold not_in_env in *. specialize (WFP _ _ Heq _ _ PAR). *)
  (*   destruct (Pos.eqb_spec id id0). *)
  (*   2:{ rewrite PTree.gso; auto. } *)
  (*   subst id0. exfalso. apply WFP; clear WFP. specialize (INCL (id, ty)). *)
  (*   replace id with (fst (id, ty)). 2: ss. apply in_map. apply INCL. ss. left; auto. *)
  (* Qed. *)

  (* Lemma alloc_variables_wf_params_of_symb *)
  (*       ge cp m params e' m' *)
  (*       (AE: alloc_variables ge cp empty_env m params e' m') *)
  (*       (pars: params_of) *)
  (*       (WFP: wf_params_of_symb pars ge) *)
  (*       fid *)
  (*       (PAR: pars ! fid = Some params) *)
  (*   : *)
  (*   wf_env ge e'. *)
  (* Proof. eapply alloc_variables_wf_params_of_symb0; eauto. ii. des_ifs. Qed. *)

End AUX.
