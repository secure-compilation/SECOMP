Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import riscV.Machregs.
Require Import riscV.Asm.
Require Import Complements.
Require Import BtBasics.


Section MEMDATA.

  (* Data to get injection by invoking correct Mem.store: inj + (apply delta) = inj *)
  Definition mem_delta_data := (memory_chunk * val * compartment)%type.
  Definition mem_delta_ofs := list (Z * mem_delta_data).
  Definition mem_delta := PTree.t mem_delta_ofs.

  Definition mem_delta_ofs_get (dd: mem_delta_ofs) (ofs: Z): option mem_delta_data :=
    match find (fun '(k, data) => Z.eqb k ofs) dd with | Some (k, data) => Some data | None => None end.
  Definition mem_delta_get (d: mem_delta) (b: block) (ofs: Z): option mem_delta_data :=
    match PTree.get b d with
    | Some dd => mem_delta_ofs_get dd ofs
    | _ => None
    end.

  Definition mem_delta_apply_ofs (b: block) (dd: mem_delta_ofs) (m0: mem) : option mem :=
    fold_left (fun om '(ofs, (ch, v, cp)) => match om with | Some m => Mem.store ch m b ofs v cp | _ => None end) dd (Some m0).
  Definition mem_delta_apply (d: mem_delta) (m0: mem) : option mem :=
    PTree.fold (fun om b dd => match om with | Some m => mem_delta_apply_ofs b dd m | _ => None end) d (Some m0).

  (* Memory injection for public global symbols: visible for external calls *)
  Definition meminj_public (ge: Senv.t): meminj :=
    fun b => match Senv.invert_symbol ge b with
          | Some id => if Senv.public_symbol ge id then Some (b, 0%Z) else None
          | None => None
          end.

  (* We keep delta only for some partial memory, as specified by some meminj *)
  Definition mem_delta_wf_inj (d: mem_delta) (j: meminj): Prop :=
    forall b ofs dd jj, (mem_delta_get d b ofs = Some dd) -> (j b = Some jj).

  Definition mem_delta_data_fo (ddd: mem_delta_data): Prop :=
    let '(ch, v, cp) := ddd in Forall (fun mv => match mv with | Byte bt => True | _ => False end) (encode_val ch v).
  Definition mem_delta_ofs_fo (dd: mem_delta_ofs): Prop :=
    Forall (fun '(k, ddd) => mem_delta_data_fo ddd) dd.
  Definition mem_delta_fo (d: mem_delta): Prop :=
    PTree.fold (fun p b dd => p /\ (mem_delta_ofs_fo dd)) d True.

  Lemma mem_delta_apply_preserves_inj
        (j: meminj) m0 m0'
        (INJ0: Mem.inject j m0 m0')
        (d: mem_delta)
        (DWF: mem_delta_wf_inj d j)
        (DFO: mem_delta_fo d)
        m1
        (APPD: mem_delta_apply d m0 = Some m1)
    :
    exists m1', (mem_delta_apply d m0' = Some m1') /\ (Mem.inject j m1 m1').
  Proof.
  Abort.


  Definition mem_delta_writable (d: mem_delta) (m: mem) :=
    forall (b: block) (ofs: Z) chunk v cp,
      mem_delta_get d b ofs = Some (chunk, v, cp) ->
      Mem.valid_access m chunk b ofs Writable (Some cp).

  Definition mem_delta_respect_inj (d: mem_delta) (f: meminj) (m1 m2: mem) :=
    (* (mem_weak_inj d f m1 m2) -> *)
    (exists m2', (mem_apply_delta d m2 = Some m2') /\ (Mem.mem_inj f m1 m2')).

  (* Memory inv = weak_inject /\ mem_delta_writable /\ mem_delta_respect_inj, meminj_public *)

End MEMDATA.


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
  | call_trace_vr_virtual : forall (cp cp' : compartment) (b : block) (vargs : list val) (vl : list eventval) (ty : list typ) (i : ident),
      Genv.type_of_call ge cp cp' = Genv.DefaultCompartmentCall ->
      Genv.invert_symbol ge b = Some i -> (vl = typ_to_eventvals ty) -> call_trace_vr ge cp cp' b vargs ty E0 i vl
  | call_trace_vr_cross : forall (cp cp' : compartment) (b : block) (vargs : list val) (vl : list eventval) (ty : list typ) (i : ident),
      Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall ->
      Genv.invert_symbol ge b = Some i -> eventval_list_match ge vl ty vargs -> call_trace_vr ge cp cp' b vargs ty (Event_call cp cp' i vl :: nil) i vl.

  Inductive return_trace_vr {F V : Type} (ge : Genv.t F V) : compartment -> compartment -> val -> rettype -> trace -> eventval -> Prop :=
  | return_trace_vr_virtual : forall (cp cp' : compartment) (res : eventval) (v : val) (ty : rettype),
      Genv.type_of_call ge cp cp' = Genv.DefaultCompartmentCall -> (res = typ_to_eventval (proj_rettype ty)) -> return_trace_vr ge cp cp' v ty E0 res
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
        (MEM: mem_apply_delta d m1 = Some m1')
        vargs vretv
        (EC: external_call ef ge cp_cur vargs m1' tr vretv m2)
        (LL: limit_leaks_and_unknown ef ge m1 vargs)
        (ARGS: evargs = vals_to_eventvals ge vargs)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_call tr id evargs sg (Some d)) (Some (cur, m2, ik))
    | ir_step_builtin
        cur m1 m2 ik
        tr ef evargs
        cp_cur
        (CURCP: cp_cur = Genv.find_comp ge (Vptr cur Ptrofs.zero))
        d m1'
        (MEM: mem_apply_delta d m1 = Some m1')
        vargs vretv
        (EC: external_call ef ge cp_cur vargs m1' tr vretv m2)
        (LL: limit_leaks_and_unknown ef ge m1 vargs)
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
        (MEM: mem_apply_delta d m1 = Some m1')
        tr2 m2 vretv
        (EC: external_call ef ge cp vargs m1' tr2 vretv m2)
        (LL: limit_leaks_and_unknown ef ge m1 vargs)
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
        (MEM: mem_apply_delta d m1 = Some m1')
        tr2 m2 vretv
        (TR2: external_call ef ge cp vargs m1' tr2 vretv m2)
        (LL: limit_leaks_and_unknown ef ge m1 vargs)
        (ARGS: evargs = vals_to_eventvals ge vargs)
        (* return part *)
        tr3 evretv
        (NPTR: crossing_comp ge cp cp' -> not_ptr vretv)
        f_cur
        (INTERNAL: Genv.find_funct_ptr ge cur = Some (AST.Internal f_cur))
        (TR3: return_trace_vr ge cp cp' vretv (sig_res sg) tr3 evretv)
      :
      ir_step ge (Some (cur, m1, ik)) (Bundle_call (tr1 ++ tr2 ++ tr3) id evargs sg (Some d)) (Some (cur, m2, ik)).

  (* we need a more precise invariant for the proof for Clight; counters, mem_inj, env, cont, state *)

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

  Definition match_mem (ge: Asm.genv) (d: mem_delta) (m_asm m_ir: mem): Prop :=
    let j := meminj_public ge in
    (weak_inject d j m_asm m_ir) /\ (mem_delta_writable d m_asm) /\
      (mem_delta_respect_inj d j m_asm m_ir).


  Definition match_state (ge: Asm.genv) (ast: Asm.state) (ist: ir_state) (d: mem_delta): Prop :=
    match ast, ist with
    | State sk rs m_a, Some (cur, m_i, ik) =>
        (match_cur_stack cur ge sk) /\ (match_cur_regset cur ge rs) /\
          (match_stack ge ik sk) /\ (match_mem ge d m_a m_i)
    | _, _ => False
    end.

End INVS.

(* TODO: destination of memcpy should not be public glob symb *)

Section AUX.

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

End AUX.


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
