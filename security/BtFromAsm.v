Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import riscV.Asm.
Require Import BtInfoAsm BtBasics.


Section WELLFORMED.

  (* Variant sf_cont_type : Type := | sf_cont: block -> signature -> sf_cont_type. *)
  Variant sf_cont_type : Type := | sf_cont: block -> sf_cont_type.
  Definition sf_conts := list sf_cont_type.

  Definition crossing_comp {F V} (ge: Genv.t F V) (cp cp': compartment) :=
    Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall.

  Definition virtual_reality (ct: Genv.call_type) (vr: real_virtual): Prop :=
    match ct with
    | Genv.InternalCall => False
    | Genv.CrossCompartmentCall => vr = is_real
    | Genv.DefaultCompartmentCall => vr = is_virtual
    end.

  (* wf_sem: from asm, wf_st: proof invariant for Clight states *)
  Inductive info_asm_sem_wf (ge: Asm.genv) : block -> mem -> sf_conts -> itrace -> Prop :=
  | info_asm_sem_wf_base
      cur m1 sf
    :
    info_asm_sem_wf ge cur m1 sf nil
  | info_asm_sem_wf_cross_call
      cur m1 sf ev ik vr tl
      cp
      (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
      cp' fid evargs
      (EV: ev = Event_call cp cp' fid evargs)
      sg
      (IK: ik = info_call not_cross_ext sg vr)
      b
      (FINDB: Genv.find_symbol ge fid = Some b)
      fd
      (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
      (CP': cp' = comp_of fd)
      (VR: virtual_reality (Genv.type_of_call ge cp cp') vr)
      (* (CROSS: Genv.type_of_call ge cp cp' <> Genv.InternalCall) *)
      args
      (NPTR: crossing_comp ge cp cp' -> Forall not_ptr args)
      (ALLOW: Genv.allowed_call ge cp (Vptr b Ptrofs.zero))
      (ESM: crossing_comp ge cp cp' -> eventval_list_match ge evargs (sig_args sg) args)
      (SIG: sg = Asm.funsig fd)
      (NEXT: info_asm_sem_wf ge b m1 ((sf_cont cur) :: sf) tl)
    :
    info_asm_sem_wf ge cur m1 sf ((ev, ik) :: tl)
  | info_asm_sem_wf_cross_return_internal
      cur m1 ev ik vr tl
      cp
      (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
      cp_c evres
      (EV: ev = Event_return cp_c cp evres)
      sg
      (IK: ik = info_return sg vr)
      cur_f
      (INTERNAL: Genv.find_funct_ptr ge cur = Some (AST.Internal cur_f))
      (* Follows from cross call - stack has the sig *)
      (SIG: sg = Asm.fn_sig cur_f)
      (VR: virtual_reality (Genv.type_of_call ge cp_c cp) vr)
      res
      (EVM: crossing_comp ge cp_c cp -> eventval_match ge evres (proj_rettype (sig_res sg)) res)
      (NPTR: crossing_comp ge cp_c cp -> not_ptr res)
      b_c sf_tl
      (CPC: cp_c = Genv.find_comp ge (Vptr b_c Ptrofs.zero))
      (* internal return: memory changes in Clight-side, so need inj-relation *)
      (NEXT: info_asm_sem_wf ge b_c m1 sf_tl tl)
    :
    info_asm_sem_wf ge cur m1 ((sf_cont b_c) :: sf_tl) ((ev, ik) :: tl)
  | info_asm_sem_wf_intra_call_external
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
      (INTRA: Genv.type_of_call ge cp (Genv.find_comp ge (Vptr fb Ptrofs.zero)) = Genv.InternalCall)
      (NEXT: info_asm_sem_wf ge cur m2 sf tl)
    :
    info_asm_sem_wf ge cur m1 sf ((ev, ik) :: tl)
  | info_asm_sem_wf_builtin
      cur m1 sf ev ik tl
      cp
      (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
      ef res m2
      (EXT: external_call_event_match_common ef ev ge cp m1 res m2)
      (IK: ik = info_builtin ef)
      (NEXT: info_asm_sem_wf ge cur m2 sf tl)
    :
    info_asm_sem_wf ge cur m1 sf ((ev, ik) :: tl)
  | info_asm_sem_wf_cross_call_external1
      (* early cut at call event *)
      cur m1 sf ev vr ik
      cp
      (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
      cp' fid evargs
      (EV: ev = Event_call cp cp' fid evargs)
      sg
      (IK: ik = info_call is_cross_ext sg vr)
      b
      (FINDB: Genv.find_symbol ge fid = Some b)
      fd
      (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
      (CP': cp' = comp_of fd)
      (VR: virtual_reality (Genv.type_of_call ge cp cp') vr)
      args
      (NPTR: crossing_comp ge cp cp' -> Forall not_ptr args)
      (ALLOW: Genv.allowed_call ge cp (Vptr b Ptrofs.zero))
      (ESM: crossing_comp ge cp cp' -> eventval_list_match ge evargs (sig_args sg) args)
      ef
      (EXTERNAL: fd = AST.External ef)
      (SIG: sg = ef_sig ef)
    :
    info_asm_sem_wf ge cur m1 sf ((ev, ik) :: nil)
  | info_asm_sem_wf_cross_call_external2
      (* early cut at call-ext_call event *)
      cur m1 sf ev1 vr1 ik1
      cp
      (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
      cp' fid evargs
      (EV: ev1 = Event_call cp cp' fid evargs)
      sg
      (IK: ik1 = info_call is_cross_ext sg vr1)
      b
      (FINDB: Genv.find_symbol ge fid = Some b)
      fd
      (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
      (CP': cp' = comp_of fd)
      (VR: virtual_reality (Genv.type_of_call ge cp cp') vr1)
      args
      (NPTR: crossing_comp ge cp cp' -> Forall not_ptr args)
      (ALLOW: Genv.allowed_call ge cp (Vptr b Ptrofs.zero))
      (ESM: crossing_comp ge cp cp' -> eventval_list_match ge evargs (sig_args sg) args)
      ef
      (EXTERNAL: fd = AST.External ef)
      (SIG: sg = ef_sig ef)
      (* external call part *)
      tr vres m2
      (EXTCALL: external_call ef ge cp args m1 tr vres m2)
      itr
      (INFO: itr = map (fun e => (e, info_external b (ef_sig ef))) tr)
    :
    info_asm_sem_wf ge cur m1 sf ((ev1, ik1) :: itr)
  | info_asm_sem_wf_cross_call_external3
      (* full call-ext_call-return event *)
      cur m1 sf ev1 vr1 ik1
      cp
      (CURCP: cp = Genv.find_comp ge (Vptr cur Ptrofs.zero))
      cp' fid evargs
      (EV: ev1 = Event_call cp cp' fid evargs)
      sg
      (IK: ik1 = info_call is_cross_ext sg vr1)
      b
      (FINDB: Genv.find_symbol ge fid = Some b)
      fd
      (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
      (CP': cp' = comp_of fd)
      (VR1: virtual_reality (Genv.type_of_call ge cp cp') vr1)
      args
      (NPTR: crossing_comp ge cp cp' -> Forall not_ptr args)
      (ALLOW: Genv.allowed_call ge cp (Vptr b Ptrofs.zero))
      (ESM: crossing_comp ge cp cp' -> eventval_list_match ge evargs (sig_args sg) args)
      ef
      (EXTERNAL: fd = AST.External ef)
      (SIG: sg = ef_sig ef)
      (* external call part *)
      tr vres m2
      (EXTCALL: external_call ef ge cp args m1 tr vres m2)
      itr
      (INFO: itr = map (fun e => (e, info_external b (ef_sig ef))) tr)
      (* return part *)
      ev3 vr3 ik3 tl
      evres
      (EV: ev3 = Event_return cp cp' evres)
      sg
      (IK: ik3 = info_return sg vr3)
      (VR2: virtual_reality (Genv.type_of_call ge cp cp') vr3)
      (EVM: crossing_comp ge cp cp' -> eventval_match ge evres (proj_rettype (sig_res sg)) vres)
      (NPTR: crossing_comp ge cp cp' -> not_ptr vres)
      (NEXT: info_asm_sem_wf ge cur m2 sf tl)
    :
    info_asm_sem_wf ge cur m1 sf ((ev1, ik1) :: (itr ++ ((ev3, ik3) :: tl)))
  .

  (* TODO *)
  (* we need a more precise invariant for the proof; counters, mem_inj, env, cont, state *)

End WELLFORMED.

Section MATCH.

  Variant match_stack_type : (sf_cont_type) -> (stackframe) -> Prop :=
    | match_stack_type_intro
        b cp sg v ofs
      :
      match_stack_type (sf_cont b) (Stackframe b cp sg v ofs).

  Definition match_stack (sf: sf_conts) (st: stack) := Forall2 match_stack_type sf st.

  Definition match_cp (ge: Asm.genv) (cur: block) (cp: compartment) : Prop :=
    Genv.find_comp ge (Vptr cur Ptrofs.zero) = cp.

  Definition meminj_ge {F V} (ge: Genv.t F V): meminj :=
    fun b => match Genv.invert_symbol ge b with
          | Some id => match Genv.find_symbol ge id with
                      | Some b' => Some (b', 0)
                      | None => None
                      end
          | None => None
          end.

  Definition match_mem (ge: Asm.genv) (m_ir m_asm: mem): Prop := Mem.inject (meminj_ge ge) m_asm m_ir.

  Definition wf_stackframe (ge: Asm.genv) (fr: stackframe) :=
    match fr with
    | Stackframe b _ _ _ _ => match Genv.find_funct_ptr ge b with
                             | Some (Internal f) => True
                             | _ => False
                             end
    end.
  Definition wf_stack (ge: Asm.genv) (sk: stack) := Forall (wf_stackframe ge) sk.

  Definition wf_regset_stack (ge: Asm.genv) (rs: regset) :=
    match rs PC with
    | Vptr b _ => match Genv.find_funct_ptr ge b with
                 | Some (External ef) => False
                 | _ => True
                 end
    | _ => True
    end.

  (* Definition wf_regset_stack cpm (ge: Asm.genv) (rs: regset) (sk: stack) := *)
  (*   match rs PC with *)
  (*   | Vptr b _ => match Genv.find_funct_ptr ge b with *)
  (*                | Some (External ef) => Genv.find_comp_ignore_offset ge (rs RA) = callee_comp cpm sk *)
  (*                | _ => True *)
  (*                end *)
  (*   | _ => True *)
  (*   end. *)



(* Definition external_call_mem_inject_gen ef := ec_mem_inject (external_call_spec ef). *)

(* external_call_mem_inject: *)
(*   forall (ef : external_function) [F V : Type] [ge : Genv.t F V] (c : compartment) [vargs : list val] [m1 : mem] (t : trace) (vres : val) (m2 : mem) [f : block -> option (block * Z)]  *)
(*     [m1' : mem] [vargs' : list val], *)
(*   meminj_preserves_globals ge f -> *)
(*   external_call ef ge c vargs m1 t vres m2 -> *)
(*   Mem.inject f m1 m1' -> *)
(*   Val.inject_list f vargs vargs' -> *)
(*   exists (f' : meminj) (vres' : val) (m2' : mem), *)
(*     external_call ef ge c vargs' m1' t vres' m2' /\ *)
(*     Val.inject f' vres vres' /\ Mem.inject f' m2 m2' /\ Mem.unchanged_on (loc_unmapped f) m1 m2 /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' /\ inject_incr f f' /\ inject_separated f f' m1 m1' *)

(* meminj_preserves_globals: forall [F V : Type], Genv.t F V -> (block -> option (block * Z)) -> Prop *)
(* Separation.globalenv_preserved: forall {F V : Type}, Genv.t F V -> meminj -> block -> Prop *)
(* Genv.same_symbols: forall [F V : Type], meminj -> Genv.t F V -> Prop *)
(*       Genv.init_mem p = Some m0 -> *)
(* Variable f: block -> option (block * Z). *)
(* Variable ge1 ge2: Senv.t. *)

(* Definition symbols_inject : Prop := *)
(*    (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) *)
(* /\ (forall id b1 b2 delta, *)
(*      f b1 = Some(b2, delta) -> Senv.find_symbol ge1 id = Some b1 -> *)
(*      delta = 0 /\ Senv.find_symbol ge2 id = Some b2) *)
(* /\ (forall id b1, *)
(*      Senv.public_symbol ge1 id = true -> Senv.find_symbol ge1 id = Some b1 -> *)
(*      exists b2, f b1 = Some(b2, 0) /\ Senv.find_symbol ge2 id = Some b2) *)
(* /\ (forall b1 b2 delta, *)
(*      f b1 = Some(b2, delta) -> *)
(*      Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1). *)
(* Senv.equiv =  *)
(* fun se1 se2 : Senv.t => *)
(* (forall id : ident, Senv.find_symbol se2 id = Senv.find_symbol se1 id) /\ *)
(* (forall id : ident, Senv.public_symbol se2 id = Senv.public_symbol se1 id) /\ (forall b : block, Senv.block_is_volatile se2 b = Senv.block_is_volatile se1 b) *)
(*      : Senv.t -> Senv.t -> Prop *)

End MATCH.

Section PROOF.

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

  (* If main is External, treat it in a different case - the trace can start with Event_syscall, without a preceding Event_call *)
  Lemma from_info_asm_sem_wf
        cpm ge s s' it
        (WFGE: wf_ge ge)
        (STAR: istar (asm_istep cpm) ge s it s')
        sk rs m
        (STATE: s = State sk rs m)
        (WFSK: wf_stack ge sk)
        (WFRS: wf_regset_stack ge rs)
        (* (WFRS: wf_regset_stack cpm ge rs sk) *)
        cur m_ir k
        (MC: match_cp ge cur (Genv.find_comp_ignore_offset ge (rs PC)))
        (MM: match_mem ge m_ir m)
        (MS: match_stack k sk)
    :
    info_asm_sem_wf ge cur m_ir k it.
  Proof.
    apply measure_istar in STAR. destruct STAR as (n & STAR).
    move n before ge. revert s s' it WFGE STAR sk rs m STATE WFSK WFRS cur m_ir k MC MM MS.
    pattern n. apply (well_founded_induction Nat.lt_wf_0). intros m IH. intros.
    inv STAR; subst.
    { constructor 1. }
    rename H0 into STAR. inv H; simpl.
    - assert (INTRA: Genv.find_comp ge (Vptr cur Ptrofs.zero) = Genv.find_comp_ignore_offset ge (rs' PC)).
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
            { clear EVLEN. eapply IH. 3: eapply IH_ISTAR. all: auto.
              - red. rewrite Pregmap.gss. rewrite NEXTPC2. rewrite NEXTFUN2. auto.
              - rewrite Pregmap.gss in *. rewrite <- e. rewrite <- REC_CURCOMP. auto.
              - admit. (* mem *)
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
            
              
              
            
                

              constructor 1. }
            
            
          




          exploit external_call_trace_length. eauto. intros EVLEN. destruct t.
          { simpl. clear EVLEN. eapply IH. 3: eapply H1. all: auto.
            - red. rewrite Pregmap.gss.
              (* TODO *)

            pose proof EV as RETEV. inv RETEV; simpl.
            { eapply IH. 3: eauto. all: auto.
              assert (STEQ: st' = sk).
              
              { unfold update_stack_return in STUPD.
                econstructor 4.

        (* TODO *)

        eapply IHSTAR.
        

istar_ind:
  forall (genv state : Type) (step : genv -> state -> itrace -> state -> Prop) (ge : genv) (P : state -> itrace -> state -> Prop),
  (forall s : state, P s nil s) ->
  (forall (s1 : state) (t1 : itrace) (s2 : state) (t2 : itrace) (s3 : state) (t : itrace), step ge s1 t1 s2 -> istar step ge s2 t2 s3 -> P s2 t2 s3 -> t = t1 ++ t2 -> P s1 t s3) ->
  forall (y : state) (i : itrace) (y0 : state), istar step ge y i y0 -> P y i y0
        
       
    
external_call_trace_length:
  forall (ef : external_function) (ge : Senv.t) (c : compartment) (vargs : list val) (m : mem) (t : trace) (vres : val) (m' : mem), external_call ef ge c vargs m t vres m' -> (Datatypes.length t <= 1)%nat

      


    (* TODO *)

  Inductive info_asm_sem_wf (ge: Asm.genv) : block -> mem -> sf_conts -> itrace -> Prop :=
  Definition state_has_trace_informative (L: Smallstep.semantics) (s: state L) (step: istep L) (t: itrace): Prop :=
    (exists s', (istar step (globalenv L)) s t s').
  Variant semantics_has_initial_trace_informative (L: Smallstep.semantics) (step: istep L) (t: itrace) : Prop :=
    | semantics_info_runs :
      forall s, (initial_state L s) -> (state_has_trace_informative L s step t) -> semantics_has_initial_trace_informative _ _ t
    | semantics_info_goes_initially_wrong : (forall s : state L, ~ initial_state L s) -> (t = nil) -> semantics_has_initial_trace_informative _ _ t.
  Definition asm_has_initial_trace_informative (p: Asm.program) (t: itrace) :=
    semantics_has_initial_trace_informative (semantics p) (asm_istep (comp_of_main p)) t.

Mem.alloc_left_unmapped_inject:
  forall (f : meminj) (m1 m2 : mem) (c : compartment) (lo hi : Z) (m1' : Mem.mem') (b1 : block),
  Mem.inject f m1 m2 -> Mem.alloc m1 c lo hi = (m1', b1) -> exists f' : meminj, Mem.inject f' m1' m2 /\ inject_incr f f' /\ f' b1 = None /\ (forall b : block, b <> b1 -> f' b = f b)

Mem.free_left_inject: forall (f : meminj) (m1 m2 : mem) (b : block) (lo hi : Z) (cp : compartment) (m1' : mem), Mem.inject f m1 m2 -> Mem.free m1 b lo hi cp = Some m1' -> Mem.inject f m1' m2

Mem.free_right_inject:
  forall (f : meminj) (m1 m2 : mem) (b : block) (lo hi : Z) (cp : compartment) (m2' : mem),
  Mem.inject f m1 m2 ->
  Mem.free m2 b lo hi cp = Some m2' ->
  (forall (b1 : block) (delta ofs : Z) (k : perm_kind) (p : permission), f b1 = Some (b, delta) -> Mem.perm m1 b1 ofs k p -> lo <= ofs + delta < hi -> False) -> Mem.inject f m1 m2'

End PROOF.
