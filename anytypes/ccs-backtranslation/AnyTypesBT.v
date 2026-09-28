(** * External functions with any types and the back-translation (ccs-backtranslation + PR #19)

    To be compiled against a build of ccs-backtranslation with PR #19 (see
    ../build.sh).  Every result is closed with Qed.

    On this branch signatures use [typ] for arguments and [rettype] for
    results; [gen_fundef] declares an external function with the C types of
    [typ_to_type], which maps [Tany32]/[Tany64] to [int]/[long].  Same
    results as AnyTypes.v, named alike: (a) [signature_of_type_no_any];
    (b) [transl_fundef_external_no_any]; (c) [gen_fundef_external_accepted],
    [bt_defs_rejected], [gen_program_does_not_compile]; (d)
    [match_prog_no_any], [transf_clight_program_no_any], [link_no_any],
    [W_t_no_any], [bt_externals_accepted].
    Caveat: on this branch [Selectionproof.transf_program_match] is admitted,
    so [transf_clight_program_no_any], [transf_c_program_no_any], [W_t_no_any]
    and [bt_externals_accepted] depend on it; the relational
    [match_prog_no_any] and all failure results do not. *)


Require Import String.
Require Import Coqlib Maps Errors AST Linking Globalenvs.
Require Import Ctypes Clight.
Require Cshmgen Cshmgenproof SimplLocals SimplLocalsproof SimplExprproof.
Require Cminorgenproof Selectionproof RTLgenproof Tailcallproof Inliningproof
        Renumberproof Constpropproof CSEproof Deadcodeproof Unusedglobproof
        Allocproof Tunnelingproof Linearizeproof CleanupLabelsproof
        Debugvarproof Stackingproof Asmgenproof.
Require Import Compiler.
Require compcert.riscV.Asm.
Require Import compcert.security.Backtranslation.

(** ** Any-typed signatures *)

Definition typ_is_any (t: typ) : bool :=
  match t with Tany32 | Tany64 => true | _ => false end.

Definition rettype_is_any (rt: rettype) : bool :=
  match rt with Tret t => typ_is_any t | _ => false end.

Definition sig_has_any (sg: signature) : bool :=
  existsb typ_is_any (sig_args sg) || rettype_is_any (sig_res sg).

(** ** (a) No C type is any-typed *)

Lemma typ_of_type_not_any:
  forall t, typ_is_any (typ_of_type t) = false.
Proof.
  intros t; destruct t; simpl; try destruct f; unfold Tptr; try destruct Archi.ptr64; reflexivity.
Qed.

Lemma rettype_of_type_not_any:
  forall t, rettype_is_any (rettype_of_type t) = false.
Proof.
  intros t; destruct t; simpl; try destruct i; try destruct s; try destruct f;
    unfold Tptr; try destruct Archi.ptr64; reflexivity.
Qed.

Theorem signature_of_type_no_any:
  forall args res cc, sig_has_any (signature_of_type args res cc) = false.
Proof.
  intros. unfold sig_has_any, signature_of_type; simpl.
  rewrite rettype_of_type_not_any, orb_false_r.
  induction args as [|a args IH]; simpl; auto.
  rewrite typ_of_type_not_any; auto.
Qed.

(** ** (b) Cshmgen accepts only declarations without any-types *)

Theorem transl_fundef_external_no_any:
  forall ce id fd ef,
  Cshmgen.transl_fundef ce id fd = OK (AST.External ef) ->
  sig_has_any (ef_sig ef) = false.
Proof.
  intros ce id [f | ef' args res cc] ef H; simpl in H.
  - destruct (Cshmgen.transl_function ce f); simpl in H; discriminate.
  - destruct (signature_eq (ef_sig ef') (signature_of_type args res cc)) as [E|]; inv H.
    rewrite E. apply signature_of_type_no_any.
Qed.

Lemma transl_fundef_external_iff:
  forall ce id ef targs tres cc,
  Cshmgen.transl_fundef ce id (Ctypes.External ef targs tres cc) =
  if signature_eq (ef_sig ef) (signature_of_type targs tres cc)
  then OK (AST.External ef)
  else Error (msg "Cshmgen.transl_fundef: wrong external signature").
Proof. reflexivity. Qed.

(** ** (c) The declarations emitted by [gen_fundef] *)

Lemma typ_to_type_roundtrip:
  forall t, typ_is_any t = false -> typ_of_type (typ_to_type t) = t.
Proof. destruct t; simpl; congruence. Qed.

Lemma rettype_to_type_ext_roundtrip:
  forall rt, rettype_is_any rt = false -> rettype_of_type (rettype_to_type_ext rt) = rt.
Proof. destruct rt as [t| | | | |]; simpl; auto. destruct t; simpl; congruence. Qed.

(** What the any-types become: [Tany32] is declared [int], [Tany64] [long]. *)
Lemma typ_to_type_any:
  typ_of_type (typ_to_type Tany32) = AST.Tint /\
  typ_of_type (typ_to_type Tany64) = AST.Tlong /\
  rettype_of_type (rettype_to_type_ext (Tret Tany32)) = Tret AST.Tint /\
  rettype_of_type (rettype_to_type_ext (Tret Tany64)) = Tret AST.Tlong.
Proof. repeat split. Qed.

Lemma typlist_roundtrip:
  forall args, existsb typ_is_any args = false ->
  typlist_of_typelist (list_typ_to_typelist args) = args.
Proof.
  induction args as [|a args IH]; simpl; intros H; auto.
  apply orb_false_iff in H as [H1 H2].
  rewrite typ_to_type_roundtrip, IH; auto.
Qed.

Lemma sig_ext_roundtrip:
  forall sg, sig_has_any sg = false ->
  signature_of_type (list_typ_to_typelist (sig_args sg))
                    (rettype_to_type_ext (sig_res sg)) (sig_cc sg) = sg.
Proof.
  intros [args res cc] H; unfold sig_has_any in H; simpl in *.
  apply orb_false_iff in H as [HA HR].
  unfold signature_of_type. f_equal.
  - apply typlist_roundtrip; auto.
  - apply rettype_to_type_ext_roundtrip; auto.
Qed.

Lemma gen_fundef_external:
  forall ge fds cnt params tr ef,
  gen_fundef ge fds cnt params tr (AST.External ef) =
  Ctypes.External ef (list_typ_to_typelist (sig_args (ef_sig ef)))
                  (rettype_to_type_ext (sig_res (ef_sig ef))) (sig_cc (ef_sig ef)).
Proof. reflexivity. Qed.

Theorem gen_fundef_external_transl:
  forall ge fds cnt params tr ef ce id,
  Cshmgen.transl_fundef ce id (gen_fundef ge fds cnt params tr (AST.External ef)) =
  if sig_has_any (ef_sig ef)
  then Error (msg "Cshmgen.transl_fundef: wrong external signature")
  else OK (AST.External ef).
Proof.
  intros. rewrite gen_fundef_external, transl_fundef_external_iff.
  destruct (signature_eq (ef_sig ef) _) as [E|NE].
  - rewrite E, signature_of_type_no_any. reflexivity.
  - destruct (sig_has_any (ef_sig ef)) eqn:H; auto.
    exfalso; apply NE. symmetry. apply sig_ext_roundtrip; auto.
Qed.

Corollary gen_fundef_external_accepted:
  forall ge fds cnt params tr ef ce id,
  (exists tf, Cshmgen.transl_fundef ce id (gen_fundef ge fds cnt params tr (AST.External ef)) = OK tf)
  <-> sig_has_any (ef_sig ef) = false.
Proof.
  intros. rewrite gen_fundef_external_transl.
  destruct (sig_has_any (ef_sig ef)); split; intros H.
  - destruct H; discriminate.
  - discriminate.
  - reflexivity.
  - eauto.
Qed.

(** *** Program level *)

Lemma list_forall2_in_left:
  forall {A B: Type} (R: A -> B -> Prop) l1 l2 x,
  list_forall2 R l1 l2 -> In x l1 -> exists y, In y l2 /\ R x y.
Proof.
  induction 1; simpl; intros IN; [contradiction|].
  destruct IN as [<- | IN]; [eauto|].
  destruct (IHlist_forall2 IN) as (y & ? & ?); eauto.
Qed.

Lemma list_forall2_in_right:
  forall {A B: Type} (R: A -> B -> Prop) l1 l2 y,
  list_forall2 R l1 l2 -> In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  induction 1; simpl; intros IN; [contradiction|].
  destruct IN as [<- | IN]; [eauto|].
  destruct (IHlist_forall2 IN) as (x & ? & ?); eauto.
Qed.

Theorem cshmgen_rejects_bad_external:
  forall (p: Clight.program) id ef targs tres cc,
  In (id, Gfun (Ctypes.External ef targs tres cc)) (Ctypes.prog_defs p) ->
  ef_sig ef <> signature_of_type targs tres cc ->
  exists e, Cshmgen.transl_program p = Error e.
Proof.
  intros p id ef targs tres cc IN NE.
  destruct (Cshmgen.transl_program p) as [tp|e] eqn:T; [|eauto].
  exfalso. apply Cshmgenproof.transf_program_match in T.
  destruct T as [L _]. simpl in L.
  destruct (list_forall2_in_left _ _ _ _ L IN) as ([id' gd'] & _ & _ & M).
  simpl in M. inv M.
  match goal with H: Cshmgenproof.match_fundef _ _ _ |- _ => inv H end. auto.
Qed.

Theorem transf_clight_program_rejects_bad_external:
  forall (p: Clight.program) id ef targs tres cc,
  In (id, Gfun (Ctypes.External ef targs tres cc)) (Ctypes.prog_defs p) ->
  ef_sig ef <> signature_of_type targs tres cc ->
  exists e, transf_clight_program p = Error e.
Proof.
  intros p id ef targs tres cc IN NE.
  unfold transf_clight_program, time. rewrite ! compose_print_identity. simpl.
  destruct (SimplLocals.transf_program p) as [p2|e] eqn:P2; simpl; [|eauto].
  apply SimplLocalsproof.match_transf_program in P2. destruct P2 as [[L _] _].
  simpl in L.
  destruct (list_forall2_in_left _ _ _ _ L IN) as ([id' gd'] & IN' & E & M).
  simpl in E, M. subst id'. inv M.
  match goal with H: SimplLocals.transf_fundef _ = OK _ |- _ => simpl in H; inv H end.
  destruct (cshmgen_rejects_bad_external p2 id ef targs tres cc) as [e C]; auto.
  rewrite C. simpl. eauto.
Qed.

Lemma map_fst_pairs:
  forall {A B: Type} (g: ident -> A -> B) (l: list (ident * A)),
  map fst (map (fun '(id, a) => (id, g id a)) l) = map fst l.
Proof.
  induction l as [|[id a] l IH]; simpl; auto. f_equal; auto.
Qed.

Lemma gen_counter_defs_dom:
  forall m gds id, In id (map fst gds) ->
  exists c, (gen_counter_defs m gds) ! id = Some c.
Proof.
  intros. unfold gen_counter_defs. apply PTree_Properties.of_list_dom.
  rewrite (map_fst_pairs (fun id gd => (Pos.add id m, gen_counter (comp_of gd)))). auto.
Qed.

Lemma map_fst_gen_params:
  forall m (gds: list (ident * globdef Asm.fundef unit)),
  map fst (map (fun '(id, gd) => match gen_params_one m gd with
                                 | Some ps => (id, ps)
                                 | None => (id, @nil (ident * type))
                                 end) gds) = map fst gds.
Proof.
  induction gds as [|[id' gd] gds IH]; simpl; auto.
  destruct (gen_params_one m gd); simpl; f_equal; auto.
Qed.

Lemma gen_params_dom:
  forall m gds id, In id (map fst gds) ->
  exists ps, (gen_params m gds) ! id = Some ps.
Proof.
  intros. unfold gen_params. apply PTree_Properties.of_list_dom.
  rewrite map_fst_gen_params. auto.
Qed.

Theorem gen_prog_defs_external:
  forall a_ge tr (gds: list (ident * globdef Asm.fundef unit)) id ef,
  In (id, Gfun (AST.External ef)) gds ->
  exists cnt params,
  In (id, Gfun (gen_fundef a_ge (funs_data_of_defs gds) cnt params (get_id_tr tr id) (AST.External ef)))
     (gen_prog_defs a_ge tr gds).
Proof.
  intros a_ge tr gds id ef IN.
  assert (D: In id (map fst gds)).
  { change id with (fst (id, @Gfun Asm.fundef unit (AST.External ef))). apply in_map; auto. }
  destruct (gen_counter_defs_dom (next_id gds) gds id D) as [[cnt cd] C].
  destruct (gen_params_dom (next_id (map snd (PTree.elements (gen_counter_defs (next_id gds) gds)))) gds id D) as [ps P].
  exists cnt, ps.
  unfold gen_prog_defs. apply in_or_app. left.
  apply in_map_iff. exists (id, Gfun (AST.External ef)). split; auto.
  cbn zeta beta iota. rewrite C, P. reflexivity.
Qed.

Corollary gen_prog_defs_external_decl:
  forall a_ge tr (gds: list (ident * globdef Asm.fundef unit)) id ef,
  In (id, Gfun (AST.External ef)) gds ->
  In (id, Gfun (Ctypes.External ef (list_typ_to_typelist (sig_args (ef_sig ef)))
                                (rettype_to_type_ext (sig_res (ef_sig ef))) (sig_cc (ef_sig ef))))
     (gen_prog_defs a_ge tr gds).
Proof.
  intros. destruct (gen_prog_defs_external a_ge tr gds id ef H) as (cnt & ps & IN).
  rewrite gen_fundef_external in IN. exact IN.
Qed.

Lemma sig_has_any_mismatch:
  forall ef, sig_has_any (ef_sig ef) = true ->
  ef_sig ef <> signature_of_type (list_typ_to_typelist (sig_args (ef_sig ef)))
                                 (rettype_to_type_ext (sig_res (ef_sig ef))) (sig_cc (ef_sig ef)).
Proof.
  intros ef H E. rewrite E, signature_of_type_no_any in H. discriminate.
Qed.

Theorem bt_defs_rejected:
  forall (W_t: Asm.program) tr (p: Clight.program) id ef,
  Ctypes.prog_defs p = gen_prog_defs (Genv.globalenv W_t) tr (AST.prog_defs W_t) ->
  In (id, Gfun (AST.External ef)) (AST.prog_defs W_t) ->
  sig_has_any (ef_sig ef) = true ->
  (exists e, Cshmgen.transl_program p = Error e) /\
  (exists e, transf_clight_program p = Error e).
Proof.
  intros W_t tr p id ef DEFS IN ANY.
  pose proof (gen_prog_defs_external_decl (Genv.globalenv W_t) tr _ id ef IN) as IN'.
  rewrite <- DEFS in IN'.
  pose proof (sig_has_any_mismatch ef ANY) as NE.
  split.
  - eapply cshmgen_rejects_bad_external; eauto.
  - eapply transf_clight_program_rejects_bad_external; eauto.
Qed.

Corollary gen_program_does_not_compile:
  forall tr (W_t: Asm.program) id ef,
  In (id, Gfun (AST.External ef)) (AST.prog_defs W_t) ->
  sig_has_any (ef_sig ef) = true ->
  (exists e, Cshmgen.transl_program (gen_program tr W_t) = Error e) /\
  (exists e, transf_clight_program (gen_program tr W_t) = Error e).
Proof.
  intros. eapply bt_defs_rejected; eauto. reflexivity.
Qed.

Corollary gen_prog_defs_external_accepted:
  forall a_ge tr (gds: list (ident * globdef Asm.fundef unit)) id ef ce,
  In (id, Gfun (AST.External ef)) gds ->
  sig_has_any (ef_sig ef) = false ->
  exists targs tres cc,
    In (id, Gfun (Ctypes.External ef targs tres cc)) (gen_prog_defs a_ge tr gds) /\
    Cshmgen.transl_fundef ce id (Ctypes.External ef targs tres cc) = OK (AST.External ef).
Proof.
  intros. do 3 eexists. split. eapply gen_prog_defs_external_decl; eauto.
  rewrite <- (gen_fundef_external a_ge (funs_data_of_defs gds) xH nil (get_id_tr tr id)).
  rewrite gen_fundef_external_transl, H0. reflexivity.
Qed.

(** ** (d) Programs compiled from C have no any-typed [External] *)

Definition no_any_ext {F V: Type} (p: AST.program (AST.fundef F) V) : Prop :=
  forall id ef, In (id, Gfun (AST.External ef)) (AST.prog_defs p) ->
  sig_has_any (ef_sig ef) = false.

Theorem cshmgen_match_no_any:
  forall p tp, Cshmgenproof.match_prog p tp -> no_any_ext tp.
Proof.
  intros p tp [L _] id ef IN.
  destruct (list_forall2_in_right _ _ _ _ L IN) as ([id' gd] & _ & _ & M).
  simpl in M. inv M.
  match goal with H: Cshmgenproof.match_fundef _ _ _ |- _ => inv H end.
  match goal with H: ef_sig _ = signature_of_type _ _ _ |- _ => rewrite H end.
  apply signature_of_type_no_any.
Qed.

Lemma match_program_gen_no_any:
  forall {C F1 V1 F2 V2: Type} {LC: Linker C}
         (mf: C -> AST.fundef F1 -> AST.fundef F2 -> Prop) (mv: V1 -> V2 -> Prop) ctx p tp,
  (forall cu f ef, mf cu f (AST.External ef) -> f = AST.External ef) ->
  match_program_gen mf mv ctx p tp -> no_any_ext p -> no_any_ext tp.
Proof.
  intros C F1 V1 F2 V2 LC mf mv ctx p tp EXT [L _] N id ef IN.
  destruct (list_forall2_in_right _ _ _ _ L IN) as ([id' gd] & IN' & E & M).
  simpl in E, M. subst id'. inv M.
  match goal with H: mf _ _ (AST.External ef) |- _ => apply EXT in H; subst end.
  eapply N; eauto.
Qed.

Lemma transf_partial_fundef_ext:
  forall {A B: Type} (tf: A -> res B) f ef,
  transf_partial_fundef tf f = OK (AST.External ef) -> f = AST.External ef.
Proof.
  intros A B tf [fi|efi] ef H; simpl in H.
  - destruct (tf fi); simpl in H; discriminate.
  - inv H; auto.
Qed.

Lemma transf_fundef_ext:
  forall {A B: Type} (tf: A -> B) f ef,
  AST.External ef = AST.transf_fundef tf f -> f = AST.External ef.
Proof.
  intros A B tf [fi|efi] ef H; simpl in H; inv H; auto.
Qed.

Ltac pass_no_any :=
  let p := fresh "p" in let tp := fresh "tp" in let M := fresh "M" in
  intros p tp M; red in M; unfold match_program in M;
  eapply match_program_gen_no_any with (2 := M);
  let cu := fresh "cu" in let f := fresh "f" in let ef := fresh "ef" in let H := fresh "H" in
  intros cu f ef H;
  first [ eapply transf_partial_fundef_ext; exact H
        | eapply transf_fundef_ext; exact H ].

Lemma cminorgen_no_any: forall p tp, Cminorgenproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma selection_no_any: forall p tp, Selectionproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof.
  intros p tp M; red in M; unfold match_program in M.
  eapply match_program_gen_no_any with (2 := M).
  intros cu f ef (hf & hf_c & _ & _ & H). eapply transf_partial_fundef_ext; exact H.
Qed.

Lemma rtlgen_no_any: forall p tp, RTLgenproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma tailcall_no_any: forall p tp, Tailcallproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma inlining_no_any: forall p tp, Inliningproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma renumber_no_any: forall p tp, Renumberproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma constprop_no_any: forall p tp, Constpropproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma cse_no_any: forall p tp, CSEproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma deadcode_no_any: forall p tp, Deadcodeproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma unusedglob_no_any: forall p tp, Unusedglobproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof.
  intros p tp (u & _ & M) N id ef IN.
  assert (D: (prog_defmap tp) ! id = Some (Gfun (AST.External ef))).
  { apply prog_defmap_norepet; auto. apply (Unusedglobproof.match_prog_unique _ _ _ M). }
  rewrite (Unusedglobproof.match_prog_def _ _ _ M) in D.
  destruct (Unusedglob.IS.mem id u); try discriminate.
  eapply N. apply in_prog_defmap; eauto.
Qed.

Lemma alloc_no_any: forall p tp, Allocproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma tunneling_no_any: forall p tp, Tunnelingproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma linearize_no_any: forall p tp, Linearizeproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma cleanuplabels_no_any: forall p tp, CleanupLabelsproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma debugvar_no_any: forall p tp, Debugvarproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma stacking_no_any: forall p tp, Stackingproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma asmgen_no_any: forall p tp, Asmgenproof.match_prog p tp -> no_any_ext p -> no_any_ext tp.
Proof. pass_no_any. Qed.

Lemma match_if_no_any:
  forall {F V: Type} (flag: unit -> bool)
         (R: AST.program (AST.fundef F) V -> AST.program (AST.fundef F) V -> Prop) p tp,
  (forall p tp, R p tp -> no_any_ext p -> no_any_ext tp) ->
  match_if flag R p tp -> no_any_ext p -> no_any_ext tp.
Proof.
  unfold match_if. intros F V flag R p tp H. destruct (flag tt); intros; subst; eauto.
Qed.

Theorem match_prog_Clight_no_any:
  forall p tp, match_prog_Clight p tp -> no_any_ext tp.
Proof.
  unfold match_prog_Clight; simpl.
  intros p1 tp (p2 & M2 & p3 & M3 & p4 & M4 & p5 & M5 & p6 & M6 & p7 & M7 &
                p8 & M8 & p9 & M9 & p10 & M10 & p11 & M11 & p12 & M12 & p13 & M13 &
                p14 & M14 & p15 & M15 & p16 & M16 & p17 & M17 & p18 & M18 &
                p19 & M19 & p20 & M20 & p21 & M21 & E).
  subst tp.
  pose proof (cshmgen_match_no_any _ _ M3) as N3.
  pose proof (cminorgen_no_any _ _ M4 N3) as N4.
  pose proof (selection_no_any _ _ M5 N4) as N5.
  pose proof (rtlgen_no_any _ _ M6 N5) as N6.
  pose proof (match_if_no_any _ _ _ _ tailcall_no_any M7 N6) as N7.
  pose proof (inlining_no_any _ _ M8 N7) as N8.
  pose proof (renumber_no_any _ _ M9 N8) as N9.
  pose proof (match_if_no_any _ _ _ _ constprop_no_any M10 N9) as N10.
  pose proof (match_if_no_any _ _ _ _ renumber_no_any M11 N10) as N11.
  pose proof (match_if_no_any _ _ _ _ cse_no_any M12 N11) as N12.
  pose proof (match_if_no_any _ _ _ _ deadcode_no_any M13 N12) as N13.
  pose proof (unusedglob_no_any _ _ M14 N13) as N14.
  pose proof (alloc_no_any _ _ M15 N14) as N15.
  pose proof (tunneling_no_any _ _ M16 N15) as N16.
  pose proof (linearize_no_any _ _ M17 N16) as N17.
  pose proof (cleanuplabels_no_any _ _ M18 N17) as N18.
  pose proof (match_if_no_any _ _ _ _ debugvar_no_any M19 N18) as N19.
  pose proof (stacking_no_any _ _ M20 N19) as N20.
  exact (asmgen_no_any _ _ M21 N20).
Qed.

Theorem match_prog_no_any:
  forall p tp, Compiler.match_prog p tp -> no_any_ext tp.
Proof.
  unfold Compiler.match_prog; simpl.
  intros p tp (p1 & _ & H).
  apply (match_prog_Clight_no_any p1 tp). exact H.
Qed.

Corollary transf_clight_program_no_any:
  forall p tp, transf_clight_program p = OK tp -> no_any_ext tp.
Proof.
  intros. apply match_prog_Clight_no_any with p. apply transf_clight_program_match; auto.
Qed.

Corollary transf_c_program_no_any:
  forall p tp, transf_c_program p = OK tp -> no_any_ext tp.
Proof.
  intros. apply match_prog_no_any with p. apply transf_c_program_match; auto.
Qed.

(** *** Linking *)

Local Transparent Linker_prog Linker_def Linker_fundef.

Lemma link_fundef_external:
  forall {F: Type} {CF: has_comp F} (f1 f2: AST.fundef F) ef,
  Linking.link_fundef f1 f2 = Some (AST.External ef) -> f1 = AST.External ef.
Proof.
  intros F CF [fi1|ef1] [fi2|ef2] ef; simpl; intros H; try discriminate.
  - destruct ef2; try discriminate. destruct (eq_compartment _ _); discriminate.
  - destruct ef1; try discriminate. destruct (eq_compartment _ _); discriminate.
  - destruct (external_function_eq ef1 ef2); inv H; auto.
Qed.

Theorem link_no_any:
  forall {F V: Type} {CF: has_comp F} {LV: Linker V}
         (p1 p2 p: AST.program (AST.fundef F) V),
  link p1 p2 = Some p -> no_any_ext p1 -> no_any_ext p2 -> no_any_ext p.
Proof.
  intros F V CF LV p1 p2 p L N1 N2 id ef IN.
  apply link_prog_inv in L. destruct L as (_ & _ & _ & E). subst p. simpl in IN.
  apply PTree.elements_complete in IN. rewrite PTree.gcombine in IN by auto.
  unfold link_prog_merge in IN.
  destruct ((prog_defmap p1) ! id) as [gd1|] eqn:G1;
  destruct ((prog_defmap p2) ! id) as [gd2|] eqn:G2; try discriminate.
  - simpl in IN. unfold Linking.link_def in IN.
    destruct gd1 as [f1|v1], gd2 as [f2|v2]; try discriminate;
      [|destruct (link v1 v2); discriminate].
    destruct (link f1 f2) as [f|] eqn:LF; inv IN.
    apply link_fundef_external in LF. subst f1.
    eapply N1. apply in_prog_defmap; eauto.
  - inv IN. eapply N1. apply in_prog_defmap; eauto.
  - inv IN. eapply N2. apply in_prog_defmap; eauto.
Qed.

Theorem W_t_no_any:
  forall (p: Clight.program) (p_compiled Ct W_t: Asm.program),
  transf_clight_program p = OK p_compiled ->
  link p_compiled Ct = Some W_t ->
  no_any_ext Ct -> no_any_ext W_t.
Proof.
  intros. eapply link_no_any; eauto. eapply transf_clight_program_no_any; eauto.
Qed.

Corollary bt_externals_accepted:
  forall (p: Clight.program) (p_compiled Ct W_t: Asm.program) tr id ef ce,
  transf_clight_program p = OK p_compiled ->
  link p_compiled Ct = Some W_t ->
  no_any_ext Ct ->
  In (id, Gfun (AST.External ef)) (AST.prog_defs W_t) ->
  exists targs tres cc,
    In (id, Gfun (Ctypes.External ef targs tres cc))
       (gen_prog_defs (Genv.globalenv W_t) tr (AST.prog_defs W_t)) /\
    Cshmgen.transl_fundef ce id (Ctypes.External ef targs tres cc) = OK (AST.External ef).
Proof.
  intros. apply gen_prog_defs_external_accepted; auto.
  eapply (W_t_no_any p p_compiled Ct W_t); eauto.
Qed.

Theorem link_keeps_context_external:
  forall (p_compiled Ct W_t: Asm.program) id ef,
  link p_compiled Ct = Some W_t ->
  (prog_defmap Ct) ! id = Some (Gfun (AST.External ef)) ->
  (prog_defmap p_compiled) ! id = None ->
  In (id, Gfun (AST.External ef)) (AST.prog_defs W_t).
Proof.
  intros p_compiled Ct W_t id ef L G2 G1.
  apply link_prog_inv in L. destruct L as (_ & _ & _ & E). subst W_t. simpl.
  apply PTree.elements_correct. rewrite PTree.gcombine by auto.
  rewrite G1, G2. reflexivity.
Qed.

Lemma link_with_external:
  forall {F: Type} {CF: has_comp F} (f1: AST.fundef F) ef f,
  Linking.link_fundef f1 (AST.External ef) = Some f ->
  (f1 = AST.External ef /\ f = AST.External ef) \/
  (exists fi cp name sg, f1 = AST.Internal fi /\ ef = EF_external cp name sg /\ f = AST.Internal fi).
Proof.
  intros F CF [fi|ef1] ef f; simpl; intros H.
  - destruct ef; try discriminate. destruct (eq_compartment _ _); inv H. right; eauto 8.
  - destruct (external_function_eq ef1 ef); inv H. left; auto.
Qed.

Theorem link_context_external_cases:
  forall (p_compiled Ct W_t: Asm.program) id ef gd1,
  no_any_ext p_compiled ->
  link p_compiled Ct = Some W_t ->
  (prog_defmap Ct) ! id = Some (Gfun (AST.External ef)) ->
  sig_has_any (ef_sig ef) = true ->
  (prog_defmap p_compiled) ! id = Some gd1 ->
  exists f cp name sg, gd1 = Gfun (AST.Internal f) /\ ef = EF_external cp name sg /\
    (prog_defmap W_t) ! id = Some (Gfun (AST.Internal f)).
Proof.
  intros p_compiled Ct W_t id ef gd1 N L G2 ANY G1.
  pose proof L as L'.
  apply link_prog_inv in L'. destruct L' as (_ & LINK & _ & E).
  destruct (LINK id gd1 _ G1 G2) as (_ & _ & gd & LG).
  subst W_t. rewrite prog_defmap_elements, PTree.gcombine by auto. rewrite G1, G2.
  simpl in LG |- *. unfold Linking.link_def in LG |- *.
  destruct gd1 as [f1|v1]; [|discriminate].
  destruct (link f1 (AST.External ef)) as [f|] eqn:LF; [|discriminate].
  apply link_with_external in LF.
  destruct LF as [[-> ->] | (fi & cp & name & sg & -> & -> & ->)].
  - exfalso. rewrite (N id ef) in ANY; [discriminate|]. apply in_prog_defmap; auto.
  - exists fi, cp, name, sg. auto.
Qed.

Corollary assumption1_fails_gen_program:
  forall (p_compiled Ct W_t: Asm.program) tr id ef,
  link p_compiled Ct = Some W_t ->
  (prog_defmap Ct) ! id = Some (Gfun (AST.External ef)) ->
  sig_has_any (ef_sig ef) = true ->
  (prog_defmap p_compiled) ! id = None ->
  exists e, transf_clight_program (gen_program tr W_t) = Error e.
Proof.
  intros. eapply (bt_defs_rejected W_t tr (gen_program tr W_t)); eauto.
  eapply link_keeps_context_external; eauto.
Qed.

(** ** Any split of the back-translated program has a part that does not compile

    security/RSC.v states Assumption 1 as the axiom [backtranslation_compiles]
    about an abstract [backtranslation pol s t = (p, C)] with
    [link p C = Some W] ([backtranslation_correct]); the connection to
    [gen_program] is not formalized.  Whatever [p] and [C] are, if their
    link [W] has the definitions generated from [W_t] and [W_t] has an
    any-typed [External], then [p] or [C] does not compile: Clight linking
    produces a declaration only from an identical declaration of one side. *)

Local Transparent Ctypes.Linker_program Ctypes.Linker_fundef.

Lemma clight_link_fundef_external:
  forall {F: Type} {CF: has_comp F} (f1 f2: Ctypes.fundef F) ef targs tres cc,
  Ctypes.link_fundef f1 f2 = Some (Ctypes.External ef targs tres cc) ->
  f1 = Ctypes.External ef targs tres cc.
Proof.
  intros F CF [fi1|ef1 a1 r1 c1] [fi2|ef2 a2 r2 c2] ef targs tres cc; simpl; intros H; try discriminate.
  - destruct ef2; try discriminate. destruct (eq_compartment _ _); discriminate.
  - destruct ef1; try discriminate. destruct (eq_compartment _ _); discriminate.
  - match type of H with (if ?c then _ else _) = _ => destruct c end; inv H; auto.
Qed.

Theorem clight_link_external_side:
  forall (p C W: Clight.program) id ef targs tres cc,
  link p C = Some W ->
  In (id, Gfun (Ctypes.External ef targs tres cc)) (Ctypes.prog_defs W) ->
  In (id, Gfun (Ctypes.External ef targs tres cc)) (Ctypes.prog_defs p) \/
  In (id, Gfun (Ctypes.External ef targs tres cc)) (Ctypes.prog_defs C).
Proof.
  intros p C W id ef targs tres cc L IN.
  simpl in L. unfold link_program in L.
  destruct (link (program_of_program p) (program_of_program C)) as [pw|] eqn:LP; try discriminate.
  destruct (lift_option (link (prog_types p) (prog_types C))) as [[typs EQ]|EQ]; try discriminate.
  destruct (link_build_composite_env (prog_types p) (prog_types C) typs
       (prog_comp_env p) (prog_comp_env C) (prog_comp_env_eq p)
       (prog_comp_env_eq C) EQ) as (env & P & Q & R).
  inv L. simpl in IN.
  apply link_prog_inv in LP. destruct LP as (_ & _ & yes & E). subst pw. simpl in IN.
  apply PTree.elements_complete in IN. rewrite PTree.gcombine in IN by auto.
  unfold link_prog_merge in IN.
  destruct ((prog_defmap (program_of_program p)) ! id) as [gd1|] eqn:G1;
  destruct ((prog_defmap (program_of_program C)) ! id) as [gd2|] eqn:G2; try discriminate.
  - simpl in IN. unfold Linking.link_def in IN.
    destruct gd1 as [f1|v1], gd2 as [f2|v2]; try discriminate;
      [|destruct (link v1 v2); discriminate].
    destruct (link f1 f2) as [f|] eqn:LF; inv IN.
    apply clight_link_fundef_external in LF. subst f1.
    left. apply in_prog_defmap in G1. exact G1.
  - inv IN. left. apply in_prog_defmap in G1. exact G1.
  - inv IN. right. apply in_prog_defmap in G2. exact G2.
Qed.

Theorem bt_split_does_not_compile:
  forall (W_t: Asm.program) tr (p C W: Clight.program) id ef,
  link p C = Some W ->
  Ctypes.prog_defs W = gen_prog_defs (Genv.globalenv W_t) tr (AST.prog_defs W_t) ->
  In (id, Gfun (AST.External ef)) (AST.prog_defs W_t) ->
  sig_has_any (ef_sig ef) = true ->
  (exists e, transf_clight_program p = Error e) \/
  (exists e, transf_clight_program C = Error e).
Proof.
  intros W_t tr p C W id ef L DEFS IN ANY.
  pose proof (gen_prog_defs_external_decl (Genv.globalenv W_t) tr _ id ef IN) as IN'.
  rewrite <- DEFS in IN'.
  pose proof (sig_has_any_mismatch ef ANY) as NE.
  destruct (clight_link_external_side p C W _ _ _ _ _ L IN') as [INp|INC].
  - left. eapply transf_clight_program_rejects_bad_external; eauto.
  - right. eapply transf_clight_program_rejects_bad_external; eauto.
Qed.

(** ** A concrete instance *)

Definition sg_any : signature := mksignature (Tany32 :: nil) (Tret Tany64) cc_default.
Definition ef_any : external_function := EF_external default_compartment "f_any"%string sg_any.
Definition W_ex : Asm.program :=
  mkprogram ((1%positive, Gfun (AST.External ef_any)) :: nil) nil 2%positive Policy.empty_pol.

Example W_ex_bt_does_not_compile:
  forall tr, exists e, transf_clight_program (gen_program tr W_ex) = Error e.
Proof.
  intros tr. apply (gen_program_does_not_compile tr W_ex 1%positive ef_any).
  - left; reflexivity.
  - reflexivity.
Qed.

Example W_ex_cshmgen_error:
  Cshmgen.transl_program (gen_program nil W_ex) =
  Error (MSG "In function " :: CTX 1%positive :: MSG ": "
         :: MSG "Cshmgen.transl_fundef: wrong external signature" :: nil).
Proof. vm_compute. reflexivity. Qed.
