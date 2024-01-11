Require Import FunInd.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Memory Events Globalenvs Builtins Determinism.


Local Open Scope string_scope.
Local Open Scope list_scope.

(** Error monad with options or lists *)

Declare Scope option_monad_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => None end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => None end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z , W <- A ; B" := (match A with Some (X, Y, Z, W) => B | None => None end)
  (at level 200, X ident, Y ident, Z ident, W ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation " 'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Declare Scope list_monad_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => nil end)
  (at level 200, X ident, A at level 100, B at level 200)
  : list_monad_scope.

Notation " 'check' A ; B" := (if A then B else nil)
  (at level 200, A at level 100, B at level 200)
  : list_monad_scope.

Local Open Scope option_monad_scope.

Section Exec.

Variable F V: Type.
Context {CF: has_comp F}.
Variable ge: Genv.t F V.

Definition eventval_of_val (v: val) (t: typ) : option eventval :=
  match v with
  | Vint i => check (typ_eq t AST.Tint); Some (EVint i)
  | Vfloat f => check (typ_eq t AST.Tfloat); Some (EVfloat f)
  | Vsingle f => check (typ_eq t AST.Tsingle); Some (EVsingle f)
  | Vlong n => check (typ_eq t AST.Tlong); Some (EVlong n)
  | Vptr b ofs =>
      do id <- Genv.invert_symbol ge b;
      check (Genv.public_symbol ge id);
      check (typ_eq t AST.Tptr);
      Some (EVptr_global id ofs)
  | _ => None
  end.

Fixpoint list_eventval_of_val (vl: list val) (tl: list typ) : option (list eventval) :=
  match vl, tl with
  | nil, nil => Some nil
  | v1::vl, t1::tl =>
      do ev1 <- eventval_of_val v1 t1;
      do evl <- list_eventval_of_val vl tl;
      Some (ev1 :: evl)
  | _, _ => None
  end.

Definition val_of_eventval (ev: eventval) (t: typ) : option val :=
  match ev with
  | EVint i => check (typ_eq t AST.Tint); Some (Vint i)
  | EVfloat f => check (typ_eq t AST.Tfloat); Some (Vfloat f)
  | EVsingle f => check (typ_eq t AST.Tsingle); Some (Vsingle f)
  | EVlong n => check (typ_eq t AST.Tlong); Some (Vlong n)
  | EVptr_global id ofs =>
      check (Genv.public_symbol ge id);
      check (typ_eq t AST.Tptr);
      do b <- Genv.find_symbol ge id;
      Some (Vptr b ofs)
  end.

Ltac mydestr :=
  match goal with
  | [ |- None = Some _ -> _ ] => let X := fresh "X" in intro X; discriminate
  | [ |- Some _ = Some _ -> _ ] => let X := fresh "X" in intro X; inv X
  | [ |- match ?x with Some _ => _ | None => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
  | [ |- match ?x with true => _ | false => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
  | [ |- match ?x with left _ => _ | right _ => _ end = Some _ -> _ ] => destruct x; mydestr
  | _ => idtac
  end.

Lemma eventval_of_val_sound:
  forall v t ev, eventval_of_val v t = Some ev -> eventval_match (Genv.to_senv ge) ev t v.
Proof.
  intros until ev. destruct v; simpl; mydestr; constructor.
  auto. apply Genv.invert_find_symbol; auto.
Qed.

Lemma eventval_of_val_complete:
  forall ev t v, eventval_match (Genv.to_senv ge) ev t v -> eventval_of_val v t = Some ev.
Proof.
  induction 1; simpl.
- auto.
- auto.
- auto.
- auto.
- rewrite (Genv.find_invert_symbol _ _ H0). simpl in H; rewrite H.
  rewrite dec_eq_true. auto.
Qed.

Lemma list_eventval_of_val_sound:
  forall vl tl evl, list_eventval_of_val vl tl = Some evl -> eventval_list_match (Genv.to_senv ge) evl tl vl.
Proof with try discriminate.
  induction vl; destruct tl; simpl; intros; inv H.
  constructor.
  destruct (eventval_of_val a t) as [ev1|] eqn:?...
  destruct (list_eventval_of_val vl tl) as [evl'|] eqn:?...
  inv H1. constructor. apply eventval_of_val_sound; auto. eauto.
Qed.

Lemma list_eventval_of_val_complete:
  forall evl tl vl, eventval_list_match (Genv.to_senv ge) evl tl vl -> list_eventval_of_val vl tl = Some evl.
Proof.
  induction 1; simpl. auto.
  rewrite (eventval_of_val_complete _ _ _ H). rewrite IHeventval_list_match. auto.
Qed.

Lemma val_of_eventval_sound:
  forall ev t v, val_of_eventval ev t = Some v -> eventval_match (Genv.to_senv ge) ev t v.
Proof.
  intros until v. destruct ev; simpl; mydestr; constructor; auto.
Qed.

Lemma val_of_eventval_complete:
  forall ev t v, eventval_match (Genv.to_senv ge) ev t v -> val_of_eventval ev t = Some v.
Proof.
  induction 1; simpl.
- auto.
- auto.
- auto.
- auto.
- simpl in *. rewrite H, H0. rewrite dec_eq_true. auto.
Qed.

Definition get_call_trace (cp cp': compartment) (vf: val) (vargs: list val) (tyargs: list typ): option trace :=
  match Genv.type_of_call cp cp' with
  | Genv.CrossCompartmentCall =>
      match vf with
      | Vptr b ofs =>
          match Genv.invert_symbol ge b with
          | Some i =>
              match list_eventval_of_val vargs tyargs with
              | Some vl => Some (Event_call cp cp' i vl :: E0)
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | _ => Some E0
  end.

Lemma get_call_trace_eq:
  forall cp cp' vf vargs tyargs t,
    call_trace ge cp cp' vf vargs tyargs t <-> get_call_trace cp cp' vf vargs tyargs = Some t.
Proof.
  intros. split.
  - intros H. unfold get_call_trace.
    inv H. destruct (Genv.type_of_call cp cp'); try congruence.
    erewrite H0, H2, list_eventval_of_val_complete; eauto.
  - unfold get_call_trace.
    intros H.
    destruct (Genv.type_of_call cp cp') eqn:TOC;
      inv H; [constructor; auto; congruence |].
    destruct vf; try congruence.
    destruct (Genv.invert_symbol ge b) eqn:IS; [| congruence].
    destruct (list_eventval_of_val vargs tyargs) eqn:LEOV; [| congruence].
    inv H1. econstructor; eauto.
    eapply list_eventval_of_val_sound; eauto.
Qed.

Definition get_return_trace (cp cp': compartment) (vres: val) (ty: rettype): option trace :=
  match Genv.type_of_call cp cp' with
  | Genv.CrossCompartmentCall =>
      match eventval_of_val vres (proj_rettype ty) with
      | Some v => Some (Event_return cp cp' v :: E0)
      | None => None
      end
  | _ => Some E0
  end.

Lemma get_return_trace_eq:
  forall cp cp' vres ty t,
    return_trace ge cp cp' vres ty t <->
      get_return_trace cp cp' vres ty = Some t.
Proof.
  intros. split.
  - intros H. unfold get_return_trace.
    inv H. destruct (Genv.type_of_call cp cp'); try congruence.
    rewrite H0. rewrite (eventval_of_val_complete res); auto.
  - unfold get_return_trace.
    intros H.
    destruct (Genv.type_of_call cp cp') eqn:TOC;
      inv H; [constructor; auto; congruence |].
    destruct (eventval_of_val vres (proj_rettype ty)) eqn:LEOV; [| congruence].
    inv H1. unfold E0. econstructor; eauto.
    eapply eventval_of_val_sound; eauto.
Qed.

(* Section MEMACCESS. *)

(** Volatile memory accesses. *)

Definition do_volatile_load (w: world) (chunk: memory_chunk) (cp: compartment) (m: mem) (b: block) (ofs: ptrofs)
                             : option (world * trace * val) :=
  if Genv.block_is_volatile ge b then
    do id <- Genv.invert_symbol ge b;
    check (flowsto_dec (Senv.find_comp (Genv.to_senv ge) id) cp);
    match nextworld_vload w chunk id ofs with
    | None => None
    | Some(res, w') =>
        check (flowsto_dec (eventval_comp (Genv.to_senv ge) res) (Senv.find_comp (Genv.to_senv ge) id));
        do vres <- val_of_eventval res (type_of_chunk chunk);
        Some(w', Event_vload chunk id ofs res :: nil, Val.load_result chunk vres)
    end
  else
    do v <- Mem.load chunk m b (Ptrofs.unsigned ofs) cp;
    Some(w, E0, v).

Definition do_volatile_store (w: world) (chunk: memory_chunk) (cp: compartment) (m: mem) (b: block) (ofs: ptrofs) (v: val)
                             : option (world * trace * mem * val) :=
  if Genv.block_is_volatile ge b then
    do id <- Genv.invert_symbol ge b;
    check (flowsto_dec (Senv.find_comp (Genv.to_senv ge) id) cp);
    do ev <- eventval_of_val (Val.load_result chunk v) (type_of_chunk chunk);
    check (flowsto_dec (eventval_comp (Genv.to_senv ge) ev) (Senv.find_comp (Genv.to_senv ge) id));
    do w' <- nextworld_vstore w chunk id ofs ev;
    Some(w', Event_vstore chunk id ofs ev :: nil, m, v)
  else
    do m' <- Mem.store chunk m b (Ptrofs.unsigned ofs) v cp;
    Some(w, E0, m', v).

Lemma do_volatile_load_sound:
  forall w chunk cp m b ofs w' t v,
  do_volatile_load w chunk cp m b ofs = Some(w', t, v) ->
  volatile_load (Genv.to_senv ge) cp chunk m b ofs t v /\ possible_trace w t w'.
Proof.
  intros until v. unfold do_volatile_load. mydestr.
  destruct p as [ev w'']. mydestr.
  split. constructor; auto. apply Genv.invert_find_symbol; auto.
  apply val_of_eventval_sound; auto.
  econstructor. constructor; eauto. constructor.
  split. econstructor; eauto.
  Local Transparent Mem.load.
  unfold Mem.load in Heqo.
  revert Heqo; mydestr; inv v0; inv H0; auto.
  constructor.
Qed.

Lemma do_volatile_load_complete:
  forall w chunk cp m b ofs w' t v ,
  volatile_load (Genv.to_senv ge) cp chunk m b ofs t v -> possible_trace w t w' ->
  do_volatile_load w chunk cp m b ofs = Some(w', t, v).
Proof.
  unfold do_volatile_load; intros. inv H; simpl in *.
  rewrite H1. rewrite (Genv.find_invert_symbol _ _ H2). inv H0. inv H8. inv H10. rewrite H12.
  destruct flowsto_dec; try congruence.
  destruct flowsto_dec; try congruence.
  rewrite (val_of_eventval_complete _ _ _ H4). auto.
  rewrite H1. rewrite H2. inv H0. auto.
Qed.

Lemma do_volatile_store_sound:
  forall w chunk cp m b ofs v w' t m' v',
  do_volatile_store w chunk cp m b ofs v = Some(w', t, m', v') ->
  volatile_store (Genv.to_senv ge) cp chunk m b ofs v t m' /\ possible_trace w t w' /\ v' = v.
Proof.
  intros until v'. unfold do_volatile_store. mydestr.
  split. constructor; auto. apply Genv.invert_find_symbol; auto.
  apply eventval_of_val_sound; auto.
  split. econstructor. constructor; eauto. constructor. auto.
  split.
  constructor; auto. eapply Mem.store_can_access_block_1; eauto.
  split. constructor; auto. auto.
Qed.

Lemma do_volatile_store_complete:
  forall w chunk cp m b ofs v w' t m',
  volatile_store (Genv.to_senv ge) cp chunk m b ofs v t m' -> possible_trace w t w' ->
  do_volatile_store w chunk cp m b ofs v = Some(w', t, m', v).
Proof.
  unfold do_volatile_store; intros. inv H; simpl in *.
  rewrite H1. rewrite (Genv.find_invert_symbol _ _ H2).
  rewrite (eventval_of_val_complete _ _ _ H4).
  inv H0. inv H8. inv H10. rewrite H12.
  destruct flowsto_dec; try congruence.
  destruct flowsto_dec; try congruence.
  auto.
  rewrite H1. rewrite H2. inv H0. auto.
Qed.

(** External calls *)

Variable do_external_function:
  string -> signature -> Senv.t -> compartment -> world -> list val -> mem -> option (world * trace * val * mem).

Hypothesis do_external_function_sound:
  forall id sg ge cp vargs m t vres m' w w',
  do_external_function id sg ge cp w vargs m = Some(w', t, vres, m') ->
  external_functions_sem id sg ge cp vargs m t vres m' /\ possible_trace w t w'.

Hypothesis do_external_function_complete:
  forall id sg ge cp vargs m t vres m' w w',
  external_functions_sem id sg ge cp vargs m t vres m' ->
  possible_trace w t w' ->
  do_external_function id sg ge cp w vargs m = Some(w', t, vres, m').

Variable do_inline_assembly:
 string -> signature -> Senv.t -> compartment -> world -> list val -> mem -> option (world * trace * val * mem).

Hypothesis do_inline_assembly_sound:
  forall txt sg ge cp vargs m t vres m' w w',
  do_inline_assembly txt sg ge cp w vargs m = Some(w', t, vres, m') ->
  inline_assembly_sem txt sg ge cp vargs m t vres m' /\ possible_trace w t w'.

Hypothesis do_inline_assembly_complete:
  forall txt sg ge cp vargs m t vres m' w w',
  inline_assembly_sem txt sg ge cp vargs m t vres m' ->
  possible_trace w t w' ->
  do_inline_assembly txt sg ge cp w vargs m = Some(w', t, vres, m').

Definition do_ef_volatile_load (chunk: memory_chunk)
       (cp: compartment) (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b ofs :: nil => do w',t,v <- do_volatile_load w chunk cp m b ofs; Some(w',t,v,m)
  | _ => None
  end.

Definition do_ef_volatile_store (chunk: memory_chunk)
       (cp: compartment) (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b ofs :: v :: nil => do w',t,m',v' <- do_volatile_store w chunk cp m b ofs v; Some(w',t,Vundef,m')
  | _ => None
  end.

Definition do_ef_volatile_load_global (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
       (cp: compartment) (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do b <- Genv.find_symbol ge id; do_ef_volatile_load chunk cp w (Vptr b ofs :: vargs) m.

Definition do_ef_volatile_store_global (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
       (cp: compartment) (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do b <- Genv.find_symbol ge id; do_ef_volatile_store chunk cp w (Vptr b ofs :: vargs) m.

Definition do_alloc_size (v: val) : option ptrofs :=
  match v with
  | Vint n => if Archi.ptr64 then None else Some (Ptrofs.of_int n)
  | Vlong n => if Archi.ptr64 then Some (Ptrofs.of_int64 n) else None
  | _ => None
  end.

Definition do_ef_malloc (cp: compartment)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | v :: nil =>
      do sz <- do_alloc_size v;
      let (m', b) := Mem.alloc m cp (- size_chunk Mptr) (Ptrofs.unsigned sz) in
      do m'' <- Mem.store Mptr m' b (- size_chunk Mptr) v cp;
      Some(w, E0, Vptr b Ptrofs.zero, m'')
  | _ => None
  end.

Definition do_ef_free (cp: compartment)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b lo :: nil =>
      do vsz <- Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) cp;
      do sz <- do_alloc_size vsz;
      check (zlt 0 (Ptrofs.unsigned sz));
      do m' <- Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) cp;
      Some(w, E0, Vundef, m')
  | Vint n :: nil =>
      if Int.eq_dec n Int.zero && negb Archi.ptr64
      then Some(w, E0, Vundef, m)
      else None
  | Vlong n :: nil =>
      if Int64.eq_dec n Int64.zero && Archi.ptr64
      then Some(w, E0, Vundef, m)
      else None
  | _ => None
  end.

Definition memcpy_args_ok
  (sz al: Z) (bdst: block) (odst: Z) (bsrc: block) (osrc: Z) : Prop :=
      (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
   /\ sz >= 0 /\ (al | sz)
   /\ (sz > 0 -> (al | osrc))
   /\ (sz > 0 -> (al | odst))
   /\ (bsrc <> bdst \/ osrc = odst \/ osrc + sz <= odst \/ odst + sz <= osrc).

Definition do_ef_memcpy (sz al: Z)
       (cp: compartment) (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr bdst odst :: Vptr bsrc osrc :: nil =>
      if decide (memcpy_args_ok sz al bdst (Ptrofs.unsigned odst) bsrc (Ptrofs.unsigned osrc)) then
        do bytes <- Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz cp;
        do m' <- Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes cp;
        Some(w, E0, Vundef, m')
      else None
  | _ => None
  end.

Definition do_ef_annot (text: string) (targs: list typ)
       (cp: compartment) (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do args <- list_eventval_of_val vargs targs;
  check (forallb (fun ev => flowsto_dec (eventval_comp (Genv.to_senv ge) ev) cp)) args;
  Some(w, Event_annot text args :: E0, Vundef, m).

Definition do_ef_annot_val (text: string) (targ: typ)
       (cp: compartment) (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | varg :: nil =>
      do arg <- eventval_of_val varg targ;
      check (flowsto_dec (eventval_comp (Genv.to_senv ge) arg) cp);
      Some(w, Event_annot text (arg :: nil) :: E0, varg, m)
  | _ => None
  end.

Definition do_ef_debug (kind: positive) (text: ident) (targs: list typ)
       (cp: compartment) (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  Some(w, E0, Vundef, m).

Definition do_builtin_or_external (name: string) (sg: signature) (cp: compartment)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match lookup_builtin_function name sg with
  | Some bf => match builtin_function_sem bf vargs with Some v => Some(w, E0, v, m) | None => None end
  | None    => do_external_function name sg (Genv.to_senv ge) cp w vargs m
  end.

Definition do_external (ef: external_function):
       compartment -> world -> list val -> mem -> option (world * trace * val * mem) :=
  match ef with
  | EF_external name sg => do_external_function name sg (Genv.to_senv ge)
  | EF_builtin name sg => do_builtin_or_external name sg
  | EF_runtime name sg => do_builtin_or_external name sg
  | EF_vload chunk => do_ef_volatile_load chunk
  | EF_vstore chunk => do_ef_volatile_store chunk
  | EF_malloc => do_ef_malloc
  | EF_free => do_ef_free
  | EF_memcpy sz al => do_ef_memcpy sz al
  | EF_annot kind text targs => do_ef_annot text targs
  | EF_annot_val kind text targ => do_ef_annot_val text targ
  | EF_inline_asm text sg clob => do_inline_assembly text sg (Genv.to_senv ge)
  | EF_debug kind text targs => do_ef_debug kind text targs
  end.

Lemma do_ef_external_sound:
  forall ef cp w vargs m w' t vres m',
  do_external ef cp w vargs m = Some(w', t, vres, m') ->
  external_call ef (Genv.to_senv ge) cp vargs m t vres m' /\ possible_trace w t w'.
Proof with try congruence.
  intros until m'.
  assert (SIZE: forall v sz, do_alloc_size v = Some sz -> v = Vptrofs sz).
  { intros until sz; unfold Vptrofs; destruct v; simpl; destruct Archi.ptr64 eqn:SF;
    intros EQ; inv EQ; f_equal; symmetry; eauto with ptrofs. }
  assert (BF_EX: forall name sg,
    do_builtin_or_external name sg cp w vargs m = Some (w', t, vres, m') ->
    builtin_or_external_sem name sg (Genv.to_senv ge) cp vargs m t vres m' /\ possible_trace w t w').
  { unfold do_builtin_or_external, builtin_or_external_sem; intros.
    destruct (lookup_builtin_function name sg ) as [bf|].
  - destruct (builtin_function_sem bf vargs) as [vres1|] eqn:BF; inv H.
    split. constructor; auto. constructor.
  - eapply do_external_function_sound; eauto.
  }
  destruct ef; simpl.
- (* EF_external *)
  eapply do_external_function_sound; eauto.
- (* EF_builtin *)
  eapply BF_EX; eauto.
- (* EF_runtime *)
  eapply BF_EX; eauto.
- (* EF_vload *)
  unfold do_ef_volatile_load. destruct vargs... destruct v... destruct vargs...
  mydestr. destruct p as [[w'' t''] v]; mydestr.
  exploit do_volatile_load_sound; eauto. intuition. econstructor; eauto.
- (* EF_vstore *)
  unfold do_ef_volatile_store. destruct vargs... destruct v... destruct vargs... destruct vargs...
  mydestr. destruct p as [[[w'' t''] m''] v'']. mydestr.
  exploit do_volatile_store_sound; eauto. intuition. econstructor; eauto.
- (* EF_malloc *)
  unfold do_ef_malloc. destruct vargs... destruct vargs... mydestr.
  destruct (Mem.alloc m cp (- size_chunk Mptr) (Ptrofs.unsigned i)) as [m1 b] eqn:?. mydestr.
  split. apply SIZE in Heqo. subst v. econstructor; eauto. constructor.
- (* EF_free *)
  unfold do_ef_free. destruct vargs... destruct v...
+ destruct vargs... mydestr; InvBooleans; subst i.
  replace (Vint Int.zero) with Vnullptr. split; constructor.
  apply negb_true_iff in H0. unfold Vnullptr; rewrite H0; auto.
+ destruct vargs... mydestr; InvBooleans; subst i.
  replace (Vlong Int64.zero) with Vnullptr. split; constructor.
  unfold Vnullptr; rewrite H0; auto.
+ destruct vargs... mydestr.
  split. apply SIZE in Heqo0. econstructor; eauto. congruence. lia.
  constructor.
- (* EF_memcpy *)
  unfold do_ef_memcpy. destruct vargs... destruct v... destruct vargs...
  destruct v... destruct vargs... mydestr.
  apply Decidable_sound in Heqb1. red in Heqb1.
  split. econstructor; eauto; tauto. constructor.
- (* EF_annot *)
  unfold do_ef_annot. mydestr.
  split. constructor. apply list_eventval_of_val_sound; auto.
  rewrite forallb_forall in Heqb. rewrite Forall_forall.
  intros. exploit Heqb; eauto. now destruct flowsto_dec; eauto.
  econstructor. constructor; eauto. constructor.
- (* EF_annot_val *)
  unfold do_ef_annot_val. destruct vargs... destruct vargs... mydestr.
  split. constructor. apply eventval_of_val_sound; auto. auto.
  econstructor. constructor; eauto. constructor.
- (* EF_inline_asm *)
  eapply do_inline_assembly_sound; eauto.
- (* EF_debug *)
  unfold do_ef_debug. mydestr. split; constructor.
Qed.

Lemma do_ef_external_complete:
  forall ef cp w vargs m w' t vres m',
  external_call ef (Genv.to_senv ge) cp vargs m t vres m' -> possible_trace w t w' ->
  do_external ef cp w vargs m = Some(w', t, vres, m').
Proof.
  intros.
  assert (SIZE: forall n, do_alloc_size (Vptrofs n) = Some n).
  { unfold Vptrofs, do_alloc_size; intros; destruct Archi.ptr64 eqn:SF.
    rewrite Ptrofs.of_int64_to_int64; auto.
    rewrite Ptrofs.of_int_to_int; auto. }
  assert (BF_EX: forall name sg,
    builtin_or_external_sem name sg (Genv.to_senv ge) cp vargs m t vres m' ->
    do_builtin_or_external name sg cp w vargs m = Some (w', t, vres, m')).
  { unfold do_builtin_or_external, builtin_or_external_sem; intros.
    destruct (lookup_builtin_function name sg) as [bf|].
  - inv H1. inv H0. rewrite H2. auto.
  - eapply do_external_function_complete; eauto.
  }
  destruct ef; simpl in *.
- (* EF_external *)
  eapply do_external_function_complete; eauto.
- (* EF_builtin *)
  eapply BF_EX; eauto.
- (* EF_runtime *)
  eapply BF_EX; eauto.
- (* EF_vload *)
  inv H; unfold do_ef_volatile_load.
  exploit do_volatile_load_complete; eauto. intros EQ; rewrite EQ; auto.
- (* EF_vstore *)
  inv H; unfold do_ef_volatile_store.
  exploit do_volatile_store_complete; eauto. intros EQ; rewrite EQ; auto.
- (* EF_malloc *)
  inv H; unfold do_ef_malloc.
  inv H0. erewrite SIZE by eauto. rewrite H1, H2. auto.
- (* EF_free *)
  inv H; unfold do_ef_free.
+ inv H0. rewrite H1. erewrite SIZE by eauto. rewrite zlt_true. rewrite H3. auto. lia.
+ inv H0. unfold Vnullptr; destruct Archi.ptr64; auto.
- (* EF_memcpy *)
  inv H; unfold do_ef_memcpy.
  inv H0. rewrite Decidable_complete. rewrite H7; rewrite H8; auto.
  red. tauto.
- (* EF_annot *)
  inv H; unfold do_ef_annot. inv H0. inv H7. inv H5.
  rewrite (list_eventval_of_val_complete _ _ _ H1).
  rewrite Forall_forall in H2.
  assert (H: forallb (fun ev : eventval => flowsto_dec (eventval_comp (Genv.to_senv ge) ev) cp) args = true).
  { rewrite forallb_forall. intros. exploit H2; eauto. now destruct flowsto_dec; eauto. }
  now rewrite H.
- (* EF_annot_val *)
  inv H; unfold do_ef_annot_val. inv H0. inv H7. inv H5.
  rewrite (eventval_of_val_complete _ _ _ H1).
  now destruct flowsto_dec; auto.
- (* EF_inline_asm *)
  eapply do_inline_assembly_complete; eauto.
- (* EF_debug *)
  inv H. inv H0. reflexivity.
Qed.

End Exec.
