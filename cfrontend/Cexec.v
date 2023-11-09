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

(** Animating the CompCert C semantics *)

Require Import FunInd.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Memory Events Globalenvs Builtins Determinism Exec.
Require Import Ctypes Cop Csyntax Csem.
Require Cstrategy.

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

Definition is_val (a: expr) : option (val * type) :=
  match a with
  | Eval v ty => Some(v, ty)
  | _ => None
  end.

Lemma is_val_inv:
  forall a v ty, is_val a = Some(v, ty) -> a = Eval v ty.
Proof.
  intros until ty. destruct a; simpl; congruence.
Qed.

Definition is_loc (a: expr) : option (block * ptrofs * bitfield * type) :=
  match a with
  | Eloc b ofs bf ty => Some(b, ofs, bf, ty)
  | _ => None
  end.

Lemma is_loc_inv:
  forall a b ofs bf ty, is_loc a = Some(b, ofs, bf, ty) -> a = Eloc b ofs bf ty.
Proof.
  intros until ty. destruct a; simpl; congruence.
Qed.

Local Open Scope option_monad_scope.

Fixpoint is_val_list (al: exprlist) : option (list (val * type)) :=
  match al with
  | Enil => Some nil
  | Econs a1 al => do vt1 <- is_val a1; do vtl <- is_val_list al; Some(vt1::vtl)
  end.

Definition is_skip (s: statement) : {s = Sskip} + {s <> Sskip}.
Proof.
  destruct s; (left; congruence) || (right; congruence).
Defined.

(** * Events, volatile memory accesses, and external functions. *)

Section EXEC.

Variable ge: genv.

(** Accessing locations *)

Definition do_deref_loc (w: world) (ty: type) (m: mem) (b: block) (ofs: ptrofs) (bf: bitfield) (cp: compartment) : option (world * trace * val) :=
  match bf with
  | Full =>
    match access_mode ty with
    | By_value chunk =>
      match type_is_volatile ty with
      | false => do v <- Mem.loadv chunk m (Vptr b ofs) (Some cp); Some(w, E0, v)
      | true => do_volatile_load _ _ ge w chunk cp m b ofs
      end
    | By_reference => Some(w, E0, Vptr b ofs)
    | By_copy => Some(w, E0, Vptr b ofs)
    | _ => None
    end
  | Bits sz sg pos width =>
    match ty with
    | Tint sz1 sg1 _ =>
      check (intsize_eq sz1 sz &&
             signedness_eq sg1 (if zlt width (bitsize_intsize sz) then Signed else sg) &&
             zle 0 pos && zlt 0 width && zle width (bitsize_intsize sz) && zle (pos + width) (bitsize_carrier sz));
      match Mem.loadv (chunk_for_carrier sz) m (Vptr b ofs) (Some cp) with
      | Some (Vint c) => Some (w, E0, Vint (bitfield_extract sz sg pos width c))
      | _ => None
      end
    | _ => None
    end
  end.

Definition assign_copy_ok (ty: type) (b: block) (ofs: ptrofs) (b': block) (ofs': ptrofs) : Prop :=
  (alignof_blockcopy ge ty | Ptrofs.unsigned ofs') /\ (alignof_blockcopy ge ty | Ptrofs.unsigned ofs) /\
  (b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
           \/ Ptrofs.unsigned ofs' + sizeof ge ty <= Ptrofs.unsigned ofs
           \/ Ptrofs.unsigned ofs + sizeof ge ty <= Ptrofs.unsigned ofs').

Remark check_assign_copy:
  forall (ty: type) (b: block) (ofs: ptrofs) (b': block) (ofs': ptrofs),
  { assign_copy_ok ty b ofs b' ofs' } + {~ assign_copy_ok ty b ofs b' ofs' }.
Proof with try (right; intuition lia).
  intros. unfold assign_copy_ok.
  destruct (Zdivide_dec (alignof_blockcopy ge ty) (Ptrofs.unsigned ofs')); auto...
  destruct (Zdivide_dec (alignof_blockcopy ge ty) (Ptrofs.unsigned ofs)); auto...
  assert (Y: {b' <> b \/
              Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs \/
              Ptrofs.unsigned ofs' + sizeof ge ty <= Ptrofs.unsigned ofs \/
              Ptrofs.unsigned ofs + sizeof ge ty <= Ptrofs.unsigned ofs'} +
           {~(b' <> b \/
              Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs \/
              Ptrofs.unsigned ofs' + sizeof ge ty <= Ptrofs.unsigned ofs \/
              Ptrofs.unsigned ofs + sizeof ge ty <= Ptrofs.unsigned ofs')}).
  destruct (eq_block b' b); auto.
  destruct (zeq (Ptrofs.unsigned ofs') (Ptrofs.unsigned ofs)); auto.
  destruct (zle (Ptrofs.unsigned ofs' + sizeof ge ty) (Ptrofs.unsigned ofs)); auto.
  destruct (zle (Ptrofs.unsigned ofs + sizeof ge ty) (Ptrofs.unsigned ofs')); auto.
  right; intuition lia.
  destruct Y... left; intuition lia.
Defined.

Definition do_assign_loc (w: world) (ty: type) (m: mem) (b: block) (ofs: ptrofs) (bf: bitfield) (v: val) (cp: compartment): option (world * trace * mem * val) :=
  match bf with
  | Full =>
    match access_mode ty with
    | By_value chunk =>
        match type_is_volatile ty with
        | false => do m' <- Mem.storev chunk m (Vptr b ofs) v cp; Some(w, E0, m', v)
        | true => do_volatile_store _ _ ge w chunk cp m b ofs v
        end
    | By_copy =>
        match v with
        | Vptr b' ofs' =>
            if check_assign_copy ty b ofs b' ofs' then
              do bytes <- Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ge ty) (Some cp);
              do m' <- Mem.storebytes m b (Ptrofs.unsigned ofs) bytes cp;
              Some(w, E0, m', v)
            else None
        | _ => None
        end
    | _ => None
    end
  | Bits sz sg pos width =>
    check (zle 0 pos && zlt 0 width && zle width (bitsize_intsize sz) && zle (pos + width) (bitsize_carrier sz));
    match ty, v, Mem.loadv (chunk_for_carrier sz) m (Vptr b ofs) (Some cp) with
    | Tint sz1 sg1 _, Vint n, Some (Vint c) =>
        check (intsize_eq sz1 sz &&
               signedness_eq sg1 (if zlt width (bitsize_intsize sz) then Signed else sg));
        do m' <- Mem.storev (chunk_for_carrier sz) m (Vptr b ofs)
                            (Vint ((Int.bitfield_insert (first_bit sz pos width) width c n))) cp;
        Some (w, E0, m', Vint (bitfield_normalize sz sg width n))
    | _, _, _ => None
    end
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

Lemma do_deref_loc_sound:
  forall w ty m b ofs bf cp w' t v,
  do_deref_loc w ty m b ofs bf cp = Some(w', t, v) ->
  deref_loc ge cp ty m b ofs bf t v /\ possible_trace w t w'.
Proof.
  unfold do_deref_loc; intros until v.
  destruct bf.
- destruct (access_mode ty) eqn:?; mydestr.
  intros. exploit do_volatile_load_sound; eauto. intuition. eapply deref_loc_volatile; eauto.
  split. eapply deref_loc_value; eauto. constructor.
  split. eapply deref_loc_reference; eauto. constructor.
  split. eapply deref_loc_copy; eauto. constructor.
- mydestr. destruct ty; mydestr. InvBooleans. subst i. destruct v0; mydestr.
  split. eapply deref_loc_bitfield; eauto. econstructor; eauto. constructor.
Qed.

Lemma do_deref_loc_complete:
  forall w ty m b ofs bf cp w' t v,
  deref_loc ge cp ty m b ofs bf t v -> possible_trace w t w' ->
  do_deref_loc w ty m b ofs bf cp = Some(w', t, v).
Proof.
  unfold do_deref_loc; intros. inv H.
- inv H0. rewrite H1; rewrite H2; rewrite H3; auto.
- rewrite H1; rewrite H2. apply do_volatile_load_complete; auto.
- inv H0. rewrite H1. auto.
- inv H0. rewrite H1. auto.
- inv H0. inv H1.
  unfold proj_sumbool; rewrite ! dec_eq_true, ! zle_true, ! zlt_true by lia. cbn.
  cbn in H4; rewrite H4. auto.
Qed.

Lemma do_assign_loc_sound:
  forall w ty m b ofs bf v cp w' t m' v',
  do_assign_loc w ty m b ofs bf v cp = Some(w', t, m', v') ->
  assign_loc ge cp ty m b ofs bf v t m' v' /\ possible_trace w t w'.
Proof.
  unfold do_assign_loc; intros until v'.
  destruct bf.
- destruct (access_mode ty) eqn:?; mydestr.
  intros. exploit do_volatile_store_sound; eauto. intros (P & Q & R). subst v'. intuition. eapply assign_loc_volatile; eauto.
  split. eapply assign_loc_value; eauto. constructor.
  destruct v; mydestr. destruct a as [P [Q R]].
  split. eapply assign_loc_copy; eauto. constructor.
- mydestr. InvBooleans.
  destruct ty; mydestr. destruct v; mydestr. destruct v; mydestr. InvBooleans. subst s i.
  split. eapply assign_loc_bitfield; eauto. econstructor; eauto. constructor.
Qed.

Lemma do_assign_loc_complete:
  forall w ty m b ofs bf v cp w' t m' v',
  assign_loc ge cp ty m b ofs bf v t m' v' -> possible_trace w t w' ->
  do_assign_loc w ty m b ofs bf v cp = Some(w', t, m', v').
Proof.
  unfold do_assign_loc; intros. inv H.
- inv H0. rewrite H1; rewrite H2; rewrite H3; auto.
- rewrite H1; rewrite H2. apply do_volatile_store_complete; auto.
- rewrite H1. destruct (check_assign_copy ty b ofs b' ofs').
  inv H0. rewrite H5; rewrite H6; auto.
  elim n. red; tauto.
- inv H0. inv H1.
  unfold proj_sumbool; rewrite ! zle_true, ! zlt_true by lia. cbn.
  rewrite ! dec_eq_true.
  cbn in H4; rewrite H4. cbn in H5; rewrite H5. auto.
Qed.

Variable do_external_function:
  compartment -> string -> signature -> Senv.t -> world -> list val -> mem -> option (world * trace * val * mem).

Hypothesis do_external_function_sound:
  forall cp id sg ge vargs m t vres m' w w',
  do_external_function cp id sg ge w vargs m = Some(w', t, vres, m') ->
  external_functions_sem cp id sg ge vargs m t vres m' /\ possible_trace w t w'.

Hypothesis do_external_function_complete:
  forall cp id sg ge vargs m t vres m' w w',
  external_functions_sem cp id sg ge vargs m t vres m' ->
  possible_trace w t w' ->
  do_external_function cp id sg ge w vargs m = Some(w', t, vres, m').

Variable do_inline_assembly:
  compartment -> string -> signature -> Senv.t -> world -> list val -> mem -> option (world * trace * val * mem).

Hypothesis do_inline_assembly_sound:
  forall txt sg ge cp vargs m t vres m' w w',
  do_inline_assembly cp txt sg ge w vargs m = Some(w', t, vres, m') ->
  inline_assembly_sem cp txt sg ge vargs m t vres m' /\ possible_trace w t w'.

Hypothesis do_inline_assembly_complete:
  forall txt sg ge cp vargs m t vres m' w w',
  inline_assembly_sem cp txt sg ge vargs m t vres m' ->
  possible_trace w t w' ->
  do_inline_assembly cp txt sg ge w vargs m = Some(w', t, vres, m').

(** * Reduction of expressions *)

Inductive reduction: Type :=
  | Lred (rule: string) (l': expr) (m': mem)
  | Rred (rule: string) (r': expr) (m': mem) (t: trace)
  | Callred (rule: string) (fd: fundef) (args: list val) (tyres: type) (t: trace) (m': mem)
  | Stuckred.

Section EXPRS.

Variable e: env.
Variable w: world.

Fixpoint sem_cast_arguments (vtl: list (val * type)) (tl: typelist) (m: mem) : option (list val) :=
  match vtl, tl with
  | nil, Tnil => Some nil
  | (v1,t1)::vtl, Tcons t1' tl =>
      do v <- sem_cast v1 t1 t1' m; do vl <- sem_cast_arguments vtl tl m; Some(v::vl)
  | _, _ => None
  end.

(** The result of stepping an expression is a list [ll] of possible reducts.
  Each element of [ll] is a pair of a context and the result of reducing
  inside this context (see type [reduction] above).
  The list [ll] is empty if the expression is fully reduced
   (it's [Eval] for a r-value and [Eloc] for a l-value).
*)

Definition reducts (A: Type): Type := list ((expr -> A) * reduction).

Definition topred (r: reduction) : reducts expr :=
  ((fun (x: expr) => x), r) :: nil.

Definition stuck : reducts expr :=
  ((fun (x: expr) => x), Stuckred) :: nil.

Definition incontext {A B: Type} (ctx: A -> B) (ll: reducts A) : reducts B :=
  map (fun z => ((fun (x: expr) => ctx(fst z x)), snd z)) ll.

Definition incontext2 {A1 A2 B: Type}
                     (ctx1: A1 -> B) (ll1: reducts A1)
                     (ctx2: A2 -> B) (ll2: reducts A2) : reducts B :=
  incontext ctx1 ll1 ++ incontext ctx2 ll2.

Declare Scope reducts_monad_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => stuck end)
  (at level 200, X ident, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => stuck end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => stuck end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'do' X , Y , Z , W <- A ; B" := (match A with Some (X, Y, Z, W) => B | None => stuck end)
  (at level 200, X ident, Y ident, Z ident, W ident, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation " 'check' A ; B" := (if A then B else stuck)
  (at level 200, A at level 100, B at level 200)
  : reducts_monad_scope.

Local Open Scope reducts_monad_scope.

Fixpoint step_expr (cp: compartment) (k: kind) (a: expr) (m: mem): reducts expr :=
  match k, a with
  | LV, Eloc b ofs bf ty =>
      nil
  | LV, Evar x ty =>
      match e!x with
      | Some(b, ty') =>
          check type_eq ty ty';
          topred (Lred "red_var_local" (Eloc b Ptrofs.zero Full ty) m)
      | None =>
          do b <- Genv.find_symbol ge x;
          check Genv.allowed_addrof_b ge cp x;
          topred (Lred "red_var_global" (Eloc b Ptrofs.zero Full ty) m)
      end
  | LV, Ederef r ty =>
      match is_val r with
      | Some(Vptr b ofs, ty') =>
          topred (Lred "red_deref" (Eloc b ofs Full ty) m)
      | Some _ =>
          stuck
      | None =>
          incontext (fun x => Ederef x ty) (step_expr cp RV r m)
      end
  | LV, Efield r f ty =>
      match is_val r with
      | Some(Vptr b ofs, ty') =>
          match ty' with
          | Tstruct id _ =>
              do co <- ge.(genv_cenv)!id;
              match field_offset ge f (co_members co) with
              | Error _ => stuck
              | OK (delta, bf) => topred (Lred "red_field_struct" (Eloc b (Ptrofs.add ofs (Ptrofs.repr delta)) bf ty) m)
              end
          | Tunion id _ =>
              do co <- ge.(genv_cenv)!id;
              match union_field_offset ge f (co_members co) with
              | Error _ => stuck
              | OK (delta, bf) => topred (Lred "red_field_union" (Eloc b (Ptrofs.add ofs (Ptrofs.repr delta)) bf ty) m)
              end
          | _ => stuck
          end
      | Some _ =>
          stuck
      | None =>
          incontext (fun x => Efield x f ty) (step_expr cp RV r m)
      end
  | RV, Eval v ty =>
      nil
  | RV, Evalof l ty =>
      match is_loc l with
      | Some(b, ofs, bf, ty') =>
          check type_eq ty ty';
          do w',t,v <- do_deref_loc w ty m b ofs bf cp;
          topred (Rred "red_rvalof" (Eval v ty) m t)
      | None =>
          incontext (fun x => Evalof x ty) (step_expr cp LV l m)
      end
  | RV, Eaddrof l ty =>
      match is_loc l with
      | Some(b, ofs, bf, ty') =>
          match bf with Full => topred (Rred "red_addrof" (Eval (Vptr b ofs) ty) m E0)
                      | Bits _ _ _ _ => stuck
          end
      | None => incontext (fun x => Eaddrof x ty) (step_expr cp LV l m)
      end
  | RV, Eunop op r1 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do v <- sem_unary_operation op v1 ty1 m;
          topred (Rred "red_unop" (Eval v ty) m E0)
      | None =>
          incontext (fun x => Eunop op x ty) (step_expr cp RV r1 m)
      end
  | RV, Ebinop op r1 r2 ty =>
      match is_val r1, is_val r2 with
      | Some(v1, ty1), Some(v2, ty2) =>
          do v <- sem_binary_operation ge op v1 ty1 v2 ty2 m;
          topred (Rred "red_binop" (Eval v ty) m E0)
      | _, _ =>
         incontext2 (fun x => Ebinop op x r2 ty) (step_expr cp RV r1 m)
                    (fun x => Ebinop op r1 x ty) (step_expr cp RV r2 m)
      end
  | RV, Ecast r1 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do v <- sem_cast v1 ty1 ty m;
          topred (Rred "red_cast" (Eval v ty) m E0)
      | None =>
          incontext (fun x => Ecast x ty) (step_expr cp RV r1 m)
      end
  | RV, Eseqand r1 r2 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do b <- bool_val v1 ty1 m;
          if b then topred (Rred "red_seqand_true" (Eparen r2 type_bool ty) m E0)
               else topred (Rred "red_seqand_false" (Eval (Vint Int.zero) ty) m E0)
      | None =>
          incontext (fun x => Eseqand x r2 ty) (step_expr cp RV r1 m)
      end
  | RV, Eseqor r1 r2 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do b <- bool_val v1 ty1 m;
          if b then topred (Rred "red_seqor_true" (Eval (Vint Int.one) ty) m E0)
               else topred (Rred "red_seqor_false" (Eparen r2 type_bool ty) m E0)
      | None =>
          incontext (fun x => Eseqor x r2 ty) (step_expr cp RV r1 m)
      end
  | RV, Econdition r1 r2 r3 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do b <- bool_val v1 ty1 m;
          topred (Rred "red_condition" (Eparen (if b then r2 else r3) ty ty) m E0)
      | None =>
          incontext (fun x => Econdition x r2 r3 ty) (step_expr cp RV r1 m)
      end
  | RV, Esizeof ty' ty =>
      topred (Rred "red_sizeof" (Eval (Vptrofs (Ptrofs.repr (sizeof ge ty'))) ty) m E0)
  | RV, Ealignof ty' ty =>
      topred (Rred "red_alignof" (Eval (Vptrofs (Ptrofs.repr (alignof ge ty'))) ty) m E0)
  | RV, Eassign l1 r2 ty =>
      match is_loc l1, is_val r2 with
      | Some(b, ofs, bf, ty1), Some(v2, ty2) =>
          check type_eq ty1 ty;
          do v <- sem_cast v2 ty2 ty1 m;
          do w',t,m',v' <- do_assign_loc w ty1 m b ofs bf v cp;
          topred (Rred "red_assign" (Eval v' ty) m' t)
      | _, _ =>
         incontext2 (fun x => Eassign x r2 ty) (step_expr cp LV l1 m)
                    (fun x => Eassign l1 x ty) (step_expr cp RV r2 m)
      end
  | RV, Eassignop op l1 r2 tyres ty =>
      match is_loc l1, is_val r2 with
      | Some(b, ofs, bf, ty1), Some(v2, ty2) =>
          check type_eq ty1 ty;
          do w',t,v1 <- do_deref_loc w ty1 m b ofs bf cp;
          let r' := Eassign (Eloc b ofs bf ty1)
                           (Ebinop op (Eval v1 ty1) (Eval v2 ty2) tyres) ty1 in
          topred (Rred "red_assignop" r' m t)
      | _, _ =>
         incontext2 (fun x => Eassignop op x r2 tyres ty) (step_expr cp LV l1 m)
                    (fun x => Eassignop op l1 x tyres ty) (step_expr cp RV r2 m)
      end
  | RV, Epostincr id l ty =>
      match is_loc l with
      | Some(b, ofs, bf, ty1) =>
          check type_eq ty1 ty;
          do w',t, v1 <- do_deref_loc w ty m b ofs bf cp;
          let op := match id with Incr => Oadd | Decr => Osub end in
          let r' :=
            Ecomma (Eassign (Eloc b ofs bf ty)
                           (Ebinop op (Eval v1 ty) (Eval (Vint Int.one) type_int32s) (incrdecr_type ty))
                           ty)
                   (Eval v1 ty) ty in
          topred (Rred "red_postincr" r' m t)
      | None =>
          incontext (fun x => Epostincr id x ty) (step_expr cp LV l m)
      end
  | RV, Ecomma r1 r2 ty =>
      match is_val r1 with
      | Some _ =>
          check type_eq (typeof r2) ty;
          topred (Rred "red_comma" r2 m E0)
      | None =>
          incontext (fun x => Ecomma x r2 ty) (step_expr cp RV r1 m)
      end
  | RV, Eparen r1 tycast ty =>
      match is_val r1 with
      | Some (v1, ty1) =>
          do v <- sem_cast v1 ty1 tycast m;
          topred (Rred "red_paren" (Eval v ty) m E0)
      | None =>
          incontext (fun x => Eparen x tycast ty) (step_expr cp RV r1 m)
      end
  | RV, Ecall r1 rargs ty =>
      match is_val r1, is_val_list rargs with
      | Some(vf, tyf), Some vtl =>
          match classify_fun tyf with
          | fun_case_f tyargs tyres cconv =>
              do fd <- Genv.find_funct ge vf;
              check (Genv.allowed_call_b ge cp vf);
              do vargs <- sem_cast_arguments vtl tyargs m;
              check type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv);
              check (match Genv.type_of_call cp (comp_of fd) with
                     | Genv.CrossCompartmentCall => forallb not_ptr_b vargs
                     | _ => true end);
              do t <- get_call_trace _ _ ge cp (comp_of fd) vf vargs (typlist_of_typelist tyargs);
              topred (Callred "red_call" fd vargs ty t m)
          | _ => stuck
          end
      | _, _ =>
          incontext2 (fun x => Ecall x rargs ty) (step_expr cp RV r1 m)
                     (fun x => Ecall r1 x ty) (step_exprlist cp rargs m)
      end
  | RV, Ebuiltin ef tyargs rargs ty =>
      match is_val_list rargs with
      | Some vtl =>
          do vargs <- sem_cast_arguments vtl tyargs m;
          check (Pos.eqb (comp_of ef) cp);
          match do_external _ _ ge do_external_function do_inline_assembly ef w vargs m with
          | None => stuck
          | Some(w',t,v,m') => topred (Rred "red_builtin" (Eval v ty) m' t)
          end
      | _ =>
          incontext (fun x => Ebuiltin ef tyargs x ty) (step_exprlist cp rargs m)
      end
  | _, _ => stuck
  end

with step_exprlist (cp: compartment) (rl: exprlist) (m: mem): reducts exprlist :=
  match rl with
  | Enil =>
      nil
  | Econs r1 rs =>
      incontext2 (fun x => Econs x rs) (step_expr cp RV r1 m)
                 (fun x => Econs r1 x) (step_exprlist cp rs m)
  end.

(** Technical properties on safe expressions. *)

Inductive imm_safe_t (cp: compartment): kind -> expr -> mem -> Prop :=
  | imm_safe_t_val: forall v ty m,
      imm_safe_t cp RV (Eval v ty) m
  | imm_safe_t_loc: forall b ofs ty bf m,
      imm_safe_t cp LV (Eloc b ofs bf ty) m
  | imm_safe_t_lred: forall to C l m l' m',
      lred ge e cp l m l' m' ->
      context LV to C ->
      imm_safe_t cp to (C l) m
  | imm_safe_t_rred: forall to C r m t r' m' w',
      rred ge cp r m t r' m' -> possible_trace w t w' ->
      context RV to C ->
      imm_safe_t cp to (C r) m
  | imm_safe_t_callred: forall to C r m fd args ty t,
      callred ge cp r m fd args ty t ->
      context RV to C ->
      imm_safe_t cp to (C r) m.

Remark imm_safe_t_imm_safe:
  forall cp k a m, imm_safe_t cp k a m -> imm_safe ge e cp k a m.
Proof.
  induction 1.
  constructor.
  constructor.
  eapply imm_safe_lred; eauto.
  eapply imm_safe_rred; eauto.
  eapply imm_safe_callred; eauto.
Qed.

Fixpoint exprlist_all_values (rl: exprlist) : Prop :=
  match rl with
  | Enil => True
  | Econs (Eval v ty) rl' => exprlist_all_values rl'
  | Econs _ _ => False
  end.

Definition invert_expr_prop (cp: compartment) (a: expr) (m: mem) : Prop :=
  match a with
  | Eloc b ofs bf ty => False
  | Evar x ty =>
      exists b,
      e!x = Some(b, ty)
      \/ (e!x = None /\ Genv.find_symbol ge x = Some b /\
            Genv.allowed_addrof ge cp x)
  | Ederef (Eval v ty1) ty =>
      exists b, exists ofs, v = Vptr b ofs
  | Eaddrof (Eloc b ofs bf ty1) ty =>
      bf = Full
  | Efield (Eval v ty1) f ty =>
      exists b, exists ofs, v = Vptr b ofs /\
      match ty1 with
      | Tstruct id _ => exists co delta bf, ge.(genv_cenv)!id = Some co /\ field_offset ge f (co_members co) = OK (delta, bf)
      | Tunion id _ => exists co delta bf, ge.(genv_cenv)!id = Some co /\ union_field_offset ge f (co_members co) = OK (delta, bf)
      | _ => False
      end
  | Eval v ty => False
  | Evalof (Eloc b ofs bf ty') ty =>
      ty' = ty /\ exists t, exists v, exists w', deref_loc ge cp ty m b ofs bf t v /\ possible_trace w t w'
  | Eunop op (Eval v1 ty1) ty =>
      exists v, sem_unary_operation op v1 ty1 m = Some v
  | Ebinop op (Eval v1 ty1) (Eval v2 ty2) ty =>
      exists v, sem_binary_operation ge op v1 ty1 v2 ty2 m = Some v
  | Ecast (Eval v1 ty1) ty =>
      exists v, sem_cast v1 ty1 ty m = Some v
  | Eseqand (Eval v1 ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eseqor (Eval v1 ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Econdition (Eval v1 ty1) r1 r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eassign (Eloc b ofs bf ty1) (Eval v2 ty2) ty =>
      exists v, exists m', exists v', exists t, exists w',
      ty = ty1 /\ sem_cast v2 ty2 ty1 m = Some v /\ assign_loc ge cp ty1 m b ofs bf v t m' v' /\ possible_trace w t w'
  | Eassignop op (Eloc b ofs bf ty1) (Eval v2 ty2) tyres ty =>
      exists t, exists v1, exists w',
      ty = ty1 /\ deref_loc ge cp ty1 m b ofs bf t v1 /\ possible_trace w t w'
  | Epostincr id (Eloc b ofs bf ty1) ty =>
      exists t, exists v1, exists w',
      ty = ty1 /\ deref_loc ge cp ty m b ofs bf t v1 /\ possible_trace w t w'
  | Ecomma (Eval v ty1) r2 ty =>
      typeof r2 = ty
  | Eparen (Eval v1 ty1) tycast ty =>
      exists v, sem_cast v1 ty1 tycast m = Some v
  | Ecall (Eval vf tyf) rargs ty =>
      exprlist_all_values rargs ->
      exists tyargs tyres cconv fd vl t,
         classify_fun tyf = fun_case_f tyargs tyres cconv
      /\ Genv.find_funct ge vf = Some fd
      /\ cast_arguments m rargs tyargs vl
      /\ type_of_fundef fd = Tfunction tyargs tyres cconv
      /\ Genv.allowed_call ge cp vf
      /\ (Genv.type_of_call cp (comp_of fd) = Genv.CrossCompartmentCall -> Forall not_ptr vl)
      /\ call_trace ge cp (comp_of fd) vf vl (typlist_of_typelist tyargs) t
  | Ebuiltin ef tyargs rargs ty =>
      exprlist_all_values rargs ->
      exists vargs t vres m' w',
         cast_arguments m rargs tyargs vargs
      /\ external_call ef ge vargs m t vres m'
      /\ comp_of ef = cp
      /\ possible_trace w t w'
  | _ => True
  end.

Lemma lred_invert:
  forall cp l m l' m', lred ge e cp l m l' m' -> invert_expr_prop cp l m.
Proof.
  induction 1; red; auto.
  exists b; auto.
  exists b; auto.
  exists b; exists ofs; auto.
  exists b; exists ofs; split; auto. exists co, delta, bf; auto.
  exists b; exists ofs; split; auto. exists co, delta, bf; auto.
Qed.

Lemma rred_invert:
  forall cp w' r m t r' m', rred ge cp r m t r' m' -> possible_trace w t w' -> invert_expr_prop cp r m.
Proof.
  induction 1; intros; red; auto.
  split; auto; exists t; exists v; exists w'; auto.
  exists v; auto.
  exists v; auto.
  exists v; auto.
  exists true; auto. exists false; auto.
  exists true; auto. exists false; auto.
  exists b; auto.
  exists v; exists m'; exists v'; exists t; exists w'; auto.
  exists t; exists v1; exists w'; auto.
  exists t; exists v1; exists w'; auto.
  exists v; auto.
  intros; exists vargs; exists t; exists vres; exists m'; exists w'; auto.
Qed.

Lemma callred_invert:
  forall cp r fd args ty t m,
  callred ge cp r m fd args ty t ->
  invert_expr_prop cp r m.
Proof.
  intros. inv H. simpl.
  intros. exists tyargs, tyres, cconv, fd, args, t; auto.
  repeat split; auto.
Qed.

Scheme context_ind2 := Minimality for context Sort Prop
  with contextlist_ind2 := Minimality for contextlist Sort Prop.
Combined Scheme context_contextlist_ind from context_ind2, contextlist_ind2.

Lemma invert_expr_context:
  (forall from to C, context from to C ->
   forall cp a m,
   invert_expr_prop cp a m ->
   invert_expr_prop cp (C a) m)
/\(forall from C, contextlist from C ->
  forall cp a m,
  invert_expr_prop cp a m ->
  ~exprlist_all_values (C a)).
Proof.
  apply context_contextlist_ind; intros; try (exploit H0; [eauto|intros]); simpl.
  auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto. intros. elim (H0 cp a m); auto.
  intros. elim (H0 cp a m); auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  red; intros. destruct (C a); auto.
  red; intros. destruct e1; auto. elim (H0 cp a m); auto.
Qed.

Lemma imm_safe_t_inv:
  forall cp k a m,
  imm_safe_t cp k a m ->
  match a with
  | Eloc _ _ _ _ => True
  | Eval _ _ => True
  | _ => invert_expr_prop cp a m
  end.
Proof.
  destruct invert_expr_context as [A B].
  intros. inv H.
  auto.
  auto.
  assert (invert_expr_prop cp (C l) m).
    eapply A; eauto. eapply lred_invert; eauto.
  red in H. destruct (C l); auto; contradiction.
  assert (invert_expr_prop cp (C r) m).
    eapply A; eauto. eapply rred_invert; eauto.
  red in H. destruct (C r); auto; contradiction.
  assert (invert_expr_prop cp (C r) m).
    eapply A; eauto. eapply callred_invert; eauto.
  red in H. destruct (C r); auto; contradiction.
Qed.

(** Soundness: if [step_expr] returns [Some ll], then every element
  of [ll] is a reduct. *)

Lemma context_compose:
  forall k2 k3 C2, context k2 k3 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  context k1 k3 (fun x => C2(C1 x))
with contextlist_compose:
  forall k2 C2, contextlist k2 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  contextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Local Hint Constructors context contextlist : core.
Local Hint Resolve context_compose contextlist_compose : core.

Definition reduction_ok (cp: compartment) (k: kind) (a: expr) (m: mem) (rd: reduction) : Prop :=
  match k, rd with
  | LV, Lred _ l' m' => lred ge e cp a m l' m'
  | RV, Rred _ r' m' t => rred ge cp a m t r' m' /\ exists w', possible_trace w t w'
  | RV, Callred _ fd args tyres t m' => callred ge cp a m fd args tyres t /\ m' = m
  | LV, Stuckred => ~imm_safe_t cp k a m
  | RV, Stuckred => ~imm_safe_t cp k a m
  | _, _ => False
  end.

Definition reducts_ok (cp: compartment) (k: kind) (a: expr) (m: mem) (ll: reducts expr) : Prop :=
  (forall C rd,
      In (C, rd) ll ->
      exists a', exists k', context k' k C /\ a = C a' /\ reduction_ok cp k' a' m rd)
  /\ (ll = nil -> match k with LV => is_loc a <> None | RV => is_val a <> None end).

Definition list_reducts_ok (cp: compartment) (al: exprlist) (m: mem) (ll: reducts exprlist) : Prop :=
  (forall C rd,
      In (C, rd) ll ->
      exists a', exists k', contextlist k' C /\ al = C a' /\ reduction_ok cp k' a' m rd)
  /\ (ll = nil -> is_val_list al <> None).

Ltac monadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some ?y |- _ ] =>
      destruct x eqn:?; [monadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some ?y |- _ ] =>
      destruct x; [monadInv|discriminate]
  | _ => idtac
  end.

Lemma sem_cast_arguments_sound:
  forall m rargs vtl tyargs vargs,
  is_val_list rargs = Some vtl ->
  sem_cast_arguments vtl tyargs m = Some vargs ->
  cast_arguments m rargs tyargs vargs.
Proof.
  induction rargs; simpl; intros.
  inv H. destruct tyargs; simpl in H0; inv H0. constructor.
  monadInv. inv H. simpl in H0. destruct p as [v1 t1]. destruct tyargs; try congruence. monadInv.
  inv H0. rewrite (is_val_inv _ _ _ Heqo). constructor. auto. eauto.
Qed.

Lemma sem_cast_arguments_complete:
  forall m al tyl vl,
  cast_arguments m al tyl vl ->
  exists vtl, is_val_list al = Some vtl /\ sem_cast_arguments vtl tyl m = Some vl.
Proof.
  induction 1.
  exists (@nil (val * type)); auto.
  destruct IHcast_arguments as [vtl [A B]].
  exists ((v, ty) :: vtl); simpl. rewrite A; rewrite B; rewrite H. auto.
Qed.

Lemma topred_ok:
  forall cp k a m rd,
  reduction_ok cp k a m rd ->
  reducts_ok cp k a m (topred rd).
Proof.
  intros. unfold topred; split; simpl; intros.
  destruct H0; try contradiction. inv H0. exists a; exists k; auto.
  congruence.
Qed.

Lemma stuck_ok:
  forall cp k a m,
  ~imm_safe_t cp k a m ->
  reducts_ok cp k a m stuck.
Proof.
  intros. unfold stuck; split; simpl; intros.
  destruct H0; try contradiction. inv H0. exists a; exists k; intuition. red. destruct k; auto.
  congruence.
Qed.

Lemma wrong_kind_ok:
  forall cp k a m,
  k <> Cstrategy.expr_kind a ->
  reducts_ok cp k a m stuck.
Proof.
  intros. apply stuck_ok. red; intros. exploit Cstrategy.imm_safe_kind; eauto.
  eapply imm_safe_t_imm_safe; eauto.
Qed.

Lemma not_invert_ok:
  forall cp k a m,
  match a with
  | Eloc _ _ _ _ => False
  | Eval _ _ => False
  | _ => invert_expr_prop cp a m -> False
  end ->
  reducts_ok cp k a m stuck.
Proof.
  intros. apply stuck_ok. red; intros.
  exploit imm_safe_t_inv; eauto. destruct a; auto.
Qed.

Lemma incontext_ok:
  forall cp k a m C res k' a',
  reducts_ok cp k' a' m res ->
  a = C a' ->
  context k' k C ->
  match k' with LV => is_loc a' = None | RV => is_val a' = None end ->
  reducts_ok cp k a m (incontext C res).
Proof.
  unfold reducts_ok, incontext; intros. destruct H. split; intros.
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eapply context_compose; eauto. rewrite V; auto.
  destruct res; simpl in H4; try congruence. destruct k'; intuition congruence.
Qed.

Lemma incontext2_ok:
  forall cp k a m k1 a1 res1 k2 a2 res2 C1 C2,
  reducts_ok cp k1 a1 m res1 ->
  reducts_ok cp k2 a2 m res2 ->
  a = C1 a1 -> a = C2 a2 ->
  context k1 k C1 -> context k2 k C2 ->
  match k1 with LV => is_loc a1 = None | RV => is_val a1 = None end
  \/ match k2 with LV => is_loc a2 = None | RV => is_val a2 = None end ->
  reducts_ok cp k a m (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_ok, incontext2, incontext; intros. destruct H; destruct H0; split; intros.
  destruct (in_app_or _ _ _ H8).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eapply context_compose; eauto. rewrite V; auto.
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eapply context_compose; eauto. rewrite H2; rewrite V; auto.
  destruct res1; simpl in H8; try congruence. destruct res2; simpl in H8; try congruence.
  destruct H5. destruct k1; intuition congruence. destruct k2; intuition congruence.
Qed.

Lemma incontext_list_ok:
  forall cp ef tyargs al ty m res,
  list_reducts_ok cp al m res ->
  is_val_list al = None ->
  reducts_ok cp RV (Ebuiltin ef tyargs al ty) m
                   (incontext (fun x => Ebuiltin ef tyargs x ty) res).
Proof.
  unfold reducts_ok, incontext; intros. destruct H. split; intros.
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res; simpl in H2. elim H1; auto. congruence.
Qed.

Lemma incontext2_list_ok:
  forall cp a1 a2 ty m res1 res2,
  reducts_ok cp RV a1 m res1 ->
  list_reducts_ok cp a2 m res2 ->
  is_val a1 = None \/ is_val_list a2 = None ->
  reducts_ok cp RV (Ecall a1 a2 ty) m
                   (incontext2 (fun x => Ecall x a2 ty) res1
                               (fun x => Ecall a1 x ty) res2).
Proof.
  unfold reducts_ok, incontext2, incontext; intros. destruct H; destruct H0; split; intros.
  destruct (in_app_or _ _ _ H4).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res1; simpl in H4; try congruence. destruct res2; simpl in H4; try congruence.
  tauto.
Qed.

Lemma incontext2_list_ok':
  forall cp a1 a2 m res1 res2,
  reducts_ok cp RV a1 m res1 ->
  list_reducts_ok cp a2 m res2 ->
  list_reducts_ok cp (Econs a1 a2) m
                     (incontext2 (fun x => Econs x a2) res1
                                 (fun x => Econs a1 x) res2).
Proof.
  unfold reducts_ok, list_reducts_ok, incontext2, incontext; intros.
  destruct H; destruct H0. split; intros.
  destruct (in_app_or _ _ _ H3).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res1; simpl in H3; try congruence. destruct res2; simpl in H3; try congruence.
  simpl. destruct (is_val a1). destruct (is_val_list a2). congruence. intuition congruence. intuition congruence.
Qed.

Lemma is_val_list_all_values:
  forall al vtl, is_val_list al = Some vtl -> exprlist_all_values al.
Proof.
  induction al; simpl; intros. auto.
  destruct (is_val r1) as [[v ty]|] eqn:?; try discriminate.
  destruct (is_val_list al) as [vtl'|] eqn:?; try discriminate.
  rewrite (is_val_inv _ _ _ Heqo). eauto.
Qed.

Ltac myinv :=
  match goal with
  | [ H: False |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H; myinv
  | [ H: exists _, _ |- _ ] => destruct H; myinv
  | _ => idtac
  end.

Theorem step_expr_sound:
  forall cp a k m, reducts_ok cp k a m (step_expr cp k a m)
with step_exprlist_sound:
  forall cp al m, list_reducts_ok cp al m (step_exprlist cp al m).
Proof with (try (apply not_invert_ok; simpl; intro; myinv; intuition congruence; fail)).
  induction a; intros; simpl; destruct k; try (apply wrong_kind_ok; simpl; congruence).
(* Eval *)
  split; intros. tauto. simpl; congruence.
(* Evar *)
  destruct (e!x) as [[b ty']|] eqn:?.
  destruct (type_eq ty ty')...
  subst. apply topred_ok; auto. apply red_var_local; auto.
  destruct (Genv.find_symbol ge x) as [b|] eqn:?...
  destruct Genv.allowed_addrof_b eqn:CHECK...
  { apply topred_ok; auto. apply red_var_global; auto.
    now apply Genv.allowed_addrof_b_reflect. }
  apply not_invert_ok. simpl. rewrite Heqo.
  intros (? & [?|(_ & _ & CONTRA)]); try easy.
  apply Genv.allowed_addrof_b_reflect in CONTRA. congruence.
(* Efield *)
  destruct (is_val a) as [[v ty'] | ] eqn:?.
  rewrite (is_val_inv _ _ _ Heqo).
  destruct v...
  destruct ty'...
  (* top struct *)
  destruct (ge.(genv_cenv)!i0) as [co|] eqn:?...
  destruct (field_offset ge f (co_members co)) as [[delta bf]|] eqn:?...
  apply topred_ok; auto. eapply red_field_struct; eauto.
  (* top union *)
  destruct (ge.(genv_cenv)!i0) as [co|] eqn:?...
  destruct (union_field_offset ge f (co_members co)) as [[delta bf]|] eqn:?...
  apply topred_ok; auto. eapply red_field_union; eauto.
  (* in depth *)
  eapply incontext_ok; eauto.
(* Evalof *)
  destruct (is_loc a) as [[[[b ofs] bf] ty']  | ] eqn:?. rewrite (is_loc_inv _ _ _ _ _ Heqo).
  (* top *)
  destruct (type_eq ty ty')... subst ty'.
  destruct (do_deref_loc w ty m b ofs bf) as [[[w' t] v] | ] eqn:?.
  exploit do_deref_loc_sound; eauto. intros [A B].
  apply topred_ok; auto. red. split. apply red_rvalof; auto. exists w'; auto.
  apply not_invert_ok; simpl; intros; myinv. exploit do_deref_loc_complete; eauto. congruence.
  (* depth *)
  eapply incontext_ok; eauto.
(* Ederef *)
  destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
  (* top *)
  destruct v... apply topred_ok; auto. apply red_deref; auto.
  (* depth *)
  eapply incontext_ok; eauto.
(* Eaddrof *)
  destruct (is_loc a) as [[[[b ofs] bf ] ty'] | ] eqn:?. rewrite (is_loc_inv _ _ _ _ _ Heqo).
  (* top *)
  destruct bf... 
  apply topred_ok; auto. split. apply red_addrof; auto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* unop *)
  destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
  (* top *)
  destruct (sem_unary_operation op v ty' m) as [v'|] eqn:?...
  apply topred_ok; auto. split. apply red_unop; auto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* binop *)
  destruct (is_val a1) as [[v1 ty1] | ] eqn:?.
  destruct (is_val a2) as [[v2 ty2] | ] eqn:?.
  rewrite (is_val_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
  (* top *)
  destruct (sem_binary_operation ge op v1 ty1 v2 ty2 m) as [v|] eqn:?...
  apply topred_ok; auto. split. apply red_binop; auto. exists w; constructor.
  (* depth *)
  eapply incontext2_ok; eauto.
  eapply incontext2_ok; eauto.
(* cast *)
  destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
  (* top *)
  destruct (sem_cast v ty' ty m) as [v'|] eqn:?...
  apply topred_ok; auto. split. apply red_cast; auto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* seqand *)
  destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
  (* top *)
  destruct (bool_val v ty' m) as [v'|] eqn:?... destruct v'.
  apply topred_ok; auto. split. eapply red_seqand_true; eauto. exists w; constructor.
  apply topred_ok; auto. split. eapply red_seqand_false; eauto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* seqor *)
  destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
  (* top *)
  destruct (bool_val v ty' m) as [v'|] eqn:?... destruct v'.
  apply topred_ok; auto. split. eapply red_seqor_true; eauto. exists w; constructor.
  apply topred_ok; auto. split. eapply red_seqor_false; eauto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* condition *)
  destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
  (* top *)
  destruct (bool_val v ty' m) as [v'|] eqn:?...
  apply topred_ok; auto. split. eapply red_condition; eauto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* sizeof *)
  apply topred_ok; auto. split. apply red_sizeof. exists w; constructor.
(* alignof *)
  apply topred_ok; auto. split. apply red_alignof. exists w; constructor.
(* assign *)
  destruct (is_loc a1) as [[[[b ofs] bf] ty1] | ] eqn:?.
  destruct (is_val a2) as [[v2 ty2] | ] eqn:?.
  rewrite (is_loc_inv _ _ _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
  (* top *)
  destruct (type_eq ty1 ty)... subst ty1.
  destruct (sem_cast v2 ty2 ty m) as [v|] eqn:?...
  destruct (do_assign_loc w ty m b ofs bf v) as [[[[w' t] m'] v']|] eqn:?.
  exploit do_assign_loc_sound; eauto. intros [P Q].
  apply topred_ok; auto. split. eapply red_assign; eauto. exists w'; auto.
  apply not_invert_ok; simpl; intros; myinv. exploit do_assign_loc_complete; eauto. congruence.
  (* depth *)
  eapply incontext2_ok; eauto.
  eapply incontext2_ok; eauto.
(* assignop *)
  destruct (is_loc a1) as [[[[b ofs] bf] ty1] | ] eqn:?.
  destruct (is_val a2) as [[v2 ty2] | ] eqn:?.
  rewrite (is_loc_inv _ _ _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
  (* top *)
  destruct (type_eq ty1 ty)... subst ty1.
  destruct (do_deref_loc w ty m b ofs bf) as [[[w' t] v] | ] eqn:?.
  exploit do_deref_loc_sound; eauto. intros [A B].
  apply topred_ok; auto. red. split. apply red_assignop; auto. exists w'; auto.
  apply not_invert_ok; simpl; intros; myinv. exploit do_deref_loc_complete; eauto. congruence.
  (* depth *)
  eapply incontext2_ok; eauto.
  eapply incontext2_ok; eauto.
(* postincr *)
  destruct (is_loc a) as [[[[b ofs] bf] ty'] | ] eqn:?. rewrite (is_loc_inv _ _ _ _ _ Heqo).
  (* top *)
  destruct (type_eq ty' ty)... subst ty'.
  destruct (do_deref_loc w ty m b ofs bf) as [[[w' t] v] | ] eqn:?.
  exploit do_deref_loc_sound; eauto. intros [A B].
  apply topred_ok; auto. red. split. apply red_postincr; auto. exists w'; auto.
  apply not_invert_ok; simpl; intros; myinv. exploit do_deref_loc_complete; eauto. congruence.
  (* depth *)
  eapply incontext_ok; eauto.
(* comma *)
  destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
  (* top *)
  destruct (type_eq (typeof a2) ty)... subst ty.
  apply topred_ok; auto. split. apply red_comma; auto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* call *)
  destruct (is_val a) as [[vf tyf] | ] eqn:?.
  destruct (is_val_list rargs) as [vtl | ] eqn:?.
  rewrite (is_val_inv _ _ _ Heqo). exploit is_val_list_all_values; eauto. intros ALLVAL.
  (* top *)
  destruct (classify_fun tyf) as [tyargs tyres cconv|] eqn:?...
  destruct (Genv.find_funct ge vf) as [fd|] eqn:?...
  destruct (Genv.allowed_call_b ge cp vf) eqn:ALLOWED...
  destruct (sem_cast_arguments vtl tyargs m) as [vargs|] eqn:?...
  destruct (type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv))...
  destruct (Genv.type_of_call cp (comp_of fd)) eqn:?...
  destruct (get_call_trace _ _ ge cp (comp_of fd) vf vargs (typlist_of_typelist tyargs)) eqn:?...
  apply topred_ok; auto. red. split; auto. eapply red_call; eauto.
  eapply sem_cast_arguments_sound; eauto.
  (* Use Heqb *)
  eapply Genv.allowed_call_reflect; eauto. congruence.
  eapply get_call_trace_eq; eauto.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
  eapply get_call_trace_eq in H5.
  rewrite Heqc in H; inv H.
  rewrite Heqo1 in H0; inv H0.
  exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. rewrite Heqo0 in P. inv P.
  rewrite Heqo2 in Q; inv Q. congruence.
  destruct (forallb not_ptr_b vargs) eqn:?...
  destruct (get_call_trace _ _ ge cp (comp_of fd) vf vargs (typlist_of_typelist tyargs)) eqn:?...
  apply topred_ok; auto. red. split; auto. eapply red_call; eauto.
  eapply sem_cast_arguments_sound; eauto.
  eapply Genv.allowed_call_reflect; eauto.
  intros. pose proof (proj1 (forallb_forall _ _) Heqb). eapply Forall_forall. intros; eapply not_ptr_reflect; eauto.
  eapply get_call_trace_eq; eauto.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
  (* apply Genv.cross_call_reflect in Heqb. *)
  assert (x2 = fd) as -> by congruence. specialize (H4 Heqc0).
  rewrite Heqc in H; inv H.
  rewrite Heqo1 in H0; inv H0.
  exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. rewrite Heqo0 in P. inv P.
  rewrite Heqo2 in Q; inv Q. eapply get_call_trace_eq in H5; congruence.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
  (* apply Genv.cross_call_reflect in Heqb. *)
  assert (x2 = fd) as -> by congruence. specialize (H4 Heqc0).
  rewrite Heqc in H; inv H.
  rewrite Heqo1 in H0; inv H0.
  exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. rewrite Heqo0 in P. inv P.
  rewrite Heqo2 in Q; inv Q.
  pose proof (proj1 (Forall_forall _ _) H4).
  eapply eq_true_false_abs with (b := forallb not_ptr_b x3); [| auto].
  eapply forallb_forall. intros. eapply not_ptr_reflect; eauto.
  destruct (get_call_trace _ _ ge cp (comp_of fd) vf vargs (typlist_of_typelist tyargs)) eqn:?...
  (* apply topred_ok; auto. red. split; auto. eapply red_call; eauto. *)
  (* eapply sem_cast_arguments_sound; eauto. *)
  (* eapply Genv.allowed_call_reflect; eauto. congruence. *)
  (* eapply get_call_trace_eq; eauto. *)
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
  (* rewrite Heqc in H; inv H. *)
  (* rewrite Heqo1 in H0; inv H0. *)
  (* exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. rewrite Heqo0 in P. inv P. *)
  (* rewrite Heqo2 in Q; inv Q. eapply get_call_trace_eq in H5; congruence. *)
  (* apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence. *)
  (* intros. apply Genv.cross_call_reflect in H; congruence. *)

  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
  exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. congruence.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
  (* Use Heqb *)
  match goal with
  | H: Genv.allowed_call _ _ _ |- _ => rewrite Genv.allowed_call_reflect in H; congruence
  end.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
  (* depth *)
  eapply incontext2_list_ok; eauto.
  eapply incontext2_list_ok; eauto.
(* builtin *)
  destruct (is_val_list rargs) as [vtl | ] eqn:?.
  exploit is_val_list_all_values; eauto. intros ALLVAL.
  (* top *)
  destruct (sem_cast_arguments vtl tyargs m) as [vargs|] eqn:?...
  destruct (Pos.eqb (comp_of ef) cp) eqn:?...
  destruct (do_external _ _ ge do_external_function do_inline_assembly ef w vargs m) as [[[[? ?] v] m'] | ] eqn:?...
  exploit do_ef_external_sound; eauto. intros [EC PT].
  apply topred_ok; auto. red. split; auto. eapply red_builtin; eauto.
  eapply sem_cast_arguments_sound; eauto. now apply Peqb_true_eq.
  exists w0; auto.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
  assert (x = vargs).
    exploit sem_cast_arguments_complete; eauto. intros [vtl' [A B]]. congruence.
  subst x. exploit do_ef_external_complete; eauto. congruence.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. subst. now rewrite Pos.eqb_refl in Heqb.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
  exploit sem_cast_arguments_complete; eauto. intros [vtl' [A B]]. congruence.
  (* depth *)
  eapply incontext_list_ok; eauto.

(* loc *)
  split; intros. tauto. simpl; congruence.
(* paren *)
  destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
  (* top *)
  destruct (sem_cast v ty' tycast m) as [v'|] eqn:?...
  apply topred_ok; auto. split. apply red_paren; auto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.

  induction al; simpl; intros.
(* nil *)
  split; intros. tauto. simpl; congruence.
(* cons *)
  eapply incontext2_list_ok'; eauto.
Qed.

Lemma step_exprlist_val_list:
  forall cp m al, is_val_list al <> None -> step_exprlist cp al m = nil.
Proof.
  induction al; simpl; intros.
  auto.
  destruct (is_val r1) as [[v1 ty1]|] eqn:?; try congruence.
  destruct (is_val_list al) eqn:?; try congruence.
  rewrite (is_val_inv _ _ _ Heqo).
  rewrite IHal. auto. congruence.
Qed.

(** Completeness part 1: [step_expr] contains all possible non-error reducts. *)

Lemma lred_topred:
  forall cp l1 m1 l2 m2,
  lred ge e cp l1 m1 l2 m2 ->
  exists rule, step_expr cp LV l1 m1 = topred (Lred rule l2 m2).
Proof.
  induction 1; simpl.
(* var local *)
  rewrite H. rewrite dec_eq_true. econstructor; eauto.
(* var global *)
  rewrite H; rewrite H0.
  assert (Genv.allowed_addrof_b ge cp x = true) as ->
    by now rewrite <- Genv.allowed_addrof_b_reflect.
  econstructor; eauto.
(* deref *)
  econstructor; eauto.
(* field struct *)
  rewrite H, H0; econstructor; eauto.
(* field union *)
  rewrite H, H0; econstructor; eauto.
Qed.

Lemma rred_topred:
  forall cp w' r1 m1 t r2 m2,
  rred ge cp r1 m1 t r2 m2 -> possible_trace w t w' ->
  exists rule, step_expr cp RV r1 m1 = topred (Rred rule r2 m2 t).
Proof.
  induction 1; simpl; intros.
(* valof *)
  rewrite dec_eq_true.
  rewrite (do_deref_loc_complete _ _ _ _ _ _ _ _ _ _ H H0). econstructor; eauto.
(* addrof *)
  inv H. econstructor; eauto.
(* unop *)
  inv H0. rewrite H; econstructor; eauto.
(* binop *)
  inv H0. rewrite H; econstructor; eauto.
(* cast *)
  inv H0. rewrite H; econstructor; eauto.
(* seqand *)
  inv H0. rewrite H; econstructor; eauto.
  inv H0. rewrite H; econstructor; eauto.
(* seqor *)
  inv H0. rewrite H; econstructor; eauto.
  inv H0. rewrite H; econstructor; eauto.
(* condition *)
  inv H0. rewrite H; econstructor; eauto.
(* sizeof *)
  inv H. econstructor; eauto.
(* alignof *)
  inv H. econstructor; eauto.
(* assign *)
  rewrite dec_eq_true. rewrite H. rewrite (do_assign_loc_complete _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
  econstructor; eauto.
(* assignop *)
  rewrite dec_eq_true. rewrite (do_deref_loc_complete _ _ _ _ _ _ _ _ _ _ H H0).
  econstructor; eauto.
(* postincr *)
  rewrite dec_eq_true. subst. rewrite (do_deref_loc_complete _ _ _ _ _ _ _ _ _ _ H H1).
  econstructor; eauto.
(* comma *)
  inv H0. rewrite dec_eq_true. econstructor; eauto.
(* paren *)
  inv H0. rewrite H; econstructor; eauto.
(* builtin *)
  exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
  subst cp.
  exploit do_ef_external_complete; eauto. intros C.
  rewrite A. rewrite B. rewrite Pos.eqb_refl. rewrite C. econstructor; eauto.
Qed.

Lemma callred_topred:
  forall cp a fd args ty t m,
  callred ge cp a m fd args ty t ->
  exists rule, step_expr cp RV a m = topred (Callred rule fd args ty t m).
Proof.
  induction 1; simpl.
  rewrite H2. exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
  rewrite A; rewrite H; rewrite B; rewrite H1; rewrite dec_eq_true.
  eapply Genv.allowed_call_reflect in ALLOWED.
  rewrite ALLOWED.
  econstructor; eauto.
  destruct (Genv.type_of_call cp (comp_of fd)) eqn:?; try reflexivity.
  eapply get_call_trace_eq in EV; rewrite EV; eauto.
  specialize (NO_CROSS_PTR eq_refl).
  pose proof (proj1 (Forall_forall _ _) NO_CROSS_PTR) as G.
  assert (forallb not_ptr_b vargs = true) as G'.
  { eapply forallb_forall.
    intros. eapply not_ptr_reflect. eauto. }
  rewrite G'.
  eapply get_call_trace_eq in EV; rewrite EV; eauto.
Qed.

Definition reducts_incl {A B: Type} (C: A -> B) (res1: reducts A) (res2: reducts B) : Prop :=
  forall C1 rd, In (C1, rd) res1 -> In ((fun x => C(C1 x)), rd) res2.

Lemma reducts_incl_trans:
  forall (A1 A2: Type) (C: A1 -> A2) res1 res2, reducts_incl C res1 res2 ->
  forall (A3: Type) (C': A2 -> A3) res3,
  reducts_incl C' res2 res3 ->
  reducts_incl (fun x => C'(C x)) res1 res3.
Proof.
  unfold reducts_incl; intros. auto.
Qed.

Lemma reducts_incl_nil:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C nil res.
Proof.
  intros; red. intros; contradiction.
Qed.

Lemma reducts_incl_val:
  forall (A: Type) cp a m v ty (C: expr -> A) res,
  is_val a = Some(v, ty) -> reducts_incl C (step_expr cp RV a m) res.
Proof.
  intros. rewrite (is_val_inv _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_loc:
  forall (A: Type) cp a m b ofs ty bf (C: expr -> A) res,
  is_loc a = Some(b, ofs, bf, ty) -> reducts_incl C (step_expr cp LV a m) res.
Proof.
  intros. rewrite (is_loc_inv _ _ _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_listval:
  forall (A: Type) cp a m vtl (C: exprlist -> A) res,
  is_val_list a = Some vtl -> reducts_incl C (step_exprlist cp a m) res.
Proof.
  intros. rewrite step_exprlist_val_list. apply reducts_incl_nil. congruence.
Qed.

Lemma reducts_incl_incontext:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C res (incontext C res).
Proof.
  unfold reducts_incl, incontext. intros.
  set (f := fun z : (expr -> A) * reduction => (fun x : expr => C (fst z x), snd z)).
  change (In (f (C1, rd)) (map f res)). apply in_map. auto.
Qed.

Lemma reducts_incl_incontext2_left:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C1 res1 (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_incl, incontext2, incontext. intros.
  rewrite in_app_iff. left.
  set (f := fun z : (expr -> A1) * reduction => (fun x : expr => C1 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f res1)). apply in_map; auto.
Qed.

Lemma reducts_incl_incontext2_right:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C2 res2 (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_incl, incontext2, incontext. intros.
  rewrite in_app_iff. right.
  set (f := fun z : (expr -> A2) * reduction => (fun x : expr => C2 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f res2)). apply in_map; auto.
Qed.

Local Hint Resolve reducts_incl_val reducts_incl_loc reducts_incl_listval
                   reducts_incl_incontext reducts_incl_incontext2_left
                   reducts_incl_incontext2_right : core.

Lemma step_expr_context:
  forall from to C, context from to C ->
  forall cp a m, reducts_incl C (step_expr cp from a m) (step_expr cp to (C a) m)
with step_exprlist_context:
  forall from C, contextlist from C ->
  forall cp a m, reducts_incl C (step_expr cp from a m) (step_exprlist cp (C a) m).
Proof.
  induction 1; simpl; intros.
(* top *)
  red. destruct (step_expr cp k a m); auto.
  try (* no eta in 8.3 *)
   (intros;
    replace (fun x => C1 x) with C1 by (apply extensionality; auto);
    auto).
(* deref *)
  eapply reducts_incl_trans with (C' := fun x => Ederef x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* field *)
  eapply reducts_incl_trans with (C' := fun x => Efield x f ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* valof *)
  eapply reducts_incl_trans with (C' := fun x => Evalof x ty); eauto.
  destruct (is_loc (C a)) as [[[[b ofs] bf] ty']|] eqn:?; eauto.
(* addrof *)
  eapply reducts_incl_trans with (C' := fun x => Eaddrof x ty); eauto.
  destruct (is_loc (C a)) as [[[[b ofs] bf] ty']|] eqn:?; eauto.
(* unop *)
  eapply reducts_incl_trans with (C' := fun x => Eunop op x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* binop left *)
  eapply reducts_incl_trans with (C' := fun x => Ebinop op x e2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* binop right *)
  eapply reducts_incl_trans with (C' := fun x => Ebinop op e1 x ty); eauto.
  destruct (is_val e1) as [[v1 ty1]|] eqn:?; eauto.
  destruct (is_val (C a)) as [[v2 ty2]|] eqn:?; eauto.
(* cast *)
  eapply reducts_incl_trans with (C' := fun x => Ecast x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* seqand *)
  eapply reducts_incl_trans with (C' := fun x => Eseqand x r2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* seqor *)
  eapply reducts_incl_trans with (C' := fun x => Eseqor x r2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* condition *)
  eapply reducts_incl_trans with (C' := fun x => Econdition x r2 r3 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* assign left *)
  eapply reducts_incl_trans with (C' := fun x => Eassign x e2 ty); eauto.
  destruct (is_loc (C a)) as [[[[b ofs] bf] ty']|] eqn:?; eauto.
(* assign right *)
  eapply reducts_incl_trans with (C' := fun x => Eassign e1 x ty); eauto.
  destruct (is_loc e1) as [[[[b ofs] bf] ty1]|] eqn:?; eauto.
  destruct (is_val (C a)) as [[v2 ty2]|] eqn:?; eauto.
(* assignop left *)
  eapply reducts_incl_trans with (C' := fun x => Eassignop op x e2 tyres ty); eauto.
  destruct (is_loc (C a)) as [[[[b ofs] bf] ty']|] eqn:?; eauto.
(* assignop right *)
  eapply reducts_incl_trans with (C' := fun x => Eassignop op e1 x tyres ty); eauto.
  destruct (is_loc e1) as [[[[b ofs] bf] ty1]|] eqn:?; eauto.
  destruct (is_val (C a)) as [[v2 ty2]|] eqn:?; eauto.
(* postincr *)
  eapply reducts_incl_trans with (C' := fun x => Epostincr id x ty); eauto.
  destruct (is_loc (C a)) as [[[[b ofs] bf] ty']|] eqn:?; eauto.
(* call left *)
  eapply reducts_incl_trans with (C' := fun x => Ecall x el ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* call right *)
  eapply reducts_incl_trans with (C' := fun x => Ecall e1 x ty). apply step_exprlist_context. auto.
  destruct (is_val e1) as [[v1 ty1]|] eqn:?; eauto.
  destruct (is_val_list (C a)) as [vl|] eqn:?; eauto.
(* builtin *)
  eapply reducts_incl_trans with (C' := fun x => Ebuiltin ef tyargs x ty). apply step_exprlist_context. auto.
  destruct (is_val_list (C a)) as [vl|] eqn:?; eauto.
(* comma *)
  eapply reducts_incl_trans with (C' := fun x => Ecomma x e2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* paren *)
  eapply reducts_incl_trans with (C' := fun x => Eparen x tycast ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.

  induction 1; simpl; intros.
(* cons left *)
  eapply reducts_incl_trans with (C' := fun x => Econs x el).
  apply step_expr_context; eauto. eauto.
(* binop right *)
  eapply reducts_incl_trans with (C' := fun x => Econs e1 x).
  apply step_exprlist_context; eauto. eauto.
Qed.

(** Completeness part 2: if we can reduce to [Stuckstate], [step_expr]
    contains at least one [Stuckred] reduction. *)

Lemma not_stuckred_imm_safe:
  forall cp m a k,
  (forall C, ~In (C, Stuckred) (step_expr cp k a m)) -> imm_safe_t cp k a m.
Proof.
  intros. generalize (step_expr_sound cp a k m). intros [A B].
  destruct (step_expr cp k a m) as [|[C rd] res] eqn:?.
  specialize (B (eq_refl _)). destruct k.
  destruct a; simpl in B; try congruence. constructor.
  destruct a; simpl in B; try congruence. constructor.
  assert (NOTSTUCK: rd <> Stuckred).
    red; intros. elim (H C); subst rd; auto with coqlib.
  exploit A. eauto with coqlib. intros [a' [k' [P [Q R]]]].
  destruct k'; destruct rd; simpl in R; intuition.
  subst a. eapply imm_safe_t_lred; eauto.
  subst a. destruct H1 as [w' PT]. eapply imm_safe_t_rred; eauto.
  subst. eapply imm_safe_t_callred; eauto.
Qed.

Lemma not_imm_safe_stuck_red:
  forall cp m a k C,
  context k RV C ->
  ~imm_safe_t cp k a m ->
  exists C', In (C', Stuckred) (step_expr cp RV (C a) m).
Proof.
  intros.
  assert (exists C', In (C', Stuckred) (step_expr cp k a m)).
    destruct (classic (exists C', In (C', Stuckred) (step_expr cp k a m))); auto.
    elim H0. apply not_stuckred_imm_safe. apply not_ex_all_not. auto.
  destruct H1 as [C' IN].
  specialize (step_expr_context _ _ _ H cp a m). unfold reducts_incl.
  intro.
  exists (fun x => (C (C' x))). apply H1; auto.
Qed.

(** Connections between [imm_safe_t] and [imm_safe] *)

Lemma imm_safe_imm_safe_t:
  forall cp k a m,
  imm_safe ge e cp k a m ->
  imm_safe_t cp k a m \/
  exists C, exists a1, exists t, exists a1', exists m',
    context RV k C /\ a = C a1 /\ rred ge cp a1 m t a1' m' /\ forall w', ~possible_trace w t w'.
Proof.
  intros. inv H.
  left. apply imm_safe_t_val.
  left. apply imm_safe_t_loc.
  left. eapply imm_safe_t_lred; eauto.
  destruct (classic (exists w', possible_trace w t w')) as [[w' A] | A].
  left. eapply imm_safe_t_rred; eauto.
  right. exists C; exists e0; exists t; exists e'; exists m'; intuition. apply A; exists w'; auto.
  left. eapply imm_safe_t_callred; eauto.
Qed.

(** A state can "crash the world" if it can make an observable transition
  whose trace is not accepted by the external world. *)

Definition can_crash_world (w: world) (S: state) : Prop :=
  exists t, exists S', Csem.step ge S t S' /\ forall w', ~possible_trace w t w'.

Theorem not_imm_safe_t:
  forall K C a m f k,
  context K RV C ->
  ~imm_safe_t (comp_of f) K a m ->
  Csem.step ge (ExprState f (C a) k e m) E0 Stuckstate \/ can_crash_world w (ExprState f (C a) k e m).
Proof.
  intros. destruct (classic (imm_safe ge e (comp_of f) K a m)).
  exploit imm_safe_imm_safe_t; eauto.
  intros [A | [C1 [a1 [t [a1' [m' [A [B [D E]]]]]]]]]. contradiction.
  right. red. exists t; econstructor; split; auto.
  left. rewrite B. eapply step_rred with (C := fun x => C(C1 x)). eauto. eauto.
  left. left. eapply step_stuck; eauto; congruence.
Qed.

End EXPRS.

(** * Transitions over states. *)

(* NOTE: default compartment previously *)
Fixpoint do_alloc_variables (e: env) (m: mem) (cp: compartment) (l: list (ident * type)) {struct l} : env * mem :=
  match l with
  | nil => (e,m)
  | (id, ty) :: l' =>
      let (m1,b1) := Mem.alloc m cp 0 (sizeof ge ty) in
      do_alloc_variables (PTree.set id (b1, ty) e) m1 cp l'
end.

Lemma do_alloc_variables_sound:
  forall l e m cp, alloc_variables ge cp e m l (fst (do_alloc_variables e m cp l)) (snd (do_alloc_variables e m cp l)).
Proof.
  induction l; intros; simpl.
  constructor.
  destruct a as [id ty]. destruct (Mem.alloc m cp 0 (sizeof ge ty)) as [m1 b1] eqn:?; simpl.
  econstructor; eauto.
Qed.

Lemma do_alloc_variables_complete:
  forall e1 m1 l e2 m2 cp, alloc_variables ge cp e1 m1 l e2 m2 ->
  do_alloc_variables e1 m1 cp l = (e2, m2).
Proof.
  induction 1; simpl.
  auto.
  rewrite H; rewrite IHalloc_variables; auto.
Qed.

Function sem_bind_parameters (w: world) (e: env) (m: mem) (l: list (ident * type)) (lv: list val) (cp: compartment)
                          {struct l} : option mem :=
  match l, lv  with
  | nil, nil => Some m
  | (id, ty) :: params, v1::lv =>
      match PTree.get id e with
         | Some (b, ty') =>
             check (type_eq ty ty');
             do w', t, m1, v' <- do_assign_loc w ty m b Ptrofs.zero Full v1 cp;
             match t with nil => sem_bind_parameters w e m1 params lv cp | _ => None end
        | None => None
      end
   | _, _ => None
end.

Lemma sem_bind_parameters_sound : forall w e m l lv cp m',
  sem_bind_parameters w e m l lv cp = Some m' ->
  bind_parameters ge cp e m l lv m'.
Proof.
   intros; functional induction (sem_bind_parameters w e m l lv cp); try discriminate.
   inversion H; constructor; auto.
   exploit do_assign_loc_sound; eauto. intros [A B]. econstructor; eauto.
Qed.

Lemma sem_bind_parameters_complete : forall w cp e m l lv m',
  bind_parameters ge cp e m l lv m' ->
  sem_bind_parameters w e m l lv cp = Some m'.
Proof.
Local Opaque do_assign_loc.
   induction 1; simpl; auto.
   rewrite H. rewrite dec_eq_true.
   assert (possible_trace w E0 w) by constructor.
   rewrite (do_assign_loc_complete _ _ _ _ _ _ _ _ _ _ _ _ H0 H2).
   simpl. auto.
Qed.

Inductive transition : Type := TR (rule: string) (t: trace) (S': state).

Definition expr_final_state (f: function) (k: cont) (e: env) (C_rd: (expr -> expr) * reduction) :=
  match snd C_rd with
  | Lred rule a m => TR rule E0 (ExprState f (fst C_rd a) k e m)
  | Rred rule a m t => TR rule t (ExprState f (fst C_rd a) k e m)
  | Callred rule fd vargs ty t m => TR rule t (Callstate fd vargs (Kcall f e (fst C_rd) ty k) m)
  | Stuckred => TR "step_stuck" E0 Stuckstate
  end.

Local Open Scope list_monad_scope.

Definition ret (rule: string) (S: state) : list transition :=
  TR rule E0 S :: nil.

Definition do_step (w: world) (s: state) : list transition :=
  match s with

  | ExprState f a k e m =>
      match is_val a with
      | Some(v, ty) =>
        match k with
        | Kdo k => ret "step_do_2" (State f Sskip k e m )
        | Kifthenelse s1 s2 k =>
            do b <- bool_val v ty m;
            ret "step_ifthenelse_2" (State f (if b then s1 else s2) k e m)
        | Kwhile1 x s k =>
            do b <- bool_val v ty m;
            if b
            then ret "step_while_true" (State f s (Kwhile2 x s k) e m)
            else ret "step_while_false" (State f Sskip k e m)
        | Kdowhile2 x s k =>
            do b <- bool_val v ty m;
            if b
            then ret "step_dowhile_true" (State f (Sdowhile x s) k e m)
            else ret "step_dowhile_false" (State f Sskip k e m)
        | Kfor2 a2 a3 s k =>
            do b <- bool_val v ty m;
            if b
            then ret "step_for_true" (State f s (Kfor3 a2 a3 s k) e m)
            else ret "step_for_false" (State f Sskip k e m)
        | Kreturn k =>
            do v' <- sem_cast v ty f.(fn_return) m;
            do m' <- Mem.free_list m (blocks_of_env ge e) (comp_of f);
            ret "step_return_2" (Returnstate v' (call_cont k) m' (rettype_of_type f.(fn_return)) (comp_of f))
        | Kswitch1 sl k =>
            do n <- sem_switch_arg v ty;
            ret "step_expr_switch" (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e m)
        | _ => nil
        end

      | None =>
          map (expr_final_state f k e) (step_expr e w (comp_of f) RV a m)
      end

  | State f (Sdo x) k e m =>
      ret "step_do_1" (ExprState f x (Kdo k) e m)
  | State f (Ssequence s1 s2) k e m =>
      ret "step_seq" (State f s1 (Kseq s2 k) e m)
  | State f Sskip (Kseq s k) e m =>
      ret "step_skip_seq" (State f s k e m)
  | State f Scontinue (Kseq s k) e m =>
      ret "step_continue_seq" (State f Scontinue k e m)
  | State f Sbreak (Kseq s k) e m =>
      ret "step_break_seq" (State f Sbreak k e m)

  | State f (Sifthenelse a s1 s2) k e m =>
      ret "step_ifthenelse_1" (ExprState f a (Kifthenelse s1 s2 k) e m)

  | State f (Swhile x s) k e m =>
      ret "step_while" (ExprState f x (Kwhile1 x s k) e m)
  | State f (Sskip|Scontinue) (Kwhile2 x s k) e m =>
      ret "step_skip_or_continue_while" (State f (Swhile x s) k e m)
  | State f Sbreak (Kwhile2 x s k) e m =>
      ret "step_break_while" (State f Sskip k e m)

  | State f (Sdowhile a s) k e m =>
      ret "step_dowhile" (State f s (Kdowhile1 a s k) e m)
  | State f (Sskip|Scontinue) (Kdowhile1 x s k) e m =>
      ret "step_skip_or_continue_dowhile" (ExprState f x (Kdowhile2 x s k) e m)
  | State f Sbreak (Kdowhile1 x s k) e m =>
      ret "step_break_dowhile" (State f Sskip k e m)

  | State f (Sfor a1 a2 a3 s) k e m =>
      if is_skip a1
      then ret "step_for" (ExprState f a2 (Kfor2 a2 a3 s k) e m)
      else ret "step_for_start" (State f a1 (Kseq (Sfor Sskip a2 a3 s) k) e m)
  | State f (Sskip|Scontinue) (Kfor3 a2 a3 s k) e m =>
      ret "step_skip_or_continue_for3" (State f a3 (Kfor4 a2 a3 s k) e m)
  | State f Sbreak (Kfor3 a2 a3 s k) e m =>
      ret "step_break_for3" (State f Sskip k e m)
  | State f Sskip (Kfor4 a2 a3 s k) e m =>
      ret "step_skip_for4" (State f (Sfor Sskip a2 a3 s) k e m)

  | State f (Sreturn None) k e m =>
      do m' <- Mem.free_list m (blocks_of_env ge e) (comp_of f);
      ret "step_return_0" (Returnstate Vundef (call_cont k) m' (rettype_of_type f.(fn_return)) (comp_of f))
  | State f (Sreturn (Some x)) k e m =>
      ret "step_return_1" (ExprState f x (Kreturn k) e m)
  | State f Sskip ((Kstop | Kcall _ _ _ _ _) as k) e m =>
      do m' <- Mem.free_list m (blocks_of_env ge e) (comp_of f);
      ret "step_skip_call" (Returnstate Vundef k m' (rettype_of_type f.(fn_return)) (comp_of f))

  | State f (Sswitch x sl) k e m =>
      ret "step_switch" (ExprState f x (Kswitch1 sl k) e m)
  | State f (Sskip|Sbreak) (Kswitch2 k) e m =>
      ret "step_skip_break_switch" (State f Sskip k e m)
  | State f Scontinue (Kswitch2 k) e m =>
      ret "step_continue_switch" (State f Scontinue k e m)

  | State f (Slabel lbl s) k e m =>
      ret "step_label" (State f s k e m)
  | State f (Sgoto lbl) k e m =>
      match find_label lbl f.(fn_body) (call_cont k) with
      | Some(s', k') => ret "step_goto" (State f s' k' e m)
      | None => nil
      end

  | Callstate (Internal f) vargs k m =>
      check (list_norepet_dec ident_eq (var_names (fn_params f) ++ var_names (fn_vars f)));
      let (e,m1) := do_alloc_variables empty_env m (fn_comp f) (f.(fn_params) ++ f.(fn_vars)) in
      do m2 <- sem_bind_parameters w e m1 f.(fn_params) vargs (fn_comp f);
      ret "step_internal_function" (State f f.(fn_body) k e m2)
  | Callstate (External ef _ tres _) vargs k m =>
      match do_external _ _ ge do_external_function do_inline_assembly ef w vargs m with
      | None => nil
      | Some(w',t,v,m') => TR "step_external_function" t (Returnstate v k m' (rettype_of_type tres) (comp_of ef)) :: nil
      end

  | Returnstate v (Kcall f e C ty k) m ty' cp =>
      check (match Genv.type_of_call (comp_of f) cp with
             | Genv.CrossCompartmentCall => not_ptr_b v
             | _ => true end);
      do t <- get_return_trace _ _ ge (comp_of f) cp v ty';
      TR "step_returnstate" t (ExprState f (C (Eval v ty)) k e m) :: nil

  | _ => nil
  end.

Ltac myinv :=
  match goal with
  | [ |- In _ nil -> _ ] => let X := fresh "X" in intro X; elim X
  | [ |- In _ (ret _ _) -> _ ] =>
        let X := fresh "X" in
        intro X; elim X; clear X;
        [let EQ := fresh "EQ" in intro EQ; unfold ret in EQ; inv EQ; myinv | myinv]
  | [ |- In _ (_ :: nil) -> _ ] =>
        let X := fresh "X" in
        intro X; elim X; clear X; [let EQ := fresh "EQ" in intro EQ; inv EQ; myinv | myinv]
  | [ |- In _ (match ?x with Some _ => _ | None => _ end) -> _ ] => destruct x eqn:?; myinv
  | [ |- In _ (match ?x with false => _ | true => _ end) -> _ ] => destruct x eqn:?; myinv
  | [ |- In _ (match ?x with left _ => _ | right _ => _ end) -> _ ] => destruct x; myinv
  | _ => idtac
  end.

Local Hint Extern 3 => exact I : core.

Theorem do_step_sound:
  forall w S rule t S',
  In (TR rule t S') (do_step w S) ->
  Csem.step ge S t S' \/ (t = E0 /\ S' = Stuckstate /\ can_crash_world w S).
Proof with try (left; right; econstructor; eauto; fail).
  intros until S'. destruct S; simpl.
(* State *)
  destruct s; myinv...
  (* skip *)
  destruct k; myinv...
  (* break *)
  destruct k; myinv...
  (* continue *)
  destruct k; myinv...
  (* goto *)
  destruct p as [s' k']. myinv...
(* ExprState *)
  destruct (is_val r) as [[v ty]|] eqn:?.
  (* expression is a value *)
  rewrite (is_val_inv _ _ _ Heqo).
  destruct k; myinv...
  (* expression reduces *)
  intros. exploit list_in_map_inv; eauto. intros [[C rd] [A B]].
  generalize (step_expr_sound e w (comp_of f) r RV m). unfold reducts_ok. intros [P Q].
  exploit P; eauto. intros [a' [k' [CTX [EQ RD]]]].
  unfold expr_final_state in A. simpl in A.
  destruct k'; destruct rd; inv A; simpl in RD; try contradiction.
  (* lred *)
  left; left; apply step_lred; auto.
  (* stuck lred *)
  exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
  (* rred *)
  destruct RD. left; left; apply step_rred; auto.
  (* callred *)
  destruct RD; subst m'. left; left; apply step_call; eauto.
  (* stuck rred *)
  exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
(* callstate *)
  destruct fd; myinv.
  (* internal *)
  destruct (do_alloc_variables empty_env m (fn_comp f) (fn_params f ++ fn_vars f)) as [e m1] eqn:?.
  myinv. left; right; apply step_internal_function with m1. auto.
  change e with (fst (e,m1)). change m1 with (snd (e,m1)) at 2. rewrite <- Heqp.
  apply do_alloc_variables_sound. eapply sem_bind_parameters_sound; eauto.
  (* external *)
  destruct p as [[[w' tr] v] m']. myinv. left; right; constructor.
  eapply do_ef_external_sound; eauto.
(* returnstate *)
  destruct k; myinv... left; right; constructor.
  intros REWR; rewrite REWR in Heqb. now apply not_ptr_reflect.
  now apply get_return_trace_eq in Heqo.
(* stuckstate *)
  contradiction.
Qed.

Remark estep_not_val:
  forall f a k e m t S, estep ge (ExprState f a k e m) t S -> is_val a = None.
Proof.
  intros.
  assert (forall b from to C, context from to C -> (from = to /\ C = fun x => x) \/ is_val (C b) = None).
    induction 1; simpl; auto.
  inv H.
  destruct (H0 a0 _ _ _ H9) as [[A B] | A]. subst. inv H8; auto. auto.
  destruct (H0 a0 _ _ _ H9) as [[A B] | A]. subst. inv H8; auto. auto.
  destruct (H0 a0 _ _ _ H9) as [[A B] | A]. subst. inv H8; auto. auto.
  destruct (H0 a0 _ _ _ H8) as [[A B] | A]. subst. destruct a0; auto. elim H9. constructor. auto.
Qed.

Theorem do_step_complete:
  forall w S t S' w',
  possible_trace w t w' -> Csem.step ge S t S' -> exists rule, In (TR rule t S') (do_step w S).
Proof with (unfold ret; eauto with coqlib).
  intros until w'; intros PT H.
  destruct H.
  (* Expression step *)
  inversion H; subst; exploit estep_not_val; eauto; intro NOTVAL.
(* lred *)
  unfold do_step; rewrite NOTVAL.
  exploit lred_topred; eauto. instantiate (1 := w). intros (rule & STEP).
  exists rule. change (TR rule E0 (ExprState f (C a') k e m')) with (expr_final_state f k e (C, Lred rule a' m')).
  apply in_map.
  generalize (step_expr_context e w _ _ _ H1 (comp_of f) a m). unfold reducts_incl.
  intro. replace C with (fun x => C x). apply H2.
  rewrite STEP. unfold topred; auto with coqlib.
  apply extensionality; auto.
(* rred *)
  unfold do_step; rewrite NOTVAL.
  exploit rred_topred; eauto. instantiate (1 := e). intros (rule & STEP).
  exists rule.
  change (TR rule t (ExprState f (C a') k e m')) with (expr_final_state f k e (C, Rred rule a' m' t)).
  apply in_map.
  generalize (step_expr_context e w _ _ _ H1 (comp_of f) a m). unfold reducts_incl.
  intro. replace C with (fun x => C x). apply H2.
  rewrite STEP; unfold topred; auto with coqlib.
  apply extensionality; auto.
(* callred *)
  unfold do_step; rewrite NOTVAL.
  exploit callred_topred; eauto.
  instantiate (1 := w). instantiate (1 := e).
  intros (rule & STEP). exists rule.
  change (TR rule t (Callstate fd vargs (Kcall f e C ty k) m))
    with (expr_final_state f k e (C, Callred rule fd vargs ty t m)).
  apply in_map.
  generalize (step_expr_context e w _ _ _ H1 (comp_of f) a m). unfold reducts_incl.
  intro. replace C with (fun x => C x). apply H2.
  rewrite STEP; unfold topred; auto with coqlib.
  apply extensionality; auto.
(* stuck *)
  exploit not_imm_safe_stuck_red. eauto. red; intros; elim H1. eapply imm_safe_t_imm_safe. eauto.
  instantiate (1 := w). intros [C' IN].
  simpl do_step. rewrite NOTVAL.
  exists "step_stuck".
  change (TR "step_stuck" E0 Stuckstate) with (expr_final_state f k e (C', Stuckred)).
  apply in_map. auto.

  (* Statement step *)
  inv H; simpl; econstructor...
  rewrite H0...
  rewrite H0...
  rewrite H0...
  destruct H0; subst s0...
  destruct H0; subst s0...
  rewrite H0...
  rewrite H0...
  rewrite pred_dec_false...
  rewrite H0...
  rewrite H0...
  destruct H0; subst x...
  (* NOTE: Parts of this proof change somewhat *)
  setoid_rewrite H0...
  rewrite H0; setoid_rewrite H1...
  (* rewrite H1. red in H0. destruct k; try contradiction... *)
  red in H0. destruct k; try setoid_rewrite H0; try contradiction...
  setoid_rewrite H1...
  setoid_rewrite H1...
  rewrite H0...
  destruct x; destruct H0; try discriminate; (left; reflexivity).
  rewrite H0...
  destruct H0...

  (* Call step *)
  rewrite pred_dec_true; auto. setoid_rewrite (do_alloc_variables_complete _ _ _ _ _ _ H1).
  rewrite (sem_bind_parameters_complete _ _ _ _ _ _ _ H2)...
  constructor.
  rewrite pred_dec_true; auto. setoid_rewrite (do_alloc_variables_complete _ _ _ _ _ _ H1).
  rewrite (sem_bind_parameters_complete _ _ _ _ _ _ _ H2)...
  constructor; auto.
  exploit do_ef_external_complete; eauto. intro EQ; rewrite EQ. auto with coqlib.
  assert (match Genv.type_of_call (comp_of f) cp with
           | Genv.CrossCompartmentCall => not_ptr_b v
           | _ => true
           end = true).
  { destruct (Genv.type_of_call (comp_of f) cp) eqn:eq_type_of_call;
      [reflexivity | ].
    apply not_ptr_reflect; auto. }
  rewrite H. apply get_return_trace_eq in EV; rewrite EV. simpl.
  left; reflexivity.
Qed.

End EXEC.

Local Open Scope option_monad_scope.

Definition do_initial_state (p: program): option (genv * state) :=
  let ge := globalenv p in
  do m0 <- Genv.init_mem p;
  do b <- Genv.find_symbol ge p.(prog_main);
  do f <- Genv.find_funct_ptr ge b;
  check (type_eq (type_of_fundef f) (Tfunction Tnil type_int32s cc_default));
  Some (ge, Callstate f nil Kstop m0).

Definition at_final_state (S: state): option int :=
  match S with
  | Returnstate (Vint r) Kstop m ty cp => Some r
  | _ => None
  end.
