Require Import String.
Require Import Coqlib Maps Errors.
Require Import AST Linking Smallstep Events Behaviors.
Require Import Clight Asm.


Variant side := Left | Right.
Theorem side_eq: forall (x y: side), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition split := compartment -> side.



Definition clight_has_side (s: split) (lr: side) (p: Clight.program) :=
  List.Forall (fun '(id, gd) =>
                 match gd with
                 | Gfun (Ctypes.Internal f) => s (comp_of f) = lr
                 | _ => True
                 end)
    (Ctypes.prog_defs p).

Definition asm_has_side (s: split) (lr: side) (p: Asm.program) :=
  List.Forall (fun '(id, gd) =>
                 match gd with
                 | Gfun (Internal f) => s (comp_of f) = lr
                 | _ => True
                 end)
    (prog_defs p).

Definition clight_compatible (s: split) (p p': Clight.program) :=
  clight_has_side s Left p /\ clight_has_side s Right p'.

Definition asm_compatible (s: split) (p p': Asm.program) :=
  asm_has_side s Left p /\ asm_has_side s Right p'.

Lemma link_compatible: forall s p p',
    clight_compatible s p p' ->
    Ctypes.prog_pol p = Ctypes.prog_pol p' ->
    exists W, link p p' = Some W.
Proof.
  admit.
Admitted.
