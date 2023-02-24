Require Import String.
Require Import Coqlib Maps Errors.
Require Import AST Linking Smallstep Events Behaviors.


Variant side := Left | Right.
Theorem side_eq: forall (x y: side), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition split := compartment -> side.
