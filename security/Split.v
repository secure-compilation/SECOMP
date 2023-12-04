Require Import String.
Require Import AST.
Require Import Values.


Variant side := Left | Right.
Theorem side_eq: forall (x y: side), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition opposite (δ: side) :=
  match δ with
  | Left => Right
  | Right => Left
  end.

Definition split := compartment -> side.

Class has_side {ctx: Type} (A: Type) :=
  { in_side: ctx -> A -> side -> Prop }.

#[export] Instance compartment_has_side: has_side compartment :=
  { in_side s := fun cp δ => s cp = δ }.

#[export] Instance has_comp_has_side (A: Type) {CA: has_comp A}: has_side A :=
  { in_side s :=  fun a δ => s (comp_of a) = δ }.

Notation "s '|=' a '∈' δ " := (in_side s a δ) (no associativity, at level 75).
