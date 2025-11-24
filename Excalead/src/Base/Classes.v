Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Class EqDec (X : Type) :=
  eq : X -> X -> bool.
Notation "x == y" := (eq x y) (no associativity, at level 70).

#[export]
Instance Z_EqDec : EqDec Z := Z.eqb.

#[export]
Instance String_EqDec : EqDec string := String.eqb.

