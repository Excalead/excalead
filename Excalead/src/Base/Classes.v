
Class EqDec (X : Type) :=
  eq : X -> X -> bool.
Notation "x == y" := (eq x y) (no associativity, at level 70).


