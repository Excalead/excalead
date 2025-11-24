Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

From Excalead Require Import Base.Nums.

Class EqDec (X : Type) :=
  eq : X -> X -> bool.
Notation "x == y" := (eq x y) (no associativity, at level 70).

#[export]
Instance Z_EqDec : EqDec Z := Z.eqb.

#[export]
Instance String_EqDec : EqDec string := String.eqb.

Global Open Scope list_scope.
Import List.ListNotations.
From JSON Require Export JSON Encode Decode.

#[export]
Instance Integer_JEncode {kind : IntegerKind.t} : JEncode (Integer.t kind) :=
  fun x => encode (i[x]).

#[export]
Instance GameDurationConfig_JDecode {kind : IntegerKind.t} : JDecode (Integer.t kind) :=
  fun j => match j with
  | JSON__Number number => inr {| Integer.value := number |}
  | _ => inl "Failed to decode Integer"
  end.
