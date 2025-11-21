Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

(* A lot of code here is taken from `coq-of-rust`. Ideally, we should merge the two projects. *)

Module IntegerKind.
  Inductive t : Set :=
  | I8 : t
  | I16 : t
  | I32 : t
  | I64 : t
  | I128 : t
  | Isize : t
  | U8 : t
  | U16 : t
  | U32 : t
  | U64 : t
  | U128 : t
  | Usize : t.
End IntegerKind.

Module Integer.
  (** We distinguish the various forms of integers at this level. We will use plain [Z] integers in
      the simulations. *)
  Record t {kind : IntegerKind.t} : Set := {
    value : Z;
  }.
  Arguments t : clear implicits.

  Definition min (kind : IntegerKind.t) : Z :=
    match kind with
    | IntegerKind.U8 => 0
    | IntegerKind.U16 => 0
    | IntegerKind.U32 => 0
    | IntegerKind.U64 => 0
    | IntegerKind.U128 => 0
    | IntegerKind.Usize => 0
    | IntegerKind.I8 => -2^7
    | IntegerKind.I16 => -2^15
    | IntegerKind.I32 => -2^31
    | IntegerKind.I64 => -2^63
    | IntegerKind.I128 => -2^127
    | IntegerKind.Isize => -2^63
    end.
  Global Hint Unfold min : coq_of_rust_z.

  Definition max (kind : IntegerKind.t) : Z :=
    match kind with
    | IntegerKind.U8 => 2^8 - 1
    | IntegerKind.U16 => 2^16 - 1
    | IntegerKind.U32 => 2^32 - 1
    | IntegerKind.U64 => 2^64 - 1
    | IntegerKind.U128 => 2^128 - 1
    | IntegerKind.Usize => 2^64 - 1
    | IntegerKind.I8 => 2^7 - 1
    | IntegerKind.I16 => 2^15 - 1
    | IntegerKind.I32 => 2^31 - 1
    | IntegerKind.I64 => 2^63 - 1
    | IntegerKind.I128 => 2^127 - 1
    | IntegerKind.Isize => 2^63 - 1
    end.
  Global Hint Unfold max : coq_of_rust_z.

  Definition normalize_wrap (kind : IntegerKind.t) (z : Z) : Z :=
    match kind with
    | IntegerKind.U8 => Z.modulo z (2^8)
    | IntegerKind.U16 => Z.modulo z (2^16)
    | IntegerKind.U32 => Z.modulo z (2^32)
    | IntegerKind.U64 => Z.modulo z (2^64)
    | IntegerKind.U128 => Z.modulo z (2^128)
    | IntegerKind.Usize => Z.modulo z (2^64)
    | IntegerKind.I8 => Z.modulo (z + 2^7) (2^8) - 2^7
    | IntegerKind.I16 => Z.modulo (z + 2^15) (2^16) - 2^15
    | IntegerKind.I32 => Z.modulo (z + 2^31) (2^32) - 2^31
    | IntegerKind.I64 => Z.modulo (z + 2^63) (2^64) - 2^63
    | IntegerKind.I128 => Z.modulo (z + 2^127) (2^128) - 2^127
    | IntegerKind.Isize => Z.modulo (z + 2^63) (2^64) - 2^63
    end.

  Definition normalize_option (kind : IntegerKind.t) (z : Z) : option Z :=
    if z <? min kind then
      None
    else if max kind <? z then
      None
    else
      Some z.

  Definition normalize_saturating (kind : IntegerKind.t) (z : Z) : Z :=
    if z <? min kind then
      min kind
    else if max kind <? z then
      max kind
    else
      z.
End Integer.

Definition u8 : Set := Integer.t IntegerKind.U8.
Definition u16 : Set := Integer.t IntegerKind.U16.
Definition u32 : Set := Integer.t IntegerKind.U32.
Definition u64 : Set := Integer.t IntegerKind.U64.
Definition u128 : Set := Integer.t IntegerKind.U128.
Definition usize : Set := Integer.t IntegerKind.Usize.
Definition i8 : Set := Integer.t IntegerKind.I8.
Definition i16 : Set := Integer.t IntegerKind.I16.
Definition i32 : Set := Integer.t IntegerKind.I32.
Definition i64 : Set := Integer.t IntegerKind.I64.
Definition i128 : Set := Integer.t IntegerKind.I128.
Definition isize : Set := Integer.t IntegerKind.Isize.
Parameter f32 : Set.
Parameter f64 : Set.

Module UnOp.
  Module Wrap.
    Definition neg {kind : IntegerKind.t} (a : Integer.t kind) : Integer.t kind :=
      {| Integer.value := Integer.normalize_wrap kind (- a.(Integer.value)) |}.
  End Wrap.

  Module Checked.
    Definition neg {kind : IntegerKind.t} (a : Integer.t kind) : option (Integer.t kind) :=
      match Integer.normalize_option kind (- a.(Integer.value)) with
      | Some value => Some {| Integer.value := value |}
      | None => None
      end.
  End Checked.

  Module Saturating.
    Definition neg {kind : IntegerKind.t} (a : Integer.t kind) : Integer.t kind :=
      {| Integer.value := Integer.normalize_saturating kind (- a.(Integer.value)) |}.
  End Saturating.
End UnOp.

Module BinOp.
  Definition eq {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.eqb a.(Integer.value) b.(Integer.value).

  Definition ne {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    negb (Z.eqb a.(Integer.value) b.(Integer.value)).

  Definition lt {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.ltb a.(Integer.value) b.(Integer.value).

  Definition le {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.leb a.(Integer.value) b.(Integer.value).

  Definition gt {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.gtb a.(Integer.value) b.(Integer.value).

  Definition ge {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.geb a.(Integer.value) b.(Integer.value).

  Module Wrap.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        {kind : IntegerKind.t}
        (a b : Integer.t kind) :
        Integer.t kind :=
      {|
        Integer.value := Integer.normalize_wrap kind (bin_op a.(Integer.value) b.(Integer.value))
      |}.

    Definition add {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.add a b.

    Definition sub {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.sub a b.

    Definition mul {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.mul a b.

    Definition div {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.div a b.

    Definition rem {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.modulo a b.

    Definition shl {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.shiftl a b.

    Definition shr {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.shiftr a b.
  End Wrap.

  Module Checked.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        {kind : IntegerKind.t}
        (a b : Integer.t kind) :
        option (Integer.t kind) :=
      match Integer.normalize_option kind (bin_op a.(Integer.value) b.(Integer.value)) with
      | Some value => Some {| Integer.value := value |}
      | None => None
      end.

    Definition add {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.add a b.

    Definition sub {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.sub a b.

    Definition mul {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.mul a b.

    Definition div {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.div a b.

    Definition rem {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.modulo a b.

    Definition shl {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.shiftl a b.

    Definition shr {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.shiftr a b.
  End Checked.

  Module Saturating.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        {kind : IntegerKind.t}
        (a b : Integer.t kind) :
        Integer.t kind :=
      {| Integer.value := Integer.normalize_saturating kind (bin_op a.(Integer.value) b.(Integer.value)) |}.

    Definition add {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.add a b.

    Definition sub {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.sub a b.

    Definition mul {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.mul a b.

    Definition div {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.div a b.

    Definition rem {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.modulo a b.

    Definition shl {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.shiftl a b.

    Definition shr {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.shiftr a b.
  End Saturating.
End BinOp.

(* Notations for wrapping and checked integer arithmetic operators *)

Notation "a '=i' b" := (BinOp.eq a b) (at level 70, no associativity).
Notation "a '!=i' b" := (BinOp.ne a b) (at level 70, no associativity).
Notation "a '<i' b" := (BinOp.lt a b) (at level 70, no associativity).
Notation "a '<=i' b" := (BinOp.le a b) (at level 70, no associativity).
Notation "a '>i' b" := (BinOp.gt a b) (at level 70, no associativity).
Notation "a '>=i' b" := (BinOp.ge a b) (at level 70, no associativity).

Notation "'-i' x" := (UnOp.Wrap.neg x) (at level 50, left associativity).
Notation "a '+i' b" := (BinOp.Wrap.add a b) (at level 50, left associativity).
Notation "a '-i' b" := (BinOp.Wrap.sub a b) (at level 50, left associativity).
Notation "a '*i' b" := (BinOp.Wrap.mul a b) (at level 40, left associativity).
Notation "a '/i' b" := (BinOp.Wrap.div a b) (at level 40, left associativity).
Notation "a '%i' b" := (BinOp.Wrap.rem a b) (at level 40, left associativity).
Notation "a '<<i' b" := (BinOp.Wrap.shl a b) (at level 40, left associativity).
Notation "a '>>i' b" := (BinOp.Wrap.shr a b) (at level 40, left associativity).

Notation "'-i'? x" := (UnOp.Checked.neg x) (at level 50, left associativity).
Notation "a '+i?' b" := (BinOp.Checked.add a b) (at level 50, left associativity).
Notation "a '-i?' b" := (BinOp.Checked.sub a b) (at level 50, left associativity).
Notation "a '*i?' b" := (BinOp.Checked.mul a b) (at level 40, left associativity).
Notation "a '/i?' b" := (BinOp.Checked.div a b) (at level 40, left associativity).
Notation "a '%i?' b" := (BinOp.Checked.rem a b) (at level 40, left associativity).
Notation "a '<<i?' b" := (BinOp.Checked.shl a b) (at level 40, left associativity).
Notation "a '>>i?' b" := (BinOp.Checked.shr a b) (at level 40, left associativity).

Notation "'-is' x" := (UnOp.Saturating.neg x) (at level 50, left associativity).
Notation "a '+is' b" := (BinOp.Saturating.add a b) (at level 50, left associativity).
Notation "a '-is' b" := (BinOp.Saturating.sub a b) (at level 50, left associativity).
Notation "a '*is' b" := (BinOp.Saturating.mul a b) (at level 40, left associativity).
Notation "a '/is' b" := (BinOp.Saturating.div a b) (at level 40, left associativity).
Notation "a '%is' b" := (BinOp.Saturating.rem a b) (at level 40, left associativity).
Notation "a '<<is' b" := (BinOp.Saturating.shl a b) (at level 40, left associativity).
Notation "a '>>is' b" := (BinOp.Saturating.shr a b) (at level 40, left associativity).

#[warnings="-uniform-inheritance"]
Coercion Integer_of_Z {kind : IntegerKind.t} (z : Z) : Integer.t kind := {| Integer.value := z |}.
