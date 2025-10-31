
Require Export Coq.PArith.BinPosDef.
Require Export Coq.Strings.PrimString.
Require Export Coq.ZArith.ZArith.

Require Export RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.
Require Export smpl.Smpl.

(* Activate the modulo arithmetic in [lia] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.
Global Open Scope bool_scope.

Export List.ListNotations.

Parameter Hash : Set.

Parameter Pubkey : Set.

Definition u8 : Set := Z.
Definition u16 : Set := Z.
Definition u32 : Set := Z.
Definition u64 : Set := Z.
Definition u128 : Set := Z.
Definition usize : Set := Z.
Definition i8 : Set := Z.
Definition i16 : Set := Z.
Definition i32 : Set := Z.
Definition i64 : Set := Z.
Definition i128 : Set := Z.
Definition isize : Set := Z.

Module Signer.
  Parameter t : Set.

  Parameter lamports : forall (self : Signer.t), u64.
End Signer.

Module System.
  Parameter t : Set.
End System.

Module Context.
  Record t {Accounts : Set} : Set := {
    accounts : Accounts;
  }.
  Arguments t : clear implicits.
End Context.

Module Result.
  Inductive t (A : Set) :=
  | Ok : A -> t A
  | Err : string -> t A.
  Arguments Ok {A} _.
  Arguments Err {A} _.

  Definition bind {A B : Set} (result : t A) (f : A -> t B) : t B :=
    match result with
    | Ok a => f a
    | Err e => Err e
    end.
End Result.

Notation "'let?' x ':=' e 'in' k" :=
  (Result.bind e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

Definition require (condition : bool) (message : string) : Result.t unit :=
  if condition then
    Result.Ok tt
  else
    Result.Err message.

Notation "'require!' condition 'with' message 'in' k" :=
  (let? _ := require condition message in k)
  (at level 200, condition at level 200, message at level 200, k at level 200).

(** For now we consider messaging as a no-op *)
Definition msg (message : string) : Result.t unit :=
  Result.Ok tt.

Notation "'msg!' message 'in' k" :=
  (let? _ := msg message in k)
  (at level 200, message at level 200, k at level 200).

Module Clock.
  Record t : Set := {
    unix_timestamp : u64;
  }.

  Parameter get : Result.t t.
End Clock.
