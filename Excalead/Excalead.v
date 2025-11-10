
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

Parameter AccountInfo : Set.

Parameter Pubkey : Set.
Parameter Pubkey_eq : Pubkey -> Pubkey -> bool.
(* Maybe this should be a module like:
   Module Pubkey.
    Parameter t : Set.
    Parameter eq : t -> t -> bool.
   End Pubkey.
*)

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
Parameter f32 : Set.
Parameter f64 : Set.

Parameter bytes : Set.

Module IsWritable.
  Inductive t : Set := Yes | No.
End IsWritable.

Module IsSigner.
  Inductive t : Set := Yes | No.
End IsSigner.

Module IsOptional.
  Inductive t : Set := Yes | No.
End IsOptional.

Module Account.
  Parameter t : IsWritable.t -> IsSigner.t -> IsOptional.t -> option Z -> option unit -> Set.
End Account.

(* TODO Ensure this is correct *)
Module UncheckedAccount.
  Parameter t : Set.
  (* Maybe this should be a type class (as in the reference this is a trait) *)
  Parameter to_account_info : forall (self : UncheckedAccount.t), AccountInfo.
End UncheckedAccount.

Module Signer.
  Parameter t : Set.

  Parameter lamports : forall (self : Signer.t), u64.
  Parameter key : forall (self : Signer.t), Pubkey.
  (* Maybe this should be a type class (as in the reference this is a trait) *)
  Parameter to_account_info : forall (self : Signer.t), AccountInfo.
End Signer.

Module System.
  Parameter t : Set.

  (* Maybe this should be a type class (as in the reference this is a trait) *)
  Parameter to_account_info : forall (self : System.t), AccountInfo.
End System.

Module Context.
  Record t {Accounts : Set} : Set := {
    (* program : AccountInfo; *)
    accounts : Accounts;
  }.
  Arguments t : clear implicits.

  Parameter new : forall {Accounts : Set}, AccountInfo -> Accounts -> Context.t Accounts.
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


Module SystemProgram.
  Module Transfer.
    Record t : Set := {
      from : AccountInfo;
      to : AccountInfo;
    }.
  End Transfer.

  Parameter transfer : forall {Accounts : Set},
    Context.t Accounts -> u64 -> Result.t unit.
End SystemProgram.

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
