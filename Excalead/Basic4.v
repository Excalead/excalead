Require Import Coq.ZArith.ZArith.

From Excalead Require Import RecordUpdate.

Global Open Scope Z_scope.

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

(** Error codes *)
Module ErrorCode.
  Inductive t : Set :=
  | Unauthorized.
End ErrorCode.

(** Counter account *)
Module Counter.
  Record t : Set := {
    authority : Pubkey;
    count : u64;
    bump : u8;
  }.

  Definition COUNTER_SIZE : usize :=
    8 + 32 + 8 + 1.
End Counter.

Module Account.
  Record t {A : Set} : Set := {
    account : A;
  }.
  Arguments t : clear implicits.
End Account.

Module Signer.
  Parameter t : Set.

  Parameter key : forall (self : t), Pubkey.
End Signer.

Module Program.
  Parameter t : Set -> Set.
End Program.

Module System.
  Parameter t : Set.
End System.

Module Initialize.
  Record t : Set := {
    counter : Account.t Counter.t;
    authority : Signer.t;
    system_program : Program.t System.t;
  }.

  Module Bumps.
    Record t : Set := {
      counter : u8;
    }.
  End Bumps.
End Initialize.

Module Increment.
  Record t : Set := {
    counter : Account.t Counter.t;
    authority : Signer.t;
  }.
End Increment.

Module Result.
  Inductive t (A : Set) :=
  | Ok : A -> t A
  | Err : ErrorCode.t -> t A.
  Arguments Ok {A} _.
  Arguments Err {A} _.
End Result.

Module Context.
  Record t {Accounts Bumps : Set} : Set := {
    accounts : Accounts;
    bumps : Bumps;
  }.
  Arguments t : clear implicits.
End Context.

Module program.
  Definition initialize (ctx : Context.t Initialize.t Initialize.Bumps.t) : Result.t Initialize.t :=
    let bump := ctx.(Context.bumps).(Initialize.Bumps.counter) in

    let ctx := ctx <|
      Context.accounts := ctx.(Context.accounts) <|
        Initialize.counter :=
          ctx.(Context.accounts).(Initialize.counter) <|
          Account.account :=
            ctx.(Context.accounts).(Initialize.counter).(Account.account)
              <| Counter.authority := Signer.key ctx.(Context.accounts).(Initialize.authority) |>
              <| Counter.count := 0 |>
              <| Counter.bump := bump |>
          |>
      |>
    |> in

    Result.Ok ctx.(Context.accounts).
End program.

  (** Contexts *)
  Record InitializeCtx := mkInitializeCtx {
    counter : Counter;
    authority : bytes32;
    system_program : unit
  }.

  Record IncrementCtx := mkIncrementCtx {
    counter : Counter;
    authority : bytes32
  }.

  (** Result type *)
  Inductive Result (A : Type) :=
  | Ok : A -> Result A
  | Err : ErrorCode -> Result A.

  Arguments Ok {A} _.
  Arguments Err {A} _.

  (** Helper for key equality *)
  Definition require_keys_eq (k1 k2 : bytes32) : Result unit :=
    if k1 =? k2 then Ok tt else Err Unauthorized.

  (** initialize instruction *)
  Definition initialize (ctx : InitializeCtx) : Result Counter :=
    let bump := ctx.(counter).(bump) in
    let counter' := mkCounter ctx.(authority) 0 bump in
    Ok counter'.

  (** increment instruction *)
  Definition increment (ctx : IncrementCtx) : Result Counter :=
    match require_keys_eq ctx.(authority) ctx.(counter).(authority) with
    | Err e => Err e
    | Ok _ =>
      let c := ctx.(counter) in
      let c' := mkCounter c.(authority) (c.(count) + 1) c.(bump) in
      Ok c'
    end.

End Basic4.
