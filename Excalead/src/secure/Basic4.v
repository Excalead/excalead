From Excalead Require Import Excalead Anchor_lang.

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
  Parameter key : forall (self : Signer.t), Pubkey.
End Signer.

Module Program.
  Parameter t : Set -> Set.
End Program.

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
