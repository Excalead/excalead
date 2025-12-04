Require Import Base.

Class Key (X : Type) :=
  key : forall (self : X), Pubkey.t.

Class ToAccountInfo (X : Type) :=
  to_account_info : forall (self : X), AccountInfo.t.
