Require Import Base.

Class Key (X : Type) :=
  key : forall (self : X), Pubkey.

Class ToAccountInfo (X : Type) :=
  to_account_info : forall (self : X), AccountInfo.


