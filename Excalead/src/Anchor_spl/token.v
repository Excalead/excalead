From Excalead Require Import Excalead Anchor_lang.

Module TokenAccount.
  Parameter t : Set.

  Parameters owner : forall (self : t), Pubkey.t.
End TokenAccount.
