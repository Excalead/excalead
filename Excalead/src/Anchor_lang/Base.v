From Excalead Require Import Classes.

Parameter Hash : Set.

Parameter AccountInfo : Set.

Parameter Pubkey : Set.

Parameter Pubkey_eq : EqDec Pubkey.
#[export] Existing Instance Pubkey_eq.

Parameter bytes : Set.


