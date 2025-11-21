From Excalead Require Import Excalead Anchor_lang.

(** This is not the exact original definition, but we take the parameters that are required for the
    calculation of the stream data. *)
Definition handler
    (salt : u128)
    (deposit_amount : u64)
    (start_time : u64)
    (cliff_time : u64)
    (end_time : u64)
    (start_unlock_amount : u64)
    (cliff_unlock_amount : u64)
    (is_cancelable : bool) :
    unit.
Admitted.
