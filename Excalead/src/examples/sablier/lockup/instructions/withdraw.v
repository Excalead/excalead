From Excalead Require Import Excalead Anchor_lang Tactics.

From Excalead.examples.sablier.lockup Require Import
  state.lockup
  utils.lockup_math
  utils.validations.

(** We assume that the fee is always [@] due to the [WITHDRAWAL_FEE_USD] constant being zero. *)
Definition charge_withdrawal_fee : u64 := 0.

Module Withdraw.
  Record t : Set := {
    stream_data : StreamData.t;
  }.
End Withdraw.

Definition handler (accounts : Withdraw.t) (amount : u64) : Result.t Withdraw.t :=
  let? _ :=
    validations.check_withdraw
      accounts.(Withdraw.stream_data).(StreamData.is_depleted)
      amount
      (get_withdrawable_amount
        accounts.(Withdraw.stream_data).(StreamData.timestamps)
        accounts.(Withdraw.stream_data).(StreamData.amounts)
        accounts.(Withdraw.stream_data).(StreamData.is_depleted)
        accounts.(Withdraw.stream_data).(StreamData.was_canceled)
      )
    in
  let? stream_data := StreamData.withdraw accounts.(Withdraw.stream_data) amount in
  let accounts := accounts <| Withdraw.stream_data := stream_data |> in
  Result.Ok accounts.
