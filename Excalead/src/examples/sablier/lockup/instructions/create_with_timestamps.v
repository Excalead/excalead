From Excalead Require Import Excalead Anchor_lang.

From Excalead.examples.sablier.lockup Require Import
  state.lockup
  utils.validations.

Module CreateWithTimestamps.
  Record t : Set := {
    stream_data : StreamData.t;
  }.
End CreateWithTimestamps.

(** This is not the exact original definition, but we take the parameters that are required for the
    calculation of the stream data. *)
Definition handler
    (accounts : CreateWithTimestamps.t)
    (deposited_token_mint : Pubkey)
    (stream_data_bump : u8)
    (sender : Pubkey)
    (salt : u128)
    (deposit_amount : u64)
    (start_time : u64)
    (cliff_time : u64)
    (end_time : u64)
    (start_unlock_amount : u64)
    (cliff_unlock_amount : u64)
    (is_cancelable : bool) :
    Result.t unit :=
  let? _ :=
    validations.check_create
      deposit_amount
      start_time
      cliff_time
      end_time
      start_unlock_amount
      cliff_unlock_amount in
  let accounts := accounts <|
    CreateWithTimestamps.stream_data :=
      StreamData.create
        accounts.(CreateWithTimestamps.stream_data)
        deposited_token_mint
        stream_data_bump
        cliff_time
        cliff_unlock_amount
        deposit_amount
        end_time
        salt
        is_cancelable
        sender
        start_time
        start_unlock_amount
  |> in
  Result.Ok tt.
