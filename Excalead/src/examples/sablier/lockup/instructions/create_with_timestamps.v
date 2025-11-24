From Excalead Require Import Excalead Anchor_lang Tactics.

From Excalead.examples.sablier.lockup Require Import
  state.lockup
  utils.validations.

Module CreateWithTimestamps.
  Record t : Set := {
    stream_data : StreamData.t;
  }.

  Module Valid.
    Record t (self : t) : Prop := {
      stream_data_is_valid : StreamData.Valid.t self.(CreateWithTimestamps.stream_data);
    }.
  End Valid.
End CreateWithTimestamps.

(** This is not the exact original definition, but we take the parameters that are required for the
    calculation of the stream data. *)
Definition handler
    (accounts : CreateWithTimestamps.t)
    (deposited_token_mint : Pubkey)
    (stream_data_bump : u8)
    (sender : Pubkey.t)
    (salt : u128)
    (deposit_amount : u64)
    (start_time : u64)
    (cliff_time : u64)
    (end_time : u64)
    (start_unlock_amount : u64)
    (cliff_unlock_amount : u64)
    (is_cancelable : bool) :
    Result.t CreateWithTimestamps.t :=
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
  Result.Ok accounts.

Lemma handler_is_valid
    accounts deposited_token_mint stream_data_bump sender salt
    deposit_amount start_time cliff_time end_time
    start_unlock_amount cliff_unlock_amount is_cancelable
    (H_stream_data_bump : Integer.Valid.t stream_data_bump)
    (H_salt : Integer.Valid.t salt)
    (H_deposit_amount : Integer.Valid.t deposit_amount)
    (H_start_time : Integer.Valid.t start_time)
    (H_cliff_time : Integer.Valid.t cliff_time)
    (H_end_time : Integer.Valid.t end_time)
    (H_start_unlock_amount : Integer.Valid.t start_unlock_amount)
    (H_cliff_unlock_amount : Integer.Valid.t cliff_unlock_amount) :
  letP? accounts :=
    handler
      accounts deposited_token_mint stream_data_bump sender salt
      deposit_amount start_time cliff_time end_time
      start_unlock_amount cliff_unlock_amount is_cancelable in
  CreateWithTimestamps.Valid.t accounts.
Proof.
  unfold handler.
  pose proof (
    check_create_is_valid
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
  ).
  destruct check_create; cbn in *; trivial.
  constructor; cbn; tauto.
Qed.
