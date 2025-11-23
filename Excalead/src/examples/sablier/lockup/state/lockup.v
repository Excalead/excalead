From Excalead Require Import Excalead Anchor_lang.

Module Amounts.
  Record t : Set := {
    start_unlock: u64;
    cliff_unlock: u64;
    deposited: u64;
    refunded: u64;
    withdrawn: u64;
  }.

  Module Valid.
    Record t (self : Amounts.t) : Prop := {
      start_unlock_valid : Integer.Valid.t self.(start_unlock);
      cliff_unlock_valid : Integer.Valid.t self.(cliff_unlock);
      deposited_valid : Integer.Valid.t self.(deposited);
      deposited_not_null : i[self.(deposited)] <> 0;
      refunded_valid : Integer.Valid.t self.(refunded);
      withdrawn_valid : Integer.Valid.t self.(withdrawn);
      total_unlock :
        i[self.(start_unlock)] + i[self.(cliff_unlock)] <=
        i[self.(deposited)];
      deposited_refunded_withdrawn :
        i[self.(refunded)] + i[self.(withdrawn)] <=
        i[self.(deposited)];
    }.
  End Valid.
End Amounts.

Module Timestamps.
  Record t : Set := {
    cliff: u64;
    end_: u64;
    start: u64;
  }.

  Module Valid.
    Record t (self : Timestamps.t) : Prop := {
      cliff_valid : Integer.Valid.t self.(cliff);
      end_valid : Integer.Valid.t self.(end_);
      start_valid : Integer.Valid.t self.(start);
      start_not_null : i[self.(start)] <> 0;
      start_before_end :
        i[self.(start)] < i[self.(end_)];
      start_before_cliff :
        i[self.(cliff)] <> 0 ->
        i[self.(start)] < i[self.(cliff)];
      cliff_before_end :
        i[self.(cliff)] <> 0 ->
        i[self.(cliff)] < i[self.(end_)];
    }.
  End Valid.
End Timestamps.

Module StreamData.
  Record t : Set := {
    amounts: Amounts.t;
    deposited_token_mint: Pubkey;
    bump: u8;
    salt: u128;
    is_cancelable: bool;
    is_depleted: bool;
    timestamps: Timestamps.t;
    sender: Pubkey;
    was_canceled: bool;
  }.

  Module Valid.
    Record t (self : t) : Prop := {
      amounts_valid : Amounts.Valid.t self.(amounts);
      bump_valid : Integer.Valid.t self.(bump);
      salt_valid : Integer.Valid.t self.(salt);
      timestamps_valid : Timestamps.Valid.t self.(timestamps);
      cliff_zeros :
        i[self.(timestamps).(Timestamps.cliff)] = 0 ->
        i[self.(amounts).(Amounts.cliff_unlock)] = 0;
    }.
  End Valid.

  Definition create
      (self : t)
      (deposited_token_mint: Pubkey)
      (bump: u8)
      (cliff_time: u64)
      (cliff_unlock_amount: u64)
      (deposit_amount: u64)
      (end_time: u64)
      (salt: u128)
      (is_cancelable: bool)
      (sender: Pubkey)
      (start_time: u64)
      (start_unlock_amount: u64) :
      t :=
    self
      <| StreamData.bump := bump |>
      <| StreamData.amounts :=
        {|
          Amounts.cliff_unlock := cliff_unlock_amount;
          Amounts.deposited := deposit_amount;
          Amounts.refunded := 0;
          Amounts.start_unlock := start_unlock_amount;
          Amounts.withdrawn := 0;
        |}
      |>
      <| StreamData.deposited_token_mint := deposited_token_mint |>
      <| StreamData.is_cancelable := is_cancelable |>
      <| StreamData.is_depleted := false |>
      <| StreamData.salt := salt |>
      <| StreamData.sender := sender |>
      <| StreamData.timestamps :=
        {|
          Timestamps.cliff := cliff_time;
          Timestamps.end_ := end_time;
          Timestamps.start := start_time;
        |}
      |>
      <| StreamData.was_canceled := false |>.

  Definition withdraw
      (self : t)
      (amount: u64) :
      Result.t t :=
    let? withdrawn :=
      match self.(amounts).(Amounts.withdrawn) +i? amount with
      | Some withdrawn => Result.Ok withdrawn
      | None => Result.Err "Withdrawn amount overflow"
      end
    in
    let '(is_cancelable, is_depleted) :=
      if withdrawn >=i self.(amounts).(Amounts.deposited) -i self.(amounts).(Amounts.refunded) then
        (false, true)
      else
        (self.(is_cancelable), self.(is_depleted))
    in
    Result.Ok (self
      <| StreamData.amounts := self.(amounts)
        <| Amounts.withdrawn := withdrawn |>
      |>
      <| StreamData.is_cancelable := is_cancelable |>
      <| StreamData.is_depleted := is_depleted |>
    ).
End StreamData.
