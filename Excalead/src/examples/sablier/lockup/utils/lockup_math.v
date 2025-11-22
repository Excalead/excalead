From Excalead Require Import Excalead Anchor_lang Tactics.

From Excalead.examples.sablier.lockup Require Import
  state.lockup.

Parameter get_current_time : unit -> u64.

Definition get_streamed_amount
    (timestamps : Timestamps.t)
    (amounts : Amounts.t)
    (is_depleted : bool)
    (was_canceled : bool) :
    u64 :=
  if is_depleted then
    amounts.(Amounts.withdrawn)
  else
  if was_canceled then
    amounts.(Amounts.deposited) -i amounts.(Amounts.refunded)
  else
  let now := get_current_time tt in
  if timestamps.(Timestamps.start) >i now then
    0
  else
  if timestamps.(Timestamps.cliff) >i now then
    amounts.(Amounts.start_unlock)
  else
  if timestamps.(Timestamps.end_) <=i now then
    amounts.(Amounts.deposited)
  else
  let unlock_amounts_sum := amounts.(Amounts.start_unlock) +i amounts.(Amounts.cliff_unlock) in
  if unlock_amounts_sum >=i amounts.(Amounts.deposited) then
    amounts.(Amounts.deposited)
  else
  let streaming_start_time :=
    if timestamps.(Timestamps.cliff) =i 0 then
      timestamps.(Timestamps.start)
    else
      timestamps.(Timestamps.cliff) in
  let SCALING_FACTOR : u128 := 10 ^ 18 in
  let elapsed_time := ((now -i streaming_start_time) ias IntegerKind.U128) *i SCALING_FACTOR in
  let streamable_range := (timestamps.(Timestamps.end_) -i streaming_start_time) ias IntegerKind.U128 in
  let elapsed_time_percentage := elapsed_time /i streamable_range in
  let streamable_amount := (amounts.(Amounts.deposited) -i unlock_amounts_sum) ias IntegerKind.U128 in
  let streamed_amount :=
    unlock_amounts_sum +i
    (((elapsed_time_percentage *i streamable_amount) /i SCALING_FACTOR) ias IntegerKind.U64) in
  if streamed_amount >i amounts.(Amounts.deposited) then
    amounts.(Amounts.withdrawn)
  else
  streamed_amount.

Definition get_withdrawable_amount
    (timestamps : Timestamps.t)
    (amounts : Amounts.t)
    (is_depleted : bool)
    (was_canceled : bool) :
    u64 :=
  get_streamed_amount timestamps amounts is_depleted was_canceled -i amounts.(Amounts.withdrawn).
