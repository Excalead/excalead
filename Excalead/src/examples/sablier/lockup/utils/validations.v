From Excalead Require Import Excalead Anchor_lang.

From Excalead.examples.sablier.lockup Require Import utils.errors.

Definition check_create
    (deposit_amount : u64)
    (start_time : u64)
    (cliff_time : u64)
    (end_time : u64)
    (start_unlock_amount : u64)
    (cliff_unlock_amount : u64) :
    Result.t unit :=
  if deposit_amount =i 0 then
    Result.error (ErrorCode.DepositAmountZero)
  else if start_time =i 0 then
    Result.error (ErrorCode.StartTimeZero)
  else if start_time >=i end_time then
    Result.error (ErrorCode.StartTimeNotLessThanEndTime)
  else if cliff_time >i 0 then
    if start_time >=i cliff_time then
      Result.error (ErrorCode.StartTimeNotLessThanCliffTime)
    else if cliff_time >=i end_time then
      Result.error (ErrorCode.CliffTimeNotLessThanEndTime)
    else if cliff_unlock_amount >i 0 then
      Result.error (ErrorCode.CliffTimeZeroUnlockAmountNotZero)
    else
      Ok tt
  else if cliff_unlock_amount >i 0 then
    Result.error (ErrorCode.CliffTimeZeroUnlockAmountNotZero)
  else
    Result.Ok tt.
