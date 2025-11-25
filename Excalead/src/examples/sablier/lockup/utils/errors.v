From Excalead Require Import Excalead Anchor_lang.

Module ErrorCode.
  Inductive t : Set :=
  | StreamDepleted : t
  | StreamCanceled : t
  | StreamIsNotCancelable : t
  | StreamSettled : t
  | CantCollectZeroFees : t
  | CliffTimeNotLessThanEndTime : t
  | CliffTimeZeroUnlockAmountNotZero : t
  | DepositAmountZero : t
  | StartTimeNotLessThanCliffTime : t
  | StartTimeNotLessThanEndTime : t
  | StartTimeZero : t
  | UnlockAmountsSumTooHigh : t
  | StreamAlreadyNonCancelable : t
  | Overdraw : t
  | WithdrawAmountZero : t.

  Global Instance ErrorCode_to_string : ToErrorString.C t := {|
    ToErrorString.to_error_string e :=
      match e with
      | StreamDepleted => "StreamDepleted"
      | StreamCanceled => "StreamCanceled"
      | StreamIsNotCancelable => "StreamIsNotCancelable"
      | StreamSettled => "StreamSettled"
      | CantCollectZeroFees => "CantCollectZeroFees"
      | CliffTimeNotLessThanEndTime => "CliffTimeNotLessThanEndTime"
      | CliffTimeZeroUnlockAmountNotZero => "CliffTimeZeroUnlockAmountNotZero"
      | DepositAmountZero => "DepositAmountZero"
      | StartTimeNotLessThanCliffTime => "StartTimeNotLessThanCliffTime"
      | StartTimeNotLessThanEndTime => "StartTimeNotLessThanEndTime"
      | StartTimeZero => "StartTimeZero"
      | UnlockAmountsSumTooHigh => "UnlockAmountsSumTooHigh"
      | StreamAlreadyNonCancelable => "StreamAlreadyNonCancelable"
      | Overdraw => "Overdraw"
      | WithdrawAmountZero => "WithdrawAmountZero"
      end;
    |}.
End ErrorCode.
