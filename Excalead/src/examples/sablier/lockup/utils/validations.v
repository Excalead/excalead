From Excalead Require Import Excalead Anchor_lang Tactics.

From Excalead.examples.sablier.lockup Require Import
  state.lockup
  utils.errors.

Definition assert_not (condition : bool) (error : ErrorCode.t) : Result.t unit :=
  if condition then
    Result.error error
  else
    Result.Ok tt.

Definition check_create
    (deposit_amount : u64)
    (start_time : u64)
    (cliff_time : u64)
    (end_time : u64)
    (start_unlock_amount : u64)
    (cliff_unlock_amount : u64) :
    Result.t unit :=
  let? _ := assert_not (deposit_amount =i 0) ErrorCode.DepositAmountZero in
  let? _ := assert_not (start_time =i 0) ErrorCode.StartTimeZero in
  let? _ := assert_not (start_time >=i end_time) ErrorCode.StartTimeNotLessThanEndTime in
  let? _ :=
    if cliff_time >i 0 then
      let? _ := assert_not (start_time >=i cliff_time) ErrorCode.StartTimeNotLessThanCliffTime in
      let? _ := assert_not (cliff_time >=i end_time) ErrorCode.CliffTimeNotLessThanEndTime in
      Result.Ok tt
    else
      let? _ := assert_not (cliff_unlock_amount >i 0) ErrorCode.CliffTimeZeroUnlockAmountNotZero in
      Result.Ok tt
  in
  let? total_unlock_amount :=
    match start_unlock_amount +i? cliff_unlock_amount with
    | None => Result.error ErrorCode.UnlockAmountsSumTooHigh
    | Some total_unlock_amount => Result.Ok total_unlock_amount
    end in
  let? _ := assert_not (total_unlock_amount >i deposit_amount) ErrorCode.UnlockAmountsSumTooHigh in
  Result.Ok tt.

(** If the [check_create] function succeeds, then we will make a valid [StreamData] element. *)
Lemma check_create_is_valid
    stream_data deposit_token_mint bump
    cliff_time cliff_unlock_amount deposit_amount end_time
    salt is_cancelable sender
    start_time start_unlock_amount
    (H_bump : Integer.Valid.t bump)
    (H_salt : Integer.Valid.t salt)
    (H_deposit_amount : Integer.Valid.t deposit_amount)
    (H_start_time : Integer.Valid.t start_time)
    (H_cliff_time : Integer.Valid.t cliff_time)
    (H_end_time : Integer.Valid.t end_time)
    (H_start_unlock_amount : Integer.Valid.t start_unlock_amount)
    (H_cliff_unlock_amount : Integer.Valid.t cliff_unlock_amount) :
  match
    check_create
      deposit_amount start_time cliff_time end_time start_unlock_amount cliff_unlock_amount
  with
  | Result.Err _ => True
  | Result.Ok _ =>
    StreamData.Valid.t (
      StreamData.create
        stream_data deposit_token_mint bump
        cliff_time cliff_unlock_amount deposit_amount end_time
        salt is_cancelable sender
        start_time start_unlock_amount
    )
  end.
Proof.
  unfold check_create; cbn in *.
  unfold "+i?", BinOp.Checked.make_arithmetic, Integer.normalize_option.
  destruct (_ =? _) eqn:? in |- *; cbn; trivial.
  destruct (_ =? _) eqn:? in |- *; cbn; trivial.
  destruct (_ >=? _) eqn:? in |- *; cbn; trivial.
  destruct (_ >? _) eqn:? in |- *; cbn; trivial.
  { destruct (_ >=? _) eqn:? in |- *; cbn; trivial.
    destruct (_ >=? _) eqn:? in |- *; cbn; trivial.
    do 2 (destruct (_ <? _) in |- *; cbn; trivial).
    destruct (_ >? _) eqn:? in |- *; cbn; trivial.
    repeat (
      constructor ||
      cbn ||
      lia
    ).
  }
  { destruct (_ >? _) eqn:? in |- *; cbn; trivial.
    do 2 (destruct (_ <? _) in |- *; cbn; trivial).
    destruct (_ >? _) eqn:? in |- *; cbn; trivial.
    repeat (
      constructor ||
      cbn ||
      lia
    ).
  }
Qed.
