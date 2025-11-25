(* Generated file *)
From Excalead Require Import Excalead Anchor_lang.

(** Error codes *)
Module ErrorCode.
  Inductive t : Set :=
  (** Can't perform the action on a depleted stream! *)
  | StreamDepleted : t
  (** Can't renounce an already-renounced Stream! *)
  | StreamCanceled : t
  (** Can't cancel a non-cancelable Stream! *)
  | StreamIsNotCancelable : t
  (** Can't cancel a settled Stream! *)
  | StreamSettled : t
  (** Can't collect zero fees! *)
  | CantCollectZeroFees : t
  (** Invalid cliff time of the Stream! *)
  | CliffTimeNotLessThanEndTime : t
  (** Cliff time zero but unlock amount not zero! *)
  | CliffTimeZeroUnlockAmountNotZero : t
  (** Invalid deposit amount! *)
  | DepositAmountZero : t
  (** Start time must be less than cliff time! *)
  | StartTimeNotLessThanCliffTime : t
  (** Start time must be less than end time! *)
  | StartTimeNotLessThanEndTime : t
  (** Start time can't be zero! *)
  | StartTimeZero : t
  (** Unlock amounts sum is greater than deposit amount! *)
  | UnlockAmountsSumTooHigh : t
  (** Can't renounce a non-cancelable Stream! *)
  | StreamAlreadyNonCancelable : t
  (** Attempting to withdraw more than available in the stream! *)
  | Overdraw : t
  (** Can't withdraw a zero amount! *)
  | WithdrawAmountZero : t.
End ErrorCode.

(** Custom types *)
Module Timestamps.
  Record t : Set := {
    cliff : u64;
    end_ : u64;
    start : u64;
  }.
End Timestamps.

Module Amounts.
  Record t : Set := {
    start_unlock : u64;
    cliff_unlock : u64;
    deposited : u64;
    refunded : u64;
    withdrawn : u64;
  }.
End Amounts.

Module CancelLockupStream.
  Record t : Set := {
    deposited_token_mint : Pubkey.t;
    recipient_amount : u64;
    sender_amount : u64;
    stream_data : Pubkey.t;
    stream_nft_mint : Pubkey.t;
  }.
End CancelLockupStream.

Module CreateLockupLinearStream.
  Record t : Set := {
    deposit_token_decimals : u8;
    deposit_token_mint : Pubkey.t;
    recipient : Pubkey.t;
    salt : u128;
    stream_data : Pubkey.t;
    stream_nft_mint : Pubkey.t;
  }.
End CreateLockupLinearStream.

Module FeesCollected.
  Record t : Set := {
    fee_amount : u64;
    fee_collector : Pubkey.t;
    fee_recipient : Pubkey.t;
  }.
End FeesCollected.

Module NftCollectionData.
  Record t : Set := {
    total_supply : u64;
    bump : u8;
  }.
End NftCollectionData.

Module RenounceLockupStream.
  Record t : Set := {
    deposited_token_mint : Pubkey.t;
    stream_data : Pubkey.t;
    stream_nft_mint : Pubkey.t;
  }.
End RenounceLockupStream.

Module StreamData.
  Record t : Set := {
    amounts : Amounts.t;
    deposited_token_mint : Pubkey.t;
    bump : u8;
    salt : u128;
    is_cancelable : bool;
    is_depleted : bool;
    timestamps : Timestamps.t;
    sender : Pubkey.t;
    was_canceled : bool;
  }.
End StreamData.

Module StreamStatus.
  Inductive t : Set :=
  | Pending
  | Streaming
  | Settled
  | Canceled
  | Depleted.
End StreamStatus.

Module Treasury.
  Record t : Set := {
    bump : u8;
    fee_collector : Pubkey.t;
    chainlink_program : Pubkey.t;
    chainlink_sol_usd_feed : Pubkey.t;
  }.
End Treasury.

Module WithdrawFromLockupStream.
  Record t : Set := {
    deposited_token_mint : Pubkey.t;
    fee_in_lamports : u64;
    stream_data : Pubkey.t;
    stream_nft_mint : Pubkey.t;
    withdrawn_amount : u64;
  }.
End WithdrawFromLockupStream.

(** Account structures *)
Module AccountStructure.
  Inductive t : Set :=
  | NftCollectionData : t
  | StreamData : t
  | Treasury : t.
End AccountStructure.

(** Instruction contexts *)
Module Instruction.
  Inductive t : Set -> Set :=
  | cancel
    (* Accounts *)
      (sender : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        Address.Any
        Pda.No
      )
      (sender_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "sender" None;
            PdaSeed.Account "deposited_token_program" None;
            PdaSeed.Account "deposited_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (deposited_token_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (stream_data : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_data_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "stream_data" None;
            PdaSeed.Account "deposited_token_program" None;
            PdaSeed.Account "deposited_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (stream_nft_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (associated_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL")
        Pda.No
      )
      (deposited_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (system_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "11111111111111111111111111111111")
        Pda.No
      )
    (* Arguments *)
    (* Return *)
      : t unit
  | collect_fees
    (* Accounts *)
      (fee_collector : Account.t
        IsWritable.No
        IsSigner.Yes
        IsOptional.No
        Address.Any
        Pda.No
      )
      (fee_recipient : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (treasury : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [116; 114; 101; 97; 115; 117; 114; 121]
          ]
          None
        )
      )
    (* Arguments *)
    (* Return *)
      : t unit
  | create_with_durations_ll
    (* Accounts *)
      (creator : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        Address.Any
        Pda.No
      )
      (creator_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "creator" None;
            PdaSeed.Account "deposit_token_program" None;
            PdaSeed.Account "deposit_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (recipient : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (sender : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (nft_collection_data : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [110; 102; 116; 95; 99; 111; 108; 108; 101; 99; 116; 105; 111; 110; 95; 100; 97; 116; 97]
          ]
          None
        )
      )
      (nft_collection_master_edition : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "nft_collection_mint" None;
            PdaSeed.Const [101; 100; 105; 116; 105; 111; 110]
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (nft_collection_metadata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "nft_collection_mint" None
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (nft_collection_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [110; 102; 116; 95; 99; 111; 108; 108; 101; 99; 116; 105; 111; 110; 95; 109; 105; 110; 116]
          ]
          None
        )
      )
      (deposit_token_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (stream_nft_mint : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 110; 102; 116; 95; 109; 105; 110; 116];
            PdaSeed.Account "sender" None;
            PdaSeed.Arg "salt"
          ]
          None
        )
      )
      (recipient_stream_nft_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "recipient" None;
            PdaSeed.Account "nft_token_program" None;
            PdaSeed.Account "stream_nft_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (stream_data : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_data_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "stream_data" None;
            PdaSeed.Account "deposit_token_program" None;
            PdaSeed.Account "deposit_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (stream_nft_master_edition : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "stream_nft_mint" None;
            PdaSeed.Const [101; 100; 105; 116; 105; 111; 110]
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (stream_nft_metadata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "stream_nft_mint" None
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (associated_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL")
        Pda.No
      )
      (deposit_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (nft_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (token_metadata_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "metaqbxxUerdq28cj1RbAWkYQm3ybzjb6a8bt518x1s")
        Pda.No
      )
      (system_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "11111111111111111111111111111111")
        Pda.No
      )
      (rent : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "SysvarRent111111111111111111111111111111111")
        Pda.No
      )
    (* Arguments *)
      (salt : u128)
      (deposit_amount : u64)
      (cliff_duration : u64)
      (total_duration : u64)
      (start_unlock_amount : u64)
      (cliff_unlock_amount : u64)
      (is_cancelable : bool)
    (* Return *)
      : t unit
  | create_with_timestamps_ll
    (* Accounts *)
      (creator : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        Address.Any
        Pda.No
      )
      (creator_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "creator" None;
            PdaSeed.Account "deposit_token_program" None;
            PdaSeed.Account "deposit_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (recipient : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (sender : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (nft_collection_data : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [110; 102; 116; 95; 99; 111; 108; 108; 101; 99; 116; 105; 111; 110; 95; 100; 97; 116; 97]
          ]
          None
        )
      )
      (nft_collection_master_edition : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "nft_collection_mint" None;
            PdaSeed.Const [101; 100; 105; 116; 105; 111; 110]
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (nft_collection_metadata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "nft_collection_mint" None
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (nft_collection_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [110; 102; 116; 95; 99; 111; 108; 108; 101; 99; 116; 105; 111; 110; 95; 109; 105; 110; 116]
          ]
          None
        )
      )
      (deposit_token_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (stream_nft_mint : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 110; 102; 116; 95; 109; 105; 110; 116];
            PdaSeed.Account "sender" None;
            PdaSeed.Arg "salt"
          ]
          None
        )
      )
      (recipient_stream_nft_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "recipient" None;
            PdaSeed.Account "nft_token_program" None;
            PdaSeed.Account "stream_nft_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (stream_data : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_data_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "stream_data" None;
            PdaSeed.Account "deposit_token_program" None;
            PdaSeed.Account "deposit_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (stream_nft_master_edition : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "stream_nft_mint" None;
            PdaSeed.Const [101; 100; 105; 116; 105; 111; 110]
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (stream_nft_metadata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "stream_nft_mint" None
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (associated_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL")
        Pda.No
      )
      (deposit_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (nft_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (token_metadata_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "metaqbxxUerdq28cj1RbAWkYQm3ybzjb6a8bt518x1s")
        Pda.No
      )
      (system_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "11111111111111111111111111111111")
        Pda.No
      )
      (rent : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "SysvarRent111111111111111111111111111111111")
        Pda.No
      )
    (* Arguments *)
      (salt : u128)
      (deposit_amount : u64)
      (start_time : u64)
      (cliff_time : u64)
      (end_time : u64)
      (start_unlock_amount : u64)
      (cliff_unlock_amount : u64)
      (is_cancelable : bool)
    (* Return *)
      : t unit
  | initialize
    (* Accounts *)
      (initializer : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        Address.Any
        Pda.No
      )
      (treasury : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [116; 114; 101; 97; 115; 117; 114; 121]
          ]
          None
        )
      )
      (nft_collection_data : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [110; 102; 116; 95; 99; 111; 108; 108; 101; 99; 116; 105; 111; 110; 95; 100; 97; 116; 97]
          ]
          None
        )
      )
      (nft_collection_master_edition : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "nft_collection_mint" None;
            PdaSeed.Const [101; 100; 105; 116; 105; 111; 110]
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (nft_collection_metadata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [109; 101; 116; 97; 100; 97; 116; 97];
            PdaSeed.Account "token_metadata_program" None;
            PdaSeed.Account "nft_collection_mint" None
          ]
          (Some (PdaSeed.Account "token_metadata_program" None))
        )
      )
      (nft_collection_mint : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [110; 102; 116; 95; 99; 111; 108; 108; 101; 99; 116; 105; 111; 110; 95; 109; 105; 110; 116]
          ]
          None
        )
      )
      (nft_collection_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "treasury" None;
            PdaSeed.Account "nft_token_program" None;
            PdaSeed.Account "nft_collection_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (associated_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL")
        Pda.No
      )
      (nft_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (token_metadata_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "metaqbxxUerdq28cj1RbAWkYQm3ybzjb6a8bt518x1s")
        Pda.No
      )
      (rent : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "SysvarRent111111111111111111111111111111111")
        Pda.No
      )
      (system_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "11111111111111111111111111111111")
        Pda.No
      )
    (* Arguments *)
      (fee_collector : Pubkey.t)
      (chainlink_program : Pubkey.t)
      (chainlink_sol_usd_feed : Pubkey.t)
    (* Return *)
      : t unit
  | refundable_amount_of
    (* Accounts *)
      (stream_data : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_nft_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
    (* Arguments *)
    (* Return *)
       : t u64
  | renounce
    (* Accounts *)
      (sender : Account.t
        IsWritable.No
        IsSigner.Yes
        IsOptional.No
        Address.Any
        Pda.No
      )
      (stream_data : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_nft_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
    (* Arguments *)
    (* Return *)
      : t unit
  | status_of
    (* Accounts *)
      (stream_data : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_nft_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
    (* Arguments *)
    (* Return *)
       : t StreamStatus.t
  | stream_exists
    (* Accounts *)
      (stream_nft_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 110; 102; 116; 95; 109; 105; 110; 116];
            PdaSeed.Arg "_sender";
            PdaSeed.Arg "_salt"
          ]
          None
        )
      )
    (* Arguments *)
      (_sender : Pubkey.t)
      (_salt : u128)
    (* Return *)
       : t bool
  | streamed_amount_of
    (* Accounts *)
      (stream_data : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_nft_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
    (* Arguments *)
    (* Return *)
       : t u64
  | treasury_view
    (* Accounts *)
      (treasury : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [116; 114; 101; 97; 115; 117; 114; 121]
          ]
          None
        )
      )
    (* Arguments *)
    (* Return *)
       : t Treasury.t
  | withdraw
    (* Accounts *)
      (signer : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        Address.Any
        Pda.No
      )
      (stream_recipient : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (withdrawal_recipient : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (withdrawal_recipient_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "withdrawal_recipient" None;
            PdaSeed.Account "deposited_token_program" None;
            PdaSeed.Account "deposited_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (treasury : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [116; 114; 101; 97; 115; 117; 114; 121]
          ]
          None
        )
      )
      (deposited_token_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (recipient_stream_nft_ata : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "stream_recipient" None;
            PdaSeed.Account "nft_token_program" None;
            PdaSeed.Account "stream_nft_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (stream_data : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_data_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "stream_data" None;
            PdaSeed.Account "deposited_token_program" None;
            PdaSeed.Account "deposited_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (stream_nft_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (associated_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL")
        Pda.No
      )
      (chainlink_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (chainlink_sol_usd_feed : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (deposited_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (nft_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (system_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "11111111111111111111111111111111")
        Pda.No
      )
    (* Arguments *)
      (amount : u64)
    (* Return *)
      : t unit
  | withdraw_max
    (* Accounts *)
      (signer : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        Address.Any
        Pda.No
      )
      (stream_recipient : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (withdrawal_recipient : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (withdrawal_recipient_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "withdrawal_recipient" None;
            PdaSeed.Account "deposited_token_program" None;
            PdaSeed.Account "deposited_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (treasury : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [116; 114; 101; 97; 115; 117; 114; 121]
          ]
          None
        )
      )
      (deposited_token_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (recipient_stream_nft_ata : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "stream_recipient" None;
            PdaSeed.Account "nft_token_program" None;
            PdaSeed.Account "stream_nft_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (stream_data : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_data_ata : Account.t
        IsWritable.Yes
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Account "stream_data" None;
            PdaSeed.Account "deposited_token_program" None;
            PdaSeed.Account "deposited_token_mint" None
          ]
          (Some (PdaSeed.Const [140; 151; 37; 143; 78; 36; 137; 241; 187; 61; 16; 41; 20; 142; 13; 131; 11; 90; 19; 153; 218; 255; 16; 132; 4; 142; 123; 216; 219; 233; 248; 89]))
        )
      )
      (stream_nft_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (associated_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL")
        Pda.No
      )
      (chainlink_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (chainlink_sol_usd_feed : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (deposited_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (nft_token_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (system_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Address.Constant "11111111111111111111111111111111")
        Pda.No
      )
    (* Arguments *)
    (* Return *)
      : t unit
  | withdrawable_amount_of
    (* Accounts *)
      (stream_data : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [115; 116; 114; 101; 97; 109; 95; 100; 97; 116; 97];
            PdaSeed.Account "stream_nft_mint" None
          ]
          None
        )
      )
      (stream_nft_mint : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
    (* Arguments *)
    (* Return *)
       : t u64
  | withdrawal_fee_in_lamports
    (* Accounts *)
      (treasury : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        (Pda.Yes [
            PdaSeed.Const [116; 114; 101; 97; 115; 117; 114; 121]
          ]
          None
        )
      )
      (chainlink_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
      (chainlink_sol_usd_feed : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        Address.Any
        Pda.No
      )
    (* Arguments *)
    (* Return *)
       : t u64.
End Instruction.

