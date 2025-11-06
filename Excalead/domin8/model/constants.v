Require Import Excalead.Excalead.

Definition SEED : string := "anchor".

Definition GAME_STATUS_OPEN : u8 := 0.
Definition GAME_STATUS_CLOSED : u8 := 1.

Definition MAX_HOUSE_FEE : u64 := 1000.

Definition MIN_ROUND_TIME : u64 := 10.
Definition MAX_ROUND_TIME : u64 := 86400.
Definition MIN_DEPOSIT_AMOUNT : u64 := 1_000_000.

Definition VRF_FORCE_LENGTH : usize := 32.

Definition BET_INFO_SIZE : usize := 2 + 8 + 1 + 4.
Definition WALLET_SIZE : usize := 32.
Definition MAX_BETS_PER_GAME : usize := 1000.
Definition MAX_BETS_PER_USER_SMALL : usize := 20.
Definition MAX_BETS_PER_USER_LARGE : usize := 30.
Definition SMALL_BET_THRESHOLD : u64 := 10_000_000.

Definition BASE_GAME_ACCOUNT_SIZE : usize := 8 + (* discriminator *)
    8 + (* game_round *)
    8 + (* start_date *)
    8 + (* end_date *)
    8 + (* total_deposit *)
    8 + (* rand *)
    1 + 32 + (* winner (Option<Pubkey>) *)
    8 + (* winner_prize *)
    1 + 8 + (* winning_bet_index (Option<u64>) *)
    8 + (* user_count *)
    32 + (* force ([u8; 32]) *)
    1 + (* status *)
    4 + 4 + 15 + 20. (* wallets Vec<Pubkey> (4) + bets Vec<BetInfo> (4) - actual data allocated dynamically *)