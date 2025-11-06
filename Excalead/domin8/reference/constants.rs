use anchor_lang::prelude::*;

#[constant]
pub const SEED: &str = "anchor";

// Game status constants
pub const GAME_STATUS_OPEN: u8 = 0;
pub const GAME_STATUS_CLOSED: u8 = 1;

// Fee constants (basis points)
pub const MAX_HOUSE_FEE: u64 = 1000; // 10%

// Time constants
pub const MIN_ROUND_TIME: u64 = 10;     // 10 seconds
pub const MAX_ROUND_TIME: u64 = 86400;  // 24 hours
pub const MIN_DEPOSIT_AMOUNT: u64 = 1_000_000; // 0.001 SOL

// VRF constants
pub const VRF_FORCE_LENGTH: usize = 32; // 32 bytes

// Account size constants
pub const BET_INFO_SIZE: usize = 2 + 8 + 1 + 4; // wallet_index (2) + amount (8) + skin (1) + position (2*2) = 15 bytes
pub const WALLET_SIZE: usize = 32; // Pubkey size
pub const MAX_BETS_PER_GAME: usize = 1000; // Reasonable limit
pub const MAX_BETS_PER_USER_SMALL: usize = 20; // Max bets per user for bets under 0.01 SOL
pub const MAX_BETS_PER_USER_LARGE: usize = 30; // Max bets per user for bets >= 0.01 SOL
pub const SMALL_BET_THRESHOLD: u64 = 10_000_000; // 0.01 SOL in lamports

pub const BASE_GAME_ACCOUNT_SIZE: usize = 8 + // discriminator
    8 + // game_round
    8 + // start_date
    8 + // end_date
    8 + // total_deposit
    8 + // rand
    1 + 32 + // winner (Option<Pubkey>)
    8 + // winner_prize
    1 + 8 + // winning_bet_index (Option<u64>)
    8 + // user_count
    32 + // force ([u8; 32])
    1 + // status
    4 + 4 + 15 + 20; // wallets Vec<Pubkey> (4) + bets Vec<BetInfo> (4) - actual data allocated dynamically
