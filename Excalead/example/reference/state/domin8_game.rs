use anchor_lang::prelude::*;

/// Bet information with game-specific data for domin8
#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy, Debug)]
pub struct BetInfo {
    pub wallet_index: u16,  // Index into the wallets Vec
    pub amount: u64,        // Bet amount in lamports
    pub skin: u8,           // Character skin ID (0-255)
    pub position: [u16; 2], // [x, y] spawn position on map
}

/// Main game state account
#[account]
pub struct Domin8Game {
    pub game_round: u64,
    pub start_date: i64,
    pub end_date: i64,
    pub total_deposit: u64,
    pub rand: u64,
    pub background: u8, // Background ID (0-255)
    pub user_count: u64,
    pub force: [u8; 32], // VRF force seed for this game
    pub status: u8,      // 0 = open, 1 = closed
    pub winner: Option<Pubkey>,
    pub winner_prize: u64, // Prize amount to be claimed by winner
    pub winning_bet_index: Option<u64>,
    pub wallets: Vec<Pubkey>, // Unique wallets (stored once)
    pub bets: Vec<BetInfo>,   // (wallet_index, amount, skin, position) tuples
}
