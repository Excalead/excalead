use anchor_lang::prelude::*;

/// Global configuration for domin8 game
#[account]
pub struct Domin8Config {
    pub admin: Pubkey,              // Admin wallet (can manage config)
    pub treasury: Pubkey,            // Treasury wallet for house fees
    pub game_round: u64,            // Current/next game round number
    pub house_fee: u64,             // House fee in basis points (e.g., 500 = 5%)
    pub min_deposit_amount: u64,    // Minimum bet amount
    pub max_deposit_amount: u64,    // Maximum bet amount
    pub round_time: u64,            // Game duration in seconds
    pub lock: bool,                 // System lock (true when game is active)
    pub force: [u8; 32],            // VRF force seed for next game
}
