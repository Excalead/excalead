use anchor_lang::prelude::*;

// Import modules
pub mod constants;
pub mod error;
pub mod instructions;
pub mod state;
pub mod utils;

// Import everything we need for the program
use instructions::*;

// Re-export public types for external use
pub use constants::*;
pub use error::*;
pub use state::*;
pub use utils::*;

declare_id!("JC7KUWuJH7SV9jcFM87J5tY1648G97jT1KShaZRy3tnj");

#[program]
pub mod domin8_prgm {
    use super::*;

    /// Initialize global domin8 configuration (admin only)
    ///
    /// Parameters:
    /// - treasury: Pubkey - Treasury wallet for house fees
    /// - house_fee: u64 - House fee in basis points (e.g., 500 = 5%)
    /// - min_deposit_amount: u64 - Minimum bet amount in lamports
    /// - max_deposit_amount: u64 - Maximum bet amount in lamports
    /// - round_time: u64 - Game duration in seconds
    pub fn initialize_config(
        ctx: Context<InitializeConfig>,
        treasury: Pubkey,
        house_fee: u64,
        min_deposit_amount: u64,
        max_deposit_amount: u64,
        round_time: u64,
    ) -> Result<()> {
        initialize_config::handler(ctx, treasury, house_fee, min_deposit_amount, max_deposit_amount, round_time)
    }

    /// Create new game round with first bet
    ///
    /// Parameters:
    /// - round_id: u64 - Round ID for the game
    /// - bet_amount: u64 - Initial bet amount in lamports
    /// - skin: u8 - Character skin ID (0-255)
    /// - position: [u16; 2] - Spawn position [x, y]
    pub fn create_game_round(
        ctx: Context<CreateGameRound>,
        round_id: u64,
        bet_amount: u64,
        skin: u8,
        position: [u16; 2],
    ) -> Result<()> {
        create_game_round::handler(ctx, round_id, bet_amount, skin, position)
    }

    /// Place a bet in the current game round
    ///
    /// Parameters:
    /// - round_id: u64 - Round ID for the game
    /// - bet_amount: u64 - Bet amount in lamports
    /// - skin: u8 - Character skin ID (0-255)
    /// - position: [u16; 2] - Spawn position [x, y]
    pub fn bet(
        ctx: Context<Bet>,
        round_id: u64,
        bet_amount: u64,
        skin: u8,
        position: [u16; 2],
    ) -> Result<()> {
        bet::handler(ctx, round_id, bet_amount, skin, position)
    }

    /// End game, draw winner, and distribute prizes (admin only)
    ///
    /// Parameters:
    /// - round_id: u64 - Round ID for the game
    pub fn end_game(ctx: Context<EndGame>, round_id: u64) -> Result<()> {
        end_game::handler(ctx, round_id)
    }

    /// Send prize to the winner of a completed game
    ///
    /// Parameters:
    /// - round_id: u64 - Round ID for the game
    pub fn send_prize_winner(ctx: Context<SendPrizeWinner>, round_id: u64) -> Result<()> {
        send_prize_winner::handler(ctx, round_id)
    }

    /// Delete a game round from the blockchain (admin only)
    ///
    /// Parameters:
    /// - round_id: u64 - Round ID for the game to delete
    pub fn delete_game(ctx: Context<DeleteGame>, round_id: u64) -> Result<()> {
        delete_game::handler(ctx, round_id)
    }
}
