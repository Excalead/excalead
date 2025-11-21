use anchor_lang::prelude::*;
use crate::state::{GameConfig, GameRound, GameDurationConfig, GameStatus};
use crate::constants::*;

#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(
        init,
        payer = authority,
        space = GameConfig::LEN,
        seeds = [GAME_CONFIG_SEED],
        bump
    )]
    pub config: Account<'info, GameConfig>,
    
    #[account(
        init,
        payer = authority,
        space = GameRound::LEN,
        seeds = [GAME_ROUND_SEED],
        bump
    )]
    pub game_round: Account<'info, GameRound>,
    
    /// CHECK: This is the vault PDA that will hold game funds
    #[account(
        seeds = [VAULT_SEED],
        bump
    )]
    pub vault: UncheckedAccount<'info>,
    
    #[account(mut)]
    pub authority: Signer<'info>,
    
    pub system_program: Program<'info, System>,
}

pub fn initialize(
    ctx: Context<Initialize>,
    treasury: Pubkey,
) -> Result<()> {
    let config = &mut ctx.accounts.config;
    let game_round = &mut ctx.accounts.game_round;
    
    // Initialize game configuration
    config.authority = ctx.accounts.authority.key();
    config.treasury = treasury;
    config.house_fee_basis_points = HOUSE_FEE_BASIS_POINTS;
    config.min_bet_lamports = MIN_BET_LAMPORTS;
    
    // Set default durations for small games
    config.small_game_duration_config = GameDurationConfig {
        waiting_phase_duration: DEFAULT_SMALL_GAME_WAITING_DURATION,
    };
    
    
    // Initialize game round in idle state
    game_round.round_id = 0;
    game_round.status = GameStatus::Idle;
    game_round.start_timestamp = 0;
    game_round.players = Vec::new();
    // game_round.finalists = Vec::new(); // Removed for small games MVP
    // game_round.spectator_bets = Vec::new(); // Removed for small games MVP
    game_round.initial_pot = 0;
    // game_round.spectator_pot = 0; // Removed for small games MVP
    game_round.winner = Pubkey::default();
    // game_round.finalist_randomness_account = Pubkey::default(); // Removed for small games MVP
    
    // ORAO VRF fields
    game_round.vrf_request_pubkey = Pubkey::default();
    game_round.vrf_seed = [0u8; 32];
    game_round.randomness_fulfilled = false;
    
    msg!("Domin8 game initialized with authority: {}", ctx.accounts.authority.key());
    
    Ok(())
}
