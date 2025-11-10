use anchor_lang::prelude::*;
use anchor_lang::system_program;
use crate::state::{GameRound, GameStatus, PlayerEntry};
use crate::constants::*;
use crate::errors::Domin8Error;

#[derive(Accounts)]
pub struct DepositBet<'info> {
    #[account(
        mut,
        seeds = [GAME_ROUND_SEED],
        bump
    )]
    pub game_round: Account<'info, GameRound>,
    
    /// CHECK: This is the vault PDA that holds game funds
    #[account(
        mut,
        seeds = [VAULT_SEED],
        bump
    )]
    pub vault: UncheckedAccount<'info>,
    
    #[account(mut)]
    pub player: Signer<'info>,
    
    pub system_program: Program<'info, System>,
}

pub fn deposit_bet(
    ctx: Context<DepositBet>,
    amount: u64,
) -> Result<()> {
    let game_round = &mut ctx.accounts.game_round;
    let player_key = ctx.accounts.player.key();
    let clock = Clock::get()?;
    
    // Validate game state - must be Idle or Waiting
    require!(
        game_round.can_accept_players(),
        Domin8Error::InvalidGameStatus
    );
    
    // Validate bet amount meets minimum requirement
    require!(
        amount >= MIN_BET_LAMPORTS,
        Domin8Error::BetTooSmall
    );
    
    // Check if we've reached maximum players
    require!(
        game_round.players.len() < MAX_PLAYERS,
        Domin8Error::MaxPlayersReached
    );
    
    // Transfer SOL to vault
    system_program::transfer(
        CpiContext::new(
            ctx.accounts.system_program.to_account_info(),
            system_program::Transfer {
                from: ctx.accounts.player.to_account_info(),
                to: ctx.accounts.vault.to_account_info(),
            },
        ),
        amount,
    )?;
    
    // Update game state based on current status
    if game_round.status == GameStatus::Idle {
        // First player - transition to Waiting
        game_round.status = GameStatus::Waiting;
        game_round.start_timestamp = clock.unix_timestamp;
        game_round.initial_pot = amount;
        
        msg!("Game started by first player");
    } else {
        // Add to existing pot
        game_round.initial_pot = game_round.initial_pot.saturating_add(amount);
    }
    
    // Find existing player or add new one
    if let Some(existing_player) = game_round.find_player_mut(&player_key) {
        // Player already exists - add to their bet
        existing_player.total_bet = existing_player.total_bet.saturating_add(amount);
        existing_player.timestamp = clock.unix_timestamp; // Update timestamp
        
        msg!("Updated bet for player: {}, new total: {}", player_key, existing_player.total_bet);
    } else {
        // New player
        let player_entry = PlayerEntry {
            wallet: player_key,
            total_bet: amount,
            timestamp: clock.unix_timestamp,
        };
        
        game_round.players.push(player_entry);
        
        msg!("New player joined: {}, bet: {}, total players: {}", 
             player_key, amount, game_round.players.len());
    }
    
    msg!("Total pot: {} lamports", game_round.initial_pot);
    
    Ok(())
}