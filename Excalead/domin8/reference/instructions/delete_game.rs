use crate::*;
use anchor_lang::prelude::*;

#[derive(Accounts)]
#[instruction(
    round_id: u64,
)]
pub struct DeleteGame<'info> {
    #[account(
        seeds = [b"domin8_config"],
        bump,
    )]
    pub config: Account<'info, Domin8Config>,

    #[account(
        mut,
        close = admin,
        seeds = [
            b"domin8_game",
            round_id.to_le_bytes().as_ref(),
        ],
        bump,
    )]
    pub game: Box<Account<'info, Domin8Game>>,

    #[account(mut)]
    pub admin: Signer<'info>,
}

/// Delete a game round from the blockchain (admin only)
///
/// Accounts:
/// 0. `[]` config: [Domin8Config] Configuration
/// 1. `[writable]` game: [Domin8Game] Game round to delete
/// 2. `[writable, signer]` admin: [AccountInfo] Administrator account
///
/// Data:
/// - round_id: [u64] Round ID for the game to delete
pub fn handler(
    ctx: Context<DeleteGame>,
    round_id: u64,
) -> Result<()> {
    let config = &ctx.accounts.config;
    let game = &ctx.accounts.game;
    let admin = &ctx.accounts.admin;

    // Verify admin authorization
    require!(admin.key() == config.admin, Domin8Error::Unauthorized);

    // Check if game exists and is the correct round
    require!(game.game_round == round_id, Domin8Error::GameNotOpen);

    // Only allow deletion of closed games (status = 1) or expired games
    let clock = Clock::get()?;
    let is_closed = game.status == GAME_STATUS_CLOSED;
    let is_expired = clock.unix_timestamp > game.end_date + 86400; // 24 hours after end

    require!(is_closed || is_expired, Domin8Error::InvalidGameStatus);

    // If game has significant funds remaining, it should have been properly ended first
    let current_balance = ctx.accounts.game.to_account_info().lamports();
    let rent = Rent::get()?;
    let rent_exempt_minimum = rent.minimum_balance(ctx.accounts.game.to_account_info().data_len());
    let significant_funds_remaining = current_balance > rent_exempt_minimum + 1000; // 1000 lamports buffer

    if significant_funds_remaining && !is_expired {
        return Err(Domin8Error::InvalidGameStatus.into());
    }

    msg!("Game round {} deleted by admin", round_id);
    msg!("Game status was: {}", game.status);
    msg!("Remaining deposit: {} lamports", game.total_deposit);

    // The account will be automatically closed due to the close constraint
    // and remaining lamports will be transferred to the admin

    Ok(())
}
