use crate::*;
use anchor_lang::prelude::*;

#[derive(Accounts)]
#[instruction(
    round_id: u64,
)]
pub struct SendPrizeWinner<'info> {
    #[account(
        seeds = [b"domin8_config"],
        bump,
    )]
    pub config: Account<'info, Domin8Config>,

    #[account(
        mut,
        seeds = [
            b"domin8_game",
            round_id.to_le_bytes().as_ref(),
        ],
        bump,
    )]
    pub game: Box<Account<'info, Domin8Game>>,

    #[account(mut)]
    pub claimer: Signer<'info>,

    /// CHECK: Winner account that will receive the prize. Validated against game.winner
    #[account(mut)]
    pub winner: AccountInfo<'info>,

    pub system_program: Program<'info, System>,
}

/// Send prize to the winner of a completed game
///
/// Accounts:
/// 0. `[]` config: [Domin8Config] Configuration account
/// 1. `[writable]` game: [Domin8Game] Game round to send prize from
/// 2. `[writable, signer]` claimer: [AccountInfo] Admin or winner initiating the claim
/// 3. `[writable]` winner: [AccountInfo] Winner account that receives the prize
/// 4. `[]` system_program: [AccountInfo] System program
///
/// Data:
/// - round_id: [u64] Round ID for the game
pub fn handler(
    ctx: Context<SendPrizeWinner>,
    round_id: u64,
) -> Result<()> {
    let claimer = &ctx.accounts.claimer;
    let winner = &ctx.accounts.winner;
    let admin = ctx.accounts.config.admin;

    // First, get the prize amount and verify everything without mutable borrow
    let game_data = &ctx.accounts.game;
    require!(game_data.game_round == round_id, Domin8Error::GameNotOpen);
    require!(game_data.status == GAME_STATUS_CLOSED, Domin8Error::InvalidGameStatus);
    require!(game_data.winner.is_some(), Domin8Error::NoWinnerFound);

    // Verify that the winner account matches the game's winner
    let winner_pubkey = game_data.winner.unwrap();
    require!(winner.key() == winner_pubkey, Domin8Error::InvalidWinner);

    // Allow either the winner OR the admin to initiate the claim
    let is_winner = claimer.key() == winner_pubkey;
    let is_admin = claimer.key() == admin;
    require!(is_winner || is_admin, Domin8Error::Unauthorized);

    require!(game_data.winner_prize > 0, Domin8Error::ArithmeticError);

    let prize_amount = game_data.winner_prize;

    // Calculate rent-exempt minimum for the game account
    let rent = Rent::get()?;
    let game_account_size = ctx.accounts.game.to_account_info().data_len();
    let rent_exempt_minimum = rent.minimum_balance(game_account_size);

    // Get current game account balance
    let current_balance = ctx.accounts.game.to_account_info().lamports();

    // Calculate maximum transferable amount (leave rent-exempt minimum)
    let max_transferable = current_balance.saturating_sub(rent_exempt_minimum);
    let actual_transfer = prize_amount.min(max_transferable);

    require!(actual_transfer > 0, Domin8Error::ArithmeticError);

    // Transfer prize to the winner
    **ctx.accounts.game.to_account_info().try_borrow_mut_lamports()? -= actual_transfer;
    **ctx.accounts.winner.try_borrow_mut_lamports()? += actual_transfer;

    msg!("✓ Prize transferred: {} lamports to {}", actual_transfer, winner.key());
    msg!("✓ Claimed by: {} (is_winner: {}, is_admin: {})", claimer.key(), is_winner, is_admin);

    // Now update the game state (mutable borrow after transfer is done)
    let game = &mut ctx.accounts.game;
    game.winner_prize = 0;

    msg!("✓ Prize sent to winner: {} lamports for round {}", prize_amount, round_id);

    Ok(())
}
