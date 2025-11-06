use crate::*;
use anchor_lang::prelude::*;

#[derive(Accounts)]
#[instruction(
    round_id: u64,
    bet_amount: u64,
    skin: u8,
    position: [u16; 2],
)]
pub struct Bet<'info> {
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
        realloc = game.to_account_info().data_len() + (BET_INFO_SIZE + WALLET_SIZE) * 1,
        realloc::payer = user,
        realloc::zero = false,
    )]
    pub game: Box<Account<'info, Domin8Game>>,

    #[account(
        mut,
        seeds = [b"active_game"],
        bump,
        realloc = active_game.to_account_info().data_len() + (BET_INFO_SIZE + WALLET_SIZE) * 1,
        realloc::payer = user,
        realloc::zero = false,
    )]
    pub active_game: Box<Account<'info, Domin8Game>>,

    #[account(mut)]
    pub user: Signer<'info>,

    pub system_program: Program<'info, System>,
}

/// Place a bet in the current game round (includes skin and position)
///
/// Accounts:
/// 0. `[]` config: [Domin8Config] Configuration
/// 1. `[writable]` game: [Domin8Game] Game round to bet in
/// 2. `[writable]` active_game: [Domin8Game] Active game singleton
/// 3. `[writable, signer]` user: [AccountInfo] User placing the bet
/// 4. `[]` system_program: [AccountInfo] System program
///
/// Data:
/// - round_id: [u64] Round ID for the game
/// - bet_amount: [u64] Bet amount in lamports
/// - skin: [u8] Character skin ID (0-255)
/// - position: [[u16; 2]] Spawn position [x, y]
pub fn handler(
    ctx: Context<Bet>,
    round_id: u64,
    bet_amount: u64,
    skin: u8,
    position: [u16; 2],
) -> Result<()> {
    let config = &ctx.accounts.config;
    let game = &mut ctx.accounts.game;
    let active_game = &mut ctx.accounts.active_game;
    let user = &ctx.accounts.user;
    let clock = Clock::get()?;

    // Check if game exists and is the correct round
    require!(game.game_round == round_id, Domin8Error::GameNotOpen);

    // Check if game is still open (status = 0)
    require!(game.status == GAME_STATUS_OPEN, Domin8Error::GameNotOpen);

    // Check if game hasn't expired
    require!(clock.unix_timestamp < game.end_date, Domin8Error::GameExpired);

    // Validate bet amount meets minimum and maximum requirements
    require!(bet_amount >= config.min_deposit_amount, Domin8Error::InsufficientBet);
    require!(bet_amount <= config.max_deposit_amount, Domin8Error::ExcessiveBet);

    // Check if user has sufficient funds
    require!(user.lamports() >= bet_amount, Domin8Error::InsufficientFunds);

    // Check if we haven't exceeded maximum bets (prevent account size issues)
    require!(active_game.bets.len() < MAX_BETS_PER_GAME, Domin8Error::ArithmeticError);

    // Transfer SOL from user to game PDA
    let transfer_instruction = anchor_lang::system_program::Transfer {
        from: user.to_account_info(),
        to: game.to_account_info(),
    };

    let cpi_context = CpiContext::new(
        ctx.accounts.system_program.to_account_info(),
        transfer_instruction,
    );

    anchor_lang::system_program::transfer(cpi_context, bet_amount)?;

    // Optimized wallet lookup - check if user is already in wallets
    let wallet_index = if let Some(index) = active_game.wallets.iter().position(|&wallet| wallet == user.key()) {
        index as u16
    } else {
        // New user - add to wallets and increment user_count
        active_game.wallets.push(user.key());
        active_game.user_count = active_game.user_count
            .checked_add(1)
            .ok_or(Domin8Error::ArithmeticError)?;
        (active_game.wallets.len() - 1) as u16
    };

    // Check if user has exceeded maximum bets per game based on bet amount
    let user_bet_count = active_game.bets.iter()
        .filter(|bet| bet.wallet_index == wallet_index)
        .count();

    // Apply different limits based on bet amount
    if bet_amount < SMALL_BET_THRESHOLD {
        // For bets under 0.01 SOL, limit to 20 bets
        require!(user_bet_count < MAX_BETS_PER_USER_SMALL, Domin8Error::UserBetLimitExceeded);
    } else {
        // For bets >= 0.01 SOL, allow up to 30 bets
        require!(user_bet_count < MAX_BETS_PER_USER_LARGE, Domin8Error::UserBetLimitExceeded);
    }

    // Add the bet to active_game.bets (only update active_game, not game) WITH skin and position
    active_game.bets.push(BetInfo {
        wallet_index,
        amount: bet_amount,
        skin,
        position,
    });

    // Update active_game total_deposit
    active_game.total_deposit = active_game.total_deposit
        .checked_add(bet_amount)
        .ok_or(Domin8Error::ArithmeticError)?;

    // Update game state (all attributes EXCEPT bets)
    game.total_deposit = active_game.total_deposit;
    game.user_count = active_game.user_count;

    msg!("Bet placed: {} lamports", bet_amount);
    msg!("Character skin: {}", skin);
    msg!("Spawn position: [{}, {}]", position[0], position[1]);
    msg!("Total bets: {}", active_game.bets.len());
    msg!("Total pot: {} lamports", active_game.total_deposit);

    Ok(())
}
