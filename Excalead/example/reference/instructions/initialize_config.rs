use crate::*;
use anchor_lang::prelude::*;

#[derive(Accounts)]
pub struct InitializeConfig<'info> {
    #[account(
        init,
        space = 8 + 32 + 32 + 8 + 8 + 8 + 8 + 8 + 1 + 32, // discriminator + admin + treasury + game_round + house_fee + min/max deposits + round_time + lock + force
        payer = admin,
        seeds = [b"domin8_config"],
        bump,
    )]
    pub config: Account<'info, Domin8Config>,

    #[account(
        init,
        space = BASE_GAME_ACCOUNT_SIZE,
        payer = admin,
        seeds = [b"active_game"],
        bump,
    )]
    pub active_game: Box<Account<'info, Domin8Game>>,

    #[account(mut)]
    pub admin: Signer<'info>,

    pub system_program: Program<'info, System>,
}

/// Initialize global domin8 configuration (admin only)
///
/// Accounts:
/// 0. `[writable]` config: [Domin8Config] Configuration account
/// 1. `[writable]` active_game: [Domin8Game] Active game singleton
/// 2. `[writable, signer]` admin: [AccountInfo] Administrator account
/// 3. `[]` system_program: [AccountInfo] Auto-generated, for account initialization
///
/// Data:
/// - treasury: [Pubkey] Treasury wallet for house fees
/// - house_fee: [u64] House fee in basis points
/// - min_deposit_amount: [u64] Minimum deposit amount
/// - max_deposit_amount: [u64] Maximum deposit amount
/// - round_time: [u64] Round duration in seconds
pub fn handler(
    ctx: Context<InitializeConfig>,
    treasury: Pubkey,
    house_fee: u64,
    min_deposit_amount: u64,
    max_deposit_amount: u64,
    round_time: u64,
) -> Result<()> {
    let config = &mut ctx.accounts.config;
    let active_game = &mut ctx.accounts.active_game;
    let clock = Clock::get()?;

    // Validate inputs
    require!(house_fee <= MAX_HOUSE_FEE, Domin8Error::FeeTooHigh);
    require!(
        round_time >= MIN_ROUND_TIME && round_time <= MAX_ROUND_TIME,
        Domin8Error::InvalidRoundTime
    );
    require!(
        min_deposit_amount >= MIN_DEPOSIT_AMOUNT,
        Domin8Error::InsufficientBet
    );

    // Initialize configuration
    config.admin = ctx.accounts.admin.key();
    config.treasury = treasury;
    config.game_round = 1; // Start from round 1
    config.house_fee = house_fee;
    config.min_deposit_amount = min_deposit_amount;
    config.max_deposit_amount = max_deposit_amount;
    config.round_time = round_time;
    config.lock = false;

    // Generate initial VRF force seed
    let mut initial_force = [0u8; 32];
    use anchor_lang::solana_program::keccak::hashv;
    let hash = hashv(&[
        &config.game_round.to_le_bytes(),
        &clock.unix_timestamp.to_le_bytes(),
        &clock.slot.to_le_bytes(),
        ctx.accounts.admin.key().as_ref(),
    ]);
    initial_force.copy_from_slice(&hash.0);
    config.force = initial_force;

    // Initialize active_game as empty
    active_game.game_round = 0; // No active game yet
    active_game.start_date = 0;
    active_game.end_date = 0;
    active_game.total_deposit = 0;
    active_game.rand = 0;
    active_game.user_count = 0;
    active_game.force = [0u8; 32];
    active_game.status = GAME_STATUS_CLOSED;
    active_game.winner = None;
    active_game.winner_prize = 0;
    active_game.winning_bet_index = None;
    active_game.wallets = Vec::new();
    active_game.bets = Vec::new();

    msg!("Domin8 configuration initialized");
    msg!("Admin: {}", config.admin);
    msg!("Treasury: {}", config.treasury);
    msg!("House fee: {}% ({}bps)", Utils::bps_to_percentage(house_fee), house_fee);
    msg!("Bet range: {}-{} lamports", min_deposit_amount, max_deposit_amount);
    msg!("Round time: {}s", round_time);
    msg!("Initial VRF force: {:?}", &initial_force[0..16]);

    Ok(())
}
