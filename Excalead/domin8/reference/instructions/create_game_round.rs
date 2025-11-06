use crate::*;
use anchor_lang::prelude::*;
use orao_solana_vrf::{
    cpi::accounts::RequestV2,
    program::OraoVrf,
    state::NetworkState,
    CONFIG_ACCOUNT_SEED,
    RANDOMNESS_ACCOUNT_SEED,
    ID as ORAO_VRF_ID,
};

#[derive(Accounts)]
#[instruction(
    round_id: u64,
    bet_amount: u64,
    skin: u8,
    position: [u16; 2],
)]
pub struct CreateGameRound<'info> {
    #[account(
        mut,
        seeds = [b"domin8_config"],
        bump,
    )]
    pub config: Account<'info, Domin8Config>,

    #[account(
        init,
        space = BASE_GAME_ACCOUNT_SIZE,
        payer = user,
        seeds = [
            b"domin8_game",
            round_id.to_le_bytes().as_ref(),
        ],
        bump,
    )]
    pub game: Box<Account<'info, Domin8Game>>,

    #[account(
        mut,
        seeds = [b"active_game"],
        bump,
    )]
    pub active_game: Box<Account<'info, Domin8Game>>,

    #[account(mut)]
    pub user: Signer<'info>,

    // ---- VRF accounts ----

    /// CHECK: Orao randomness account
    #[account(
        mut,
        seeds = [RANDOMNESS_ACCOUNT_SEED, &config.force],
        bump,
        seeds::program = ORAO_VRF_ID
    )]
    pub vrf_randomness: AccountInfo<'info>,

    /// CHECK: Orao treasury (devnet/mainnet address), used by VRF CPI
    #[account(mut)]
    pub vrf_treasury: AccountInfo<'info>,

    #[account(
        mut,
        seeds = [CONFIG_ACCOUNT_SEED],
        bump,
        seeds::program = ORAO_VRF_ID
    )]
    pub vrf_config: Account<'info, NetworkState>,

    pub vrf_program: Program<'info, OraoVrf>,
    pub system_program: Program<'info, System>,
}

/// Create new game round with first bet (includes skin and position)
///
/// Accounts:
/// 0. `[writable]` config: [Domin8Config] Configuration
/// 1. `[writable]` game: [Domin8Game] Game round account
/// 2. `[writable]` active_game: [Domin8Game] Active game singleton
/// 3. `[writable, signer]` user: [AccountInfo] User creating the game
/// 4-8. VRF accounts
/// 9. `[]` system_program: [AccountInfo] System program
///
/// Data:
/// - round_id: [u64] Round ID for the game
/// - bet_amount: [u64] Initial bet amount
/// - skin: [u8] Character skin ID (0-255)
/// - position: [[u16; 2]] Spawn position [x, y]
pub fn handler(
    ctx: Context<CreateGameRound>,
    round_id: u64,
    bet_amount: u64,
    skin: u8,
    position: [u16; 2],
) -> Result<()> {
    let config = &mut ctx.accounts.config;
    let game = &mut ctx.accounts.game;
    let active_game = &mut ctx.accounts.active_game;
    let user = &ctx.accounts.user;
    let clock = Clock::get()?;

    // Check if system is locked
    require!(!config.lock, Domin8Error::GameLocked);

    // Validate round_id matches the expected next round
    require!(round_id == config.game_round, Domin8Error::GameAlreadyExists);

    // Validate bet amount meets minimum and maximum requirements
    require!(bet_amount >= config.min_deposit_amount, Domin8Error::InsufficientBet);
    require!(bet_amount <= config.max_deposit_amount, Domin8Error::ExcessiveBet);

    // Get force from config for VRF request
    let force = config.force;

    // Request VRF randomness
    let vrf_cpi = CpiContext::new(
        ctx.accounts.vrf_program.to_account_info(),
        RequestV2 {
            payer: user.to_account_info(),
            network_state: ctx.accounts.vrf_config.to_account_info(),
            treasury: ctx.accounts.vrf_treasury.to_account_info(),
            request: ctx.accounts.vrf_randomness.to_account_info(),
            system_program: ctx.accounts.system_program.to_account_info(),
        },
    );
    orao_solana_vrf::cpi::request_v2(vrf_cpi, force)?;

    // Check if user has sufficient funds
    require!(user.lamports() >= bet_amount, Domin8Error::InsufficientFunds);

    // Check if game is already initialized (prevent double initialization)
    if game.game_round != 0 {
        return Err(Domin8Error::GameAlreadyExists.into());
    }

    // Initialize the game
    game.game_round = round_id;
    game.start_date = clock.unix_timestamp;
    game.end_date = clock.unix_timestamp + config.round_time as i64;
    game.total_deposit = bet_amount;
    game.rand = 0; // Will be filled when VRF is ready
    game.winner = None;
    game.winner_prize = 0; // Will be set when game ends
    game.winning_bet_index = None; // Will be set when game ends
    game.user_count = 1;
    game.force = force; // Store as [u8; 32]
    game.status = GAME_STATUS_OPEN;
    game.wallets = Vec::new();
    game.bets = Vec::new();

    // Reset the active game (this will be called for each new game round)
    active_game.game_round = round_id;
    active_game.start_date = clock.unix_timestamp;
    active_game.end_date = clock.unix_timestamp + config.round_time as i64;
    active_game.total_deposit = bet_amount;
    active_game.rand = 0; // Will be filled when VRF is ready
    active_game.winner = None;
    active_game.winner_prize = 0; // Will be set when game ends
    active_game.winning_bet_index = None; // Will be set when game ends
    active_game.user_count = 1;
    active_game.force = force; // Store as [u8; 32]
    active_game.status = GAME_STATUS_OPEN;
    active_game.wallets = Vec::new(); // Initialize empty wallets vector
    active_game.bets = Vec::new();

    // Calculate new space needed for the first bet
    let current_space = game.to_account_info().data_len();
    let new_space = current_space + BET_INFO_SIZE + WALLET_SIZE;

    // Reallocate account to accommodate the first bet
    game.to_account_info().realloc(new_space, false)?;

    // Reallocate active_game to match game size
    let active_game_current_size = active_game.to_account_info().data_len();
    if active_game_current_size != new_space {
        // Calculate rent-exempt minimum for the new size
        let rent = Rent::get()?;
        let active_game_rent_exempt = rent.minimum_balance(new_space);
        let active_game_current_balance = active_game.to_account_info().lamports();

        // Transfer SOL if needed
        if active_game_current_balance < active_game_rent_exempt {
            let needed = active_game_rent_exempt - active_game_current_balance;
            let active_game_transfer = anchor_lang::system_program::Transfer {
                from: user.to_account_info(),
                to: active_game.to_account_info(),
            };

            let active_game_cpi_context = CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                active_game_transfer,
            );

            anchor_lang::system_program::transfer(active_game_cpi_context, needed)?;
            msg!("✓ Transferred {} lamports to active_game for rent", needed);
        }

        // Reallocate active_game to match game size
        active_game.to_account_info().realloc(new_space, false)?;
        msg!("✓ Reallocated active_game from {} to {} bytes", active_game_current_size, new_space);
    }

    // Add the first bet to active_game only (game will be synced in end_game)
    // First, add the user to wallets
    active_game.wallets.push(user.key());

    // Add the first bet with wallet_index 0 (first wallet) INCLUDING skin and position
    active_game.bets.push(BetInfo {
        wallet_index: 0,
        amount: bet_amount,
        skin,
        position,
    });

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

    // Increment the game round counter for next game
    config.game_round += 1;

    // Lock the system to prevent multiple concurrent games
    config.lock = true;

    msg!("Game round {} created by user: {}", round_id, user.key());
    msg!("Initial bet: {} lamports", bet_amount);
    msg!("Character skin: {}", skin);
    msg!("Spawn position: [{}, {}]", position[0], position[1]);
    msg!("Game ends at: {}", game.end_date);
    msg!("VRF force (hex): {}", Utils::bytes_to_hex(&force));
    msg!("Total bets: {}", game.bets.len());
    msg!("Account space: {} bytes", new_space);

    Ok(())
}
