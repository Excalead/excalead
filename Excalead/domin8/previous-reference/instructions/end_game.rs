use crate::*;
use anchor_lang::prelude::*;
use orao_solana_vrf::{
    state::RandomnessAccountData,
    RANDOMNESS_ACCOUNT_SEED,
    ID as ORAO_VRF_ID,
};

#[derive(Accounts)]
#[instruction(
    round_id: u64,
)]
pub struct EndGame<'info> {
    #[account(
        mut,
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

    #[account(
        mut,
        seeds = [b"active_game"],
        bump,
    )]
    pub active_game: Box<Account<'info, Domin8Game>>,

    #[account(mut)]
    pub admin: Signer<'info>,

    #[account(mut)]
    /// CHECK: Treasury wallet
    pub treasury: UncheckedAccount<'info>,

    /// CHECK: Must equal PDA of (RANDOMNESS_ACCOUNT_SEED, open_request.force) for ORAO_VRF_ID
    #[account(
        seeds = [RANDOMNESS_ACCOUNT_SEED, &game.force],
        bump,
        seeds::program = ORAO_VRF_ID
    )]
    pub vrf_randomness: AccountInfo<'info>,

    pub system_program: Program<'info, System>,
}

/// End game, draw winner, and distribute prizes (admin only)
///
/// Accounts:
/// 0. `[writable]` config: [Domin8Config] Configuration
/// 1. `[writable]` game: [Domin8Game] Game round to end
/// 2. `[writable]` active_game: [Domin8Game] Active game singleton
/// 3. `[writable, signer]` admin: [AccountInfo] Administrator account
/// 4. `[writable]` treasury: [AccountInfo] Treasury wallet for fees
/// 5. `[]` vrf_randomness: [AccountInfo] Orao VRF randomness account
/// 6. `[]` system_program: [AccountInfo] System program
///
/// Data:
/// - round_id: [u64] Round ID for the game
pub fn handler(
    ctx: Context<EndGame>,
    round_id: u64,
) -> Result<()> {
    let admin = &ctx.accounts.admin;
    let treasury = &ctx.accounts.treasury;
    let clock = Clock::get()?;

    // First, do all validations without mutable borrows
    let game_data = &ctx.accounts.game;
    let active_game_data = &ctx.accounts.active_game;
    let config_data = &ctx.accounts.config;

    // Verify admin authorization
    require!(admin.key() == config_data.admin, Domin8Error::Unauthorized);

    // Check if game exists and is the correct round
    require!(game_data.game_round == round_id, Domin8Error::GameNotOpen);

    // Check if game is still open (status = 0)
    require!(game_data.status == GAME_STATUS_OPEN, Domin8Error::InvalidGameStatus);

    // Check if game has ended (current time > end_date)
    require!(clock.unix_timestamp >= game_data.end_date, Domin8Error::GameNotEnded);

    // Verify treasury address matches config
    require!(treasury.key() == config_data.treasury, Domin8Error::Unauthorized);

    // Ensure there are bets to process
    require!(!active_game_data.bets.is_empty(), Domin8Error::NoBets);

    // Get VRF randomness from Orao VRF
    let mut data = &ctx.accounts.vrf_randomness.try_borrow_data()?[..];
    let vrf_state = RandomnessAccountData::try_deserialize(&mut data)
        .map_err(|_| Domin8Error::RandomnessNotReady)?;

    // Pull the randomness (32 bytes) if fulfilled
    let rnd32 = vrf_state
        .fulfilled_randomness()
        .ok_or(Domin8Error::RandomnessNotReady)?;

    // Use first 8 bytes as u64
    let randomness = u64::from_le_bytes(rnd32[0..8].try_into().unwrap());
    msg!("VRF randomness (u64): {}", randomness);

    // Select winner using weighted random selection based on bet amounts
    let (selected_winner, winning_bet_index) = Utils::select_winner_by_weight(
        randomness,
        &active_game_data.bets,
        &active_game_data.wallets,
        active_game_data.total_deposit
    )?;

    // Calculate prize distribution from the FULL POT
    let total_pot = game_data.total_deposit;
    require!(total_pot > 0, Domin8Error::ArithmeticError);

    // Minimal logging to save CU
    msg!("Game {} ended: winner={}, pot={}", round_id, selected_winner, total_pot);

    // Calculate house fee
    let house_fee_amount = Utils::calculate_fee(total_pot, config_data.house_fee)?;

    // Winner gets the remaining amount after fees are deducted
    let winner_prize = total_pot
        .checked_sub(house_fee_amount)
        .ok_or(Domin8Error::ArithmeticError)?;

    // Validate that we have enough funds to cover all distributions
    require!(house_fee_amount <= total_pot, Domin8Error::ArithmeticError);

    // Minimal fee logging
    msg!("House fee: {}, Winner prize: {}", house_fee_amount, winner_prize);

    // Calculate rent-exempt minimum for the game account
    let rent = Rent::get()?;
    let game_account_size = ctx.accounts.game.to_account_info().data_len();
    let rent_exempt_minimum = rent.minimum_balance(game_account_size);
    let current_balance = ctx.accounts.game.to_account_info().lamports();

    // Transfer house fee
    if house_fee_amount > 0 {
        let max_transferable = current_balance.saturating_sub(rent_exempt_minimum);
        let actual_house_fee = house_fee_amount.min(max_transferable);

        if actual_house_fee > 0 {
            **ctx.accounts.game.to_account_info().try_borrow_mut_lamports()? -= actual_house_fee;
            **ctx.accounts.treasury.to_account_info().try_borrow_mut_lamports()? += actual_house_fee;
        }
    }

    // Now do all mutable updates after transfers are complete
    let game = &mut ctx.accounts.game;
    let active_game = &mut ctx.accounts.active_game;
    let config = &mut ctx.accounts.config;

    // Transfer data from active_game to game without cloning (memory-efficient)
    game.wallets = std::mem::take(&mut active_game.wallets);
    game.bets = std::mem::take(&mut active_game.bets);
    game.total_deposit = active_game.total_deposit;
    game.user_count = active_game.user_count;

    // Store winner prize amount in game state for later claiming
    game.winner_prize = winner_prize;
    game.rand = randomness;
    game.winner = Some(selected_winner);
    game.winning_bet_index = Some(winning_bet_index as u64);

    // Close the game
    game.status = GAME_STATUS_CLOSED;

    // Update active_game to match the game state
    active_game.winner_prize = winner_prize;
    active_game.rand = randomness;
    active_game.winner = Some(selected_winner);
    active_game.winning_bet_index = Some(winning_bet_index as u64);
    active_game.status = GAME_STATUS_CLOSED;

    // Generate new VRF force seed for next game (using current randomness + game data)
    let mut new_force = [0u8; 32];
    let randomness_bytes = randomness.to_le_bytes();
    let round_id_bytes = round_id.to_le_bytes();
    let total_pot_bytes = total_pot.to_le_bytes();

    // Combine randomness, round_id, and total_pot to create new force seed
    for i in 0..32 {
        new_force[i] = randomness_bytes[i % 8]
            ^ round_id_bytes[i % 8]
            ^ total_pot_bytes[i % 8]
            ^ (i as u8);
    }

    // Update config with new force for next game
    config.force = new_force;

    // Minimal completion logging
    msg!("Game {} completed", round_id);

    // Unlock the system to allow new game creation
    config.lock = false;

    Ok(())
}
