Require Import Excalead.Excalead.

From Exalead.example.model Require Import state.mod errors.

(*
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
*)
Module DepositBet.
  Record t : Set := {
    game_round: GameRound.t;
    vault: UncheckedAccount.t;
    player: Signer.t;
    system_program: System.t;
  }.
End DepositBet.

Definition deposit_bet
    (ctx : Context.t DepositBet.t)
    (amount: u64) :
    Resylt.t unit :=
  let game_round := ctx.(Context.accounts).(DepositBet.game_round) in
  let player := Signer.key ctx.(Context.accounts).(DepositBet.player) in
  let? clock := Clock.get in

  require!
    game_round.(GameRound.can_accept_players) () with
    "Invalid game status" in

  require!
    amound >=? MIN_BET_LAMPORTS with
    "Bet too small" in

  require!
    Z.of_nat (List.length game_round.(GameRound.players)) <? MAX_PLAYERS with
    "Max Players Reached" in

  (* // Transfer SOL to vault
  system_program::transfer(
      CpiContext::new(
          ctx.accounts.system_program.to_account_info(),
          system_program::Transfer {
              from: ctx.accounts.player.to_account_info(),
              to: ctx.accounts.vault.to_account_info(),
          },
      ),
      amount,
  )?; *)

  (* // Update game state based on current status
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
   *)

  Result.Ok tt.
