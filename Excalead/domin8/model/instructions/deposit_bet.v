Require Import Excalead.Excalead.

From Excalead.domin8.model Require Import state.mod errors constants.

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
  (* #[derive(Accounts)] *)
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
    Result.t GameRound.t :=
  let game_round := ctx.(Context.accounts).(DepositBet.game_round) in
  let player_key := key ctx.(Context.accounts).(DepositBet.player) in
  let? clock := Clock.get in

  require!
    GameRound.can_accept_players game_round with
    "Invalid game status" in

  require!
    amount >=? MIN_BET_LAMPORTS with
    "Bet too small" in

  require!
    Z.of_nat (List.length game_round.(GameRound.players)) <? MAX_PLAYERS with
    "Max Players Reached" in

  let? _ :=
    (* // Transfer SOL to vault *)
    SystemProgram.transfer
      (Context.new
        (to_account_info ctx.(Context.accounts).(DepositBet.system_program))
        ({| SystemProgram.Transfer.from :=
              to_account_info ctx.(Context.accounts).(DepositBet.player);
            SystemProgram.Transfer.to :=
              to_account_info ctx.(Context.accounts).(DepositBet.vault);
        |}))
      amount
  in

  (* // Update game state based on current status *)
  let game_round :=
    match game_round.(GameRound.status) with
    | GameStatus.Idle =>
      (* // First player - transition to Waiting *)
      game_round
        <| GameRound.status := GameStatus.Waiting |>
        <| GameRound.start_timestamp := clock.(Clock.unix_timestamp) |>
        <| GameRound.initial_pot := amount  |>
      (* msg!("Game started by first player"); *)
    | _ =>
      (* // Add to existing pot *)
      game_round
        <| GameRound.initial_pot :=
            game_round.(GameRound.initial_pot) + amount |>
    end in

    (* // Find existing player or add new one *)
    let game_round :=
      match GameRound.find_player_mut game_round player_key with
      | Some handle =>
        handle (fun existing_player => {|
            (* // Player already exists - add to their bet *)
            PlayerEntry.wallet := existing_player.(PlayerEntry.wallet);
            PlayerEntry.total_bet :=
              existing_player.(PlayerEntry.total_bet) + amount;
            PlayerEntry.timestamp := clock.(Clock.unix_timestamp)
          |}
          (* msg!("Updated bet for player: {}, new total: {}", player_key, existing_player.total_bet); *)
          )
      | None =>
        (* // New player *)
        let player_entry := {|
          PlayerEntry.wallet := player_key;
          PlayerEntry.total_bet := amount;
          PlayerEntry.timestamp := clock.(Clock.unix_timestamp)
        |} in
        game_round <|
          GameRound.players := player_entry :: game_round.(GameRound.players)
        |>
        (* msg!("New player joined: {}, bet: {}, total players: {}",  *)
        (*      player_key, amount, game_round.players.len()); *)
      end in

    (* msg!("Total pot: {} lamports", game_round.initial_pot); *)

  Result.Ok game_round.
