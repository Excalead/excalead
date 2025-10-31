Require Import Excalead.Excalead.
Require Import Excalead.example.model.constants.
Require Import Excalead.example.model.state.config.
Require Import Excalead.example.model.state.game.

Module BetAccounts.
  Record t : Set := {
    config : Domin8Config.t;
    game : Domin8Game.t;
    active_game : Domin8Game.t;
    user : Signer.t;
    system_program : System.t;
  }.
End BetAccounts.

Definition handler
    (ctx : Context.t BetAccounts.t)
    (round_id : u64)
    (bet_amount : u64)
    (skin : u8)
    (position : u16 * u16) :
    Result.t unit :=
  let config := ctx.(Context.accounts).(BetAccounts.config) in
  let game := ctx.(Context.accounts).(BetAccounts.game) in
  let active_game := ctx.(Context.accounts).(BetAccounts.active_game) in
  let user := ctx.(Context.accounts).(BetAccounts.user) in
  let? clock := Clock.get in

  require! game.(Domin8Game.game_round) =? round_id with "Game not open" in

  require! game.(Domin8Game.status) =? GAME_STATUS_OPEN with "Game not open" in

  require! clock.(Clock.unix_timestamp) <? game.(Domin8Game.end_date) with "Game expired" in

  require! bet_amount >=? config.(Domin8Config.min_deposit_amount) with "Insufficient bet amount" in
  require! bet_amount <=? config.(Domin8Config.max_deposit_amount) with "Excessive bet amount" in

  require! Signer.lamports user >=? bet_amount with "Insufficient funds" in

  require! Z.of_nat (List.length active_game.(Domin8Game.bets)) <? MAX_BETS_PER_GAME
    with "Maximum bets per game exceeded" in

  (* let? transfer_instruction := Transfer.create(user.to_account_info, game.to_account_info) in
  let? cpi_context := CpiContext.new(system_program.to_account_info, transfer_instruction) in
  let? transfer_result := System.transfer(cpi_context, bet_amount) in *)

  (* let? wallet_index := active_game.wallets.iter.position(|&wallet| wallet = user.key) in
  let? wallet_index := active_game.wallets.iter.position(|&wallet| wallet = user.key) in *)

  (* TODO *)
  let wallet_index := 0 in

  let user_bet_count := List.length (List.filter
    (fun bet => bet.(BetInfo.wallet_index) =? wallet_index)
    active_game.(Domin8Game.bets)
  ) in

  Result.Ok tt.
