(* LICENSE *)

(* open Domin8 *)
open Yojson
open String

module Result = Domin8.Result

module GameRound = struct
  include Domin8.Game_round.GameRound

  let to_json (game_round : t) : Safe.t = failwith "Unimplemented"
  let from_json (json : Safe.t) : t = failwith "Unimplemented"
end

module DepositBet = struct
  include Domin8.Deposit_bet.DepositBet

  let from_json (json : Safe.t) : t = failwith "Unimplemented"
end

let string_of_char_list (lst : char list) : string =
  String.of_seq (List.to_seq lst)


let test_deposit_bet (input_ctx : Safe.t) (input_amount : int) : Safe.t =
      (* Domin8.Game_round.GameRound.t Domin8.Result.t = *)
  let ctx = DepositBet.from_json input_ctx in
  match Domin8.Deposit_bet.deposit_bet ctx input_amount with
  | Result.Ok game_round ->
    GameRound.to_json game_round
  | Result.Err str ->
    failwith ("deposit_bet Error: "^string_of_char_list str)

