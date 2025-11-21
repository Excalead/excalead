Require Import Excalead.Excalead.

Module Domin8Error.
  Inductive t : Set :=
  | InvalidGameStatus
  | Unauthorized
  | BettingPhaseClosed
  | BetTooSmall
  | MaxPlayersReached
  | PlayerNotFound
  | RandomnessNotResolved
  | InvalidRandomnessAccount
  | CommitSlotNotElapsed
  | NotASpectator
  | FinalistNotFound
  | InsufficientFunds
  | MathOverflow
  | NoWinnerDetermined
  | InvalidGameType
  | NoWinnerSet
  | NoFinalistsSet
  | PayoutExceedsAvailableFunds
  | AlreadyClaimed
  | NoWinningsFound
  | HouseFeeAlreadyCollected
  | GameAlreadyReset
  | InvalidVrfAccount
  | RandomnessNotFulfilled
  | VrfRequestFailed
  | InvalidVrfSeed
  | InvalidWinnerAccount
  | InvalidTreasury
  | NoPlayers
  | InvalidBetAmount
  | ArithmeticOverflow
  .

  Definition to_string (self : Domin8Error.t) : string :=
    match self with
    | InvalidGameStatus => "Invalid game status for this action"
    | Unauthorized => "Unauthorized: only authority can perform this action"
    | BettingPhaseClosed => "Betting phase is closed"
    | BetTooSmall => "Bet amount is below minimum required"
    | MaxPlayersReached => "Maximum number of players reached"
    | PlayerNotFound => "Player not found in current game"
    | RandomnessNotResolved => "Switchboard randomness value is not yet available for the committed slot"
    | InvalidRandomnessAccount => "The provided Switchboard randomness account is not valid for the current game round"
    | CommitSlotNotElapsed => "The committed slot has not elapsed yet"
    | NotASpectator => "A finalist cannot place a spectator bet"
    | FinalistNotFound => "Target finalist not found"
    | InsufficientFunds => "Insufficient funds for bet"
    | MathOverflow => "Mathematical overflow occurred"
    | NoWinnerDetermined => "No winner has been determined yet"
    | InvalidGameType => "Invalid game type for this operation"
    | NoWinnerSet => "No winner has been set"
    | NoFinalistsSet => "No finalists have been set"
    | PayoutExceedsAvailableFunds => "Payout amount exceeds available funds"
    | AlreadyClaimed => "Winnings have already been claimed"
    | NoWinningsFound => "No winnings found for this wallet"
    | HouseFeeAlreadyCollected => "House fee has already been collected"
    | GameAlreadyReset => "Game has already been reset"
    | InvalidVrfAccount => "VRF account is invalid"
    | RandomnessNotFulfilled => "Randomness not yet fulfilled"
    | VrfRequestFailed => "VRF request failed"
    | InvalidVrfSeed => "Invalid VRF seed"
    | InvalidWinnerAccount => "Invalid winner account"
    | InvalidTreasury => "Invalid treasury account"
    | NoPlayers => "No players in game"
    | InvalidBetAmount => "Invalid bet amount"
    | ArithmeticOverflow => "Arithmetic overflow occurred"
    end.
End Domin8Error.
