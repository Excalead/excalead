From Excalead Require Import Excalead Vector Anchor_lang.

Require Import Coq.Lists.List.

Require Import player_entry.
Require Import domin8.constants.

(*
/// Game status enumeration
#[derive(AnchorSerialize, AnchorDeserialize, Clone, PartialEq, Debug)]
pub enum GameStatus {
    Idle,                        // Waiting for first player
    Waiting,                     // Accepting bets
    AwaitingWinnerRandomness,   // Waiting for Switchboard VRF for winner selection
    Finished,                    // Game concluded, winner selected
}
*)
Module GameStatus.
  Inductive t : Set :=
    | Idle
    | Waiting
    | AwaitingWinnerRandomness
    | Finished
  .
  (*
  pub const LEN: usize = 1; // Enum is 1 byte
  *)
  Definition LEN: usize := 1.

  #[export]
  Instance GameStatus_JEncode : JEncode GameStatus.t :=
    fun x => match x with
    | Idle => encode "Idle"
    | Waiting => encode "Waiting"
    | AwaitingWinnerRandomness => encode "AwaitWinnerRandomness"
    | Finished => encode "Finished"
    end.

  #[export]
  Instance GameStatus_JDecode : JDecode GameStatus.t :=
    fun j => match decode j with
      | inr "Idle" => inr Idle
      | inr "Waiting" => inr Waiting
      | inr "AwaitingWinnerRandomness" => inr AwaitingWinnerRandomness
      | inr "Finished" => inr Finished
      | _ => inl "Failed to decode GameStatus"
      end.
End GameStatus.
Export (hints) GameStatus.


(*
/// Current game round state stored as singleton PDA
/// Seeds: [b"game_round"]
#[account]
pub struct GameRound {
    pub round_id: u64,
    pub status: GameStatus,
    pub start_timestamp: i64,

    // Players (max 64)
    pub players: Vec<PlayerEntry>,


    // Pot tracking
    pub initial_pot: u64,
    // pub spectator_pot: u64,  // Removed for small games MVP

    // Winner
    pub winner: Pubkey,

    // ORAO VRF integration
    pub vrf_request_pubkey: Pubkey,    // ORAO VRF request account
    pub vrf_seed: [u8; 32],           // Seed used for VRF request
    pub randomness_fulfilled: bool,    // Track if randomness is ready
}
*)
Module GameRound.
  Record t : Set := {
    round_id: u64;
    status: GameStatus.t;
    start_timestamp: i64;
    players: list PlayerEntry.t;
    initial_pot: u64;
    winner: Pubkey.t;
    vrf_request_pubkey: Pubkey.t;
    vrf_seed: Hash.t;
    randomness_fulfielled: bool;
  }.

  #[export]
  Instance GameRound_JEncode : JEncode GameRound.t :=
    fun x =>
    JSON__Object [
      ("round_id", encode x.(round_id));
      ("status", encode x.(status));
      ("start_timestamp", encode x.(start_timestamp));
      ("players", encode x.(players));
      ("initial_pot", encode x.(initial_pot));
      ("winner", encode x.(winner));
      ("vrf_request_pubkey", encode x.(vrf_request_pubkey));
      ("vrf_seed", encode x.(vrf_seed));
      ("randomness_fulfielled", encode x.(randomness_fulfielled))
    ].

  #[export]
  Instance GameRound_JDecode : JDecode GameRound.t :=
    fun j => match j with
    | JSON__Object [
        ("round_id", round_id_json);
        ("status", status_json);
        ("start_timestamp", start_timestamp_json);
        ("players", players_json);
        ("initial_pot", initial_pot_json);
        ("winner", winner_json);
        ("vrf_request_pubkey", vrf_request_pubkey_json);
        ("vrf_seed", vrf_seed_json);
        ("randomness_fulfielled", randomness_fulfielled_json) ] =>
      decode round_id_json >>= fun round_id =>
      decode status_json >>= fun status =>
      decode start_timestamp_json >>= fun start_timestamp =>
      decode__list players_json >>= fun players =>
      decode initial_pot_json >>= fun initial_pot =>
      decode winner_json >>= fun winner =>
      decode vrf_request_pubkey_json >>= fun vrf_request_pubkey =>
      decode vrf_seed_json >>= fun vrf_seed =>
      decode randomness_fulfielled_json >>= fun randomness_fulfielled =>
      inr {| round_id := round_id;
             status := status;
             start_timestamp := start_timestamp;
             players := players;
             initial_pot := initial_pot;
             winner := winner;
             vrf_request_pubkey := vrf_request_pubkey;
             vrf_seed := vrf_seed;
             randomness_fulfielled := randomness_fulfielled |}
    | _ => inl "Failed to decode GameRound"
    end.



  Module Valid.
    Record t (self : GameRound.t) : Prop := {
      players_len : Z.of_nat (List.length self.(players)) <= MAX_PLAYERS;
    }.
  End Valid.

  (*
  /// Account space calculation for small games MVP with ORAO VRF:
  /// 8 (discriminator) + 8 (round_id) + 1 (status) + 8 (start_timestamp)
  /// + 4 (players vec len) + (64 * 48) (max players)
  /// + 8 (initial_pot) + 32 (winner) 
  /// + 32 (vrf_request_pubkey) + 32 (vrf_seed) + 1 (randomness_fulfilled)
  /// = 8 + 8 + 1 + 8 + 4 + 3072 + 8 + 32 + 32 + 32 + 1 = 3206 bytes (~3.1KB)
  pub const LEN: usize = 8 + 8 + GameStatus::LEN + 8 + 4 + (64 * PlayerEntry::LEN) + 8 + 32 + 32 + 32 + 1;
  *)
  Definition LEN: usize := 8 + 8 + GameStatus.LEN + 8 + 4 + (64 * PlayerEntry.LEN) + 8 + 32 + 32 + 32 + 1.

  (*
  /// Check if the game is in a state where players can join
  pub fn can_accept_players(&self) -> bool {
      matches!(self.status, GameStatus::Idle | GameStatus::Waiting)
  }
  *)
  Definition can_accept_players (self: GameRound.t) : bool :=
    match self.(GameRound.status) with
    | GameStatus.Idle | GameStatus.Waiting => true
    | _ => false
    end.
  (*
  /// Check if the game is a small game (2+ players) - all games are small games in MVP
  pub fn is_small_game(&self) -> bool {
      self.players.len() >= 2
  }
  *)
  Definition is_small_game (self: GameRound.t) : bool :=
    Z.of_nat (List.length self.(GameRound.players)) >=? 2.

  (*
  /// Get player by wallet address
  pub fn find_player(&self, wallet: &Pubkey) -> Option<&PlayerEntry> {
      self.players.iter().find(|p| p.wallet == *wallet)
  }
  *)
  Definition find_player
      (self: GameRound.t)
      (wallet: Pubkey.t) :
      option PlayerEntry.t :=
    List.find
      (fun (p : PlayerEntry.t) => p.(PlayerEntry.wallet) == wallet)
      self.(GameRound.players).

  (*
  /// Get mutable player by wallet address
  pub fn find_player_mut(&mut self, wallet: &Pubkey) -> Option<&mut PlayerEntry> {
      self.players.iter_mut().find(|p| p.wallet == *wallet)
  }
  *)
  Definition find_player_mut
      (self: GameRound.t)
      (wallet: Pubkey.t) :
      option ((PlayerEntry.t -> PlayerEntry.t) -> GameRound.t) :=
    match
      zipper_find
        (fun (p : PlayerEntry.t) => p.(PlayerEntry.wallet) == wallet)
        self.(GameRound.players)
    with
    | Some (player, (prefix, suffix)) =>
        let res handle :=
          self <|
            GameRound.players := unzipper (handle player) prefix suffix
          |>
        in Some res
    | None => None
    end.

  (*
  /// Calculate total pot value (just initial pot in small games MVP)
  pub fn total_pot(&self) -> u64 {
      self.initial_pot
  }
  *)
  Definition total_pot (self: GameRound.t) : u64 :=
    self.(GameRound.initial_pot).

End GameRound.
Export (hints) GameRound.

