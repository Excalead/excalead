Require Import Excalead.Excalead.

(*
pub struct BetInfo {
    pub wallet_index: u16,  // Index into the wallets Vec
    pub amount: u64,        // Bet amount in lamports
    pub skin: u8,           // Character skin ID (0-255)
    pub position: [u16; 2], // [x, y] spawn position on map
}
*)
Module BetInfo.
  Record t : Set := {
    wallet_index : u16;
    amount : u64;
    skin : u8;
    position : u16 * u16;
  }.
End BetInfo.

(*
#[account]
pub struct Domin8Game {
    pub game_round: u64,
    pub start_date: i64,
    pub end_date: i64,
    pub total_deposit: u64,
    pub rand: u64,
    pub background: u8, // Background ID (0-255)
    pub user_count: u64,
    pub force: [u8; 32], // VRF force seed for this game
    pub status: u8,      // 0 = open, 1 = closed
    pub winner: Option<Pubkey>,
    pub winner_prize: u64, // Prize amount to be claimed by winner
    pub winning_bet_index: Option<u64>,
    pub wallets: Vec<Pubkey>, // Unique wallets (stored once)
    pub bets: Vec<BetInfo>,   // (wallet_index, amount, skin, position) tuples
}
*)
Module Domin8Game.
  Record t : Set := {
    game_round : u64;
    start_date : i64;
    end_date : i64;
    total_deposit : u64;
    rand : u64;
    background : u8;
    user_count : u64;
    force : Hash;
    status : u8;
    winner : option Pubkey;
    winner_prize : u64;
    winning_bet_index : option u64;
    wallets : list Pubkey;
    bets : list BetInfo.t;
  }.
End Domin8Game.
