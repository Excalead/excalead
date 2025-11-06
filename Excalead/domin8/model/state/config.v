Require Import Excalead.Excalead.

(*
#[account]
pub struct Domin8Config {
    pub admin: Pubkey,              // Admin wallet (can manage config)
    pub treasury: Pubkey,            // Treasury wallet for house fees
    pub game_round: u64,            // Current/next game round number
    pub house_fee: u64,             // House fee in basis points (e.g., 500 = 5%)
    pub min_deposit_amount: u64,    // Minimum bet amount
    pub max_deposit_amount: u64,    // Maximum bet amount
    pub round_time: u64,            // Game duration in seconds
    pub lock: bool,                 // System lock (true when game is active)
    pub force: [u8; 32],            // VRF force seed for next game
}
*)
Module Domin8Config.
  Record t : Set := {
    admin : Pubkey;
    treasury : Pubkey;
    game_round : u64;
    house_fee : u64;
    min_deposit_amount : u64;
    max_deposit_amount : u64;
    round_time : u64;
    lock : bool;
    force : Hash;
  }.
End Domin8Config.
