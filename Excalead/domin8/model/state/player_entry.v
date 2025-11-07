Require Import Excalead.Excalead.

(*
/// Individual player entry in a game round
#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct PlayerEntry {
    pub wallet: Pubkey,
    pub total_bet: u64,
    pub timestamp: i64,
}
*)
Module PlayerEntity.
  Record t : Set := {
    wallet: Pubkey;
    total_bet: u64;
    timestamp: i64
  }.

(*
  /// Player entry size: 32 (wallet) + 8 (total_bet) + 8 (timestamp) = 48 bytes
  pub const LEN: usize = 32 + 8 + 8;
*)
  Definition LEN: usize := 32 + 8 + 8.
End PlayerEntry.


