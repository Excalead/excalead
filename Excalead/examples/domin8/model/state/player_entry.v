From Excalead Require Import Excalead Anchor_lang.

(*
/// Individual player entry in a game round
#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct PlayerEntry {
    pub wallet: Pubkey,
    pub total_bet: u64,
    pub timestamp: i64,
}
*)
Module PlayerEntry.
  Record t : Set := {
    wallet: Pubkey.t;
    total_bet: u64;
    timestamp: i64
  }.

  #[export]
  Instance PlayerEntry_JEncode : JEncode PlayerEntry.t :=
    fun x =>
    JSON__Object [
      ("wallet", encode x.(wallet));
      ("total_bet", encode x.(total_bet));
      ("timestamp", encode x.(timestamp))
      ].

  #[export]
  Instance PlayerEntry_JDecode : JDecode PlayerEntry.t :=
    fun j : json =>
      match j with
      | JSON__Object  [ ("wallet", wallet_json);
            ("total_bet", total_bet_json);
            ("timestamp", timestamp_json) ] =>
          decode wallet_json >>= fun wallet =>
          decode total_bet_json >>= fun total_bet =>
          decode timestamp_json >>= fun timestamp =>
          inr {|
            wallet := wallet;
            total_bet := total_bet;
            timestamp := timestamp |}
      | _ => inl "Failed to decode PlayerEntry"
      end.

(*
  /// Player entry size: 32 (wallet) + 8 (total_bet) + 8 (timestamp) = 48 bytes
  pub const LEN: usize = 32 + 8 + 8;
*)
  Definition LEN: usize := 32 + 8 + 8.
End PlayerEntry.
Export (hints) PlayerEntry.


