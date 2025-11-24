From Excalead Require Import Excalead Anchor_lang.

(*
/// Configuration for game durations
#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct GameDurationConfig {
    pub waiting_phase_duration: u64,
}
*)
Module GameDurationConfig.
  Record t : Set := {
    waiting_phase_duration : u64;
  }.
  (*
  pub const LEN: usize = 8 + 8 + 8 + 8; // 32 bytes
  *)
  Definition LEN : usize := 8 + 8 + 8 + 8.

  #[export]
  Instance GameDurationConfig_JEncode : JEncode GameDurationConfig.t :=
    fun x => JSON__Object [
      ("waiting_phase_duration", encode x.(waiting_phase_duration)) ].

  #[export]
  Instance GameDurationConfig_JDecode : JDecode GameDurationConfig.t :=
    fun j => match j with
    | JSON__Object [("waiting_phase_duration", waiting_phase_duration_json)] =>
      decode waiting_phase_duration_json >>= fun waiting_phase_duration =>
      inr {| waiting_phase_duration := waiting_phase_duration |}
    | _ =>
      inl "Failed to decode GameDurationConfig"
    end.

End GameDurationConfig.
Export (hints) GameDurationConfig.



(*
/// Global game configuration stored as singleton PDA
/// Seeds: [b"game_config"]
#[account]
pub struct GameConfig {
    pub authority: Pubkey,
    pub treasury: Pubkey,
    pub house_fee_basis_points: u16,     // 500 = 5%
    pub min_bet_lamports: u64,           // 10,000,000 = 0.01 SOL
    pub small_game_duration_config: GameDurationConfig,

    // ORAO VRF configuration
    pub vrf_fee_lamports: u64,        // Fee for VRF requests (0.001 SOL)
    pub vrf_network_state: Pubkey,    // ORAO network state account
    pub vrf_treasury: Pubkey,         // ORAO treasury account
}
*)
Module GameConfig.
  Record t : Set := {
    authority: Pubkey.t;
    treasury: Pubkey.t;
    house_fee_basis_points: u16;
    min_bet_lamports: u64;
    small_game_duration_config: GameDurationConfig.t;

    vrf_fee_lamports: u64;
    vrf_network_state: Pubkey.t;
    vrf_treasury: Pubkey.t;
  }.

  #[export]
  Instance GameConfig_JEncode : JEncode GameConfig.t :=
    fun x =>
      JSON__Object [
        ("authority", encode x.(authority));
        ("treasure", encode x.(treasury));
        ("house_fee_basis_points", encode x.(house_fee_basis_points));
        ("min_bet_lamports", encode x.(min_bet_lamports));
        ("small_game_duration_config", encode x.(small_game_duration_config));
        ("vrf_fee_lamports", encode x.(vrf_fee_lamports));
        ("vrf_network_state", encode x.(vrf_network_state));
        ("vrf_treasury", encode x.(vrf_treasury))
      ].

  #[export]
  Instance GameConfig_JDecode : JDecode GameConfig.t :=
    fun j => match j with
      | JSON__Object [
          ("authority", authority_json);
          ("treasure", treasury_json);
          ("house_fee_basis_points", house_fee_basis_points_json);
          ("min_bet_lamports", min_bet_lamports_json);
          ("small_game_duration_config", small_game_duration_config_json);
          ("vrf_fee_lamports", vrf_fee_lamports_json);
          ("vrf_network_state", vrf_network_state_json);
          ("vrf_treasury", vrf_treasury_json) ] =>
        decode authority_json >>= fun authority =>
        decode treasury_json >>= fun treasury =>
        decode house_fee_basis_points_json >>= fun house_fee_basis_points =>
        decode min_bet_lamports_json >>= fun min_bet_lamports =>
        decode small_game_duration_config_json >>= fun small_game_duration_config =>
        decode vrf_fee_lamports_json >>= fun vrf_fee_lamports =>
        decode vrf_network_state_json >>= fun vrf_network_state =>
        decode vrf_treasury_json >>= fun vrf_treasury =>
        inr {| authority := authority;
               treasury := treasury;
               house_fee_basis_points := house_fee_basis_points;
               min_bet_lamports := min_bet_lamports;
               small_game_duration_config := small_game_duration_config;
               vrf_fee_lamports := vrf_fee_lamports;
               vrf_network_state := vrf_network_state;
               vrf_treasury := vrf_treasury |}
    | _ => inl "Failed to decode GameConfig"
    end
        .

  (*
  /// Account space calculation:
  /// 8 (discriminator) + 32 (authority) + 32 (treasury) + 2 (house_fee) + 8 (min_bet)
  /// + 32 (small_game_config) + 32 (large_game_config) 
  /// + 8 (vrf_fee) + 32 (vrf_network_state) + 32 (vrf_treasury) = 218 bytes
  pub const LEN: usize = 8 + 32 + 32 + 2 + 8 + GameDurationConfig::LEN + GameDurationConfig::LEN + 8 + 32 + 32;
  *)
  Definition LEN: usize := 8 + 32 + 32 + 2 + 8 + GameDurationConfig.LEN + GameDurationConfig.LEN + 8 + 32 + 32.

  (*
  /// Calculate house fee from pot amount
  pub fn calculate_house_fee(&self, pot_amount: u64) -> u64 {
      pot_amount
          .saturating_mul(self.house_fee_basis_points as u64)
          .saturating_div(10_000)
  }
  *)
  Definition calculate_house_fee (self: GameConfig.t) (pot_amount: u64) : u64 :=
    let house_fee_basis_points_as_u64 :=
      self.(GameConfig.house_fee_basis_points) : u64 in
    Z.div
      (Z.mul pot_amount house_fee_basis_points_as_u64)
      10000.

  (*
  /// Calculate winner payout after house fee
  pub fn calculate_winner_payout(&self, pot_amount: u64) -> u64 {
      pot_amount.saturating_sub(self.calculate_house_fee(pot_amount))
  }
  *)
  Definition calculate_winner_payout (self: GameConfig.t) (pot_amount: u64) : u64 :=
    Z.sub pot_amount (calculate_house_fee self pot_amount).

  (*
  /// Validate if a bet amount meets minimum requirements
  pub fn is_valid_bet_amount(&self, amount: u64) -> bool {
      amount >= self.min_bet_lamports
  }
  *)
  Definition is_valid_bet_amount (self: GameConfig.t) (amount: u64) : bool :=
    amount >=? self.(GameConfig.min_bet_lamports).
End GameConfig.
Export (hints) GameConfig.
