Require Import Excalead.Excalead.


(** Game constraints *)
Definition MAX_PLAYERS: usize := 64.

(** Financial constants *)
Definition MIN_BET_LAMPORTS: u64 := 10_000_000.
Definition HOUSE_FEE_BASIS_POINTS: u16 := 500.

(** PDA seeds for deterministic account derivation *)
Definition GAME_CONFIG_SEED: string := "game_config".
Definition GAME_ROUND_SEED: string := "game_round".
Definition VAULT_SEED: string := "vault".

(** Default game durations (in seconds) *)

(** Small games (2-64 players) *)
Definition DEFAULT_SMALL_GAME_WAITING_DURATION: u64 := 30.
Definition DEFAULT_SMALL_GAME_ELIMINATION_DURATION: u64 := 0.
Definition DEFAULT_SMALL_GAME_SPECTATOR_BETTING_DURATION: u64 := 0.
Definition DEFAULT_SMALL_GAME_RESOLVING_DURATION: u64 := 15.



(** Account space calculations for rent exemption *)
(** These constants are used to determine the exact amount of SOL needed for rent exemption *)

(** GameConfig account space: ~146 bytes *)
(** - 8 (discriminator) + 32 (authority) + 32 (treasury) + 2 (house_fee) + 8 (min_bet) *)
(** - + 32 (small_game_config) + 32 (large_game_config) = 146 bytes *)
Definition GAME_CONFIG_SPACE: usize := 146.

(** GameRound account space: ~4797 bytes (~4.7KB)*)
(** - Base: 8 + 8 + 1 + 8 + 8 + 8 + 32 + 32 + 32 + 8 = 145 bytes *)
(** - Players: 4 + (64 * 48) = 3076 bytes *)
(** - Finalists: 4 + (4 * 32) = 132 bytes *)
(** - Spectator bets: 4 + (20 * 72) = 1444 bytes *)
(** - Total: ~4797 bytes *)
Definition GAME_ROUND_SPACE: usize := 4797.

