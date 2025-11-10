// Instructions module - contains all instruction handlers
pub mod initialize;
pub mod deposit_bet;
// pub mod place_spectator_bet;  // Removed for small games MVP
// pub mod progress_to_resolution;  // Removed - replaced by unified
// pub mod progress_to_final_battle;  // Removed for small games MVP
// pub mod resolve_finalists;  // Removed for small games MVP
// pub mod resolve_winner;  // Removed - replaced by unified
// pub mod distribute_winnings;  // Removed - replaced by unified
// pub mod claim_winnings;  // Removed for small games MVP

// ORAO VRF unified instructions
pub mod unified_progress_to_resolution;
pub mod unified_resolve_and_distribute;

pub use initialize::*;
pub use deposit_bet::*;
// pub use place_spectator_bet::*;  // Removed for small games MVP
// pub use progress_to_resolution::*;  // Removed - replaced by unified
// pub use progress_to_final_battle::*;  // Removed for small games MVP
// pub use resolve_finalists::*;  // Removed for small games MVP
// pub use resolve_winner::*;  // Removed - replaced by unified
// pub use distribute_winnings::*;  // Removed - replaced by unified
// pub use claim_winnings::*;  // Removed for small games MVP

// ORAO VRF unified exports
pub use unified_progress_to_resolution::*;
pub use unified_resolve_and_distribute::*;