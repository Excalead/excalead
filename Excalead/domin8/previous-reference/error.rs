use anchor_lang::prelude::*;

#[error_code]
pub enum Domin8Error {
    #[msg("Unauthorized access - admin only")]
    Unauthorized,
    #[msg("Game system is locked")]
    GameLocked,
    #[msg("Game is not open for betting")]
    GameNotOpen,
    #[msg("Game has not ended yet")]
    GameNotEnded,
    #[msg("Bet amount below minimum required")]
    InsufficientBet,
    #[msg("Bet amount exceeds maximum allowed")]
    ExcessiveBet,
    #[msg("Game round already exists")]
    GameAlreadyExists,
    #[msg("VRF randomness not ready")]
    RandomnessNotReady,
    #[msg("No winner could be determined")]
    NoWinnerFound,
    #[msg("Invalid winner account")]
    InvalidWinner,
    #[msg("Invalid game status for this operation")]
    InvalidGameStatus,
    #[msg("Game round has expired")]
    GameExpired,
    #[msg("Insufficient funds for bet")]
    InsufficientFunds,
    #[msg("Arithmetic operation failed")]
    ArithmeticError,
    #[msg("Invalid VRF force seed format")]
    InvalidVrfForce,
    #[msg("Invalid wallet address")]
    InvalidWallet,
    #[msg("Fee percentage too high")]
    FeeTooHigh,
    #[msg("Round time out of bounds")]
    InvalidRoundTime,
    #[msg("Game has no bets")]
    NoBets,
    #[msg("Cannot modify active game")]
    GameActive,
    #[msg("User has exceeded maximum bets per game")]
    UserBetLimitExceeded,
    #[msg("Invalid skin ID")]
    InvalidSkin,
    #[msg("Invalid position coordinates")]
    InvalidPosition,
}
