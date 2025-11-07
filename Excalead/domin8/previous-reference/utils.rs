use anchor_lang::prelude::*;
use crate::error::Domin8Error;
use crate::state::BetInfo;

/// Utility functions for the domin8 program
pub struct Utils;

impl Utils {
    /// Convert bytes array to hex string for display
    pub fn bytes_to_hex(bytes: &[u8; 32]) -> String {
        bytes.iter()
            .map(|b| format!("{:02x}", b))
            .collect()
    }

    /// Select winner based on weighted random selection using VRF randomness
    ///
    /// This function implements a provably fair winner selection algorithm:
    /// 1. Uses VRF randomness to generate a random position in the total pot
    /// 2. Finds which bet this position falls into based on cumulative bet amounts
    /// 3. Returns the winner's pubkey and bet index
    ///
    /// # Arguments
    /// * `randomness` - VRF randomness value
    /// * `bets` - Vector of all bets in the game
    /// * `wallets` - Vector of unique wallet addresses
    /// * `total_pot` - Total amount deposited (for validation)
    ///
    /// # Returns
    /// * `(winner_pubkey, winning_bet_index)` - The winner and their bet index
    pub fn select_winner_by_weight(
        randomness: u64,
        bets: &[BetInfo],
        wallets: &[Pubkey],
        total_pot: u64
    ) -> Result<(Pubkey, usize)> {
        require!(!bets.is_empty(), Domin8Error::NoBets);
        require!(total_pot > 0, Domin8Error::ArithmeticError);

        // Use randomness to select a position in the total pot
        let winning_position = randomness % total_pot;

        // Linear search with proper overflow handling
        let mut cumulative = 0u64;
        for (index, bet) in bets.iter().enumerate() {
            cumulative = cumulative.checked_add(bet.amount)
                .ok_or(Domin8Error::ArithmeticError)?;

            if winning_position < cumulative {
                // Get the actual wallet from the wallet_index
                let wallet = wallets.get(bet.wallet_index as usize)
                    .ok_or(Domin8Error::ArithmeticError)?;
                return Ok((*wallet, index));
            }
        }

        // Fallback to last bet (should never happen with correct math)
        let last_index = bets.len() - 1;
        let last_wallet = wallets.get(bets[last_index].wallet_index as usize)
            .ok_or(Domin8Error::ArithmeticError)?;
        Ok((*last_wallet, last_index))
    }

    /// Calculate fee amount from total pot and basis points
    ///
    /// # Arguments
    /// * `total_pot` - The total amount in the pot (in lamports)
    /// * `fee_bps` - Fee percentage in basis points (1 bps = 0.01%)
    ///
    /// # Examples
    /// * calculate_fee(1_000_000, 500) = 50_000 (5% of 1M lamports)
    /// * calculate_fee(2_000_000, 250) = 50_000 (2.5% of 2M lamports)
    ///
    /// # Formula
    /// fee_amount = (total_pot * fee_bps) / 10000
    pub fn calculate_fee(total_pot: u64, fee_bps: u64) -> Result<u64> {
        // Validate fee percentage is within bounds
        require!(fee_bps <= 10000, Domin8Error::FeeTooHigh); // Max 100%

        // Calculate: (total_pot * fee_bps) / 10000
        let fee_amount = total_pot
            .checked_mul(fee_bps)
            .ok_or(Domin8Error::ArithmeticError)?
            .checked_div(10000)
            .ok_or(Domin8Error::ArithmeticError)?;

        Ok(fee_amount)
    }

    /// Calculate percentage from basis points for display purposes
    ///
    /// # Arguments
    /// * `bps` - Basis points (1 bps = 0.01%)
    ///
    /// # Returns
    /// Percentage as f64 (e.g., 500 bps = 5.0%)
    pub fn bps_to_percentage(bps: u64) -> f64 {
        bps as f64 / 100.0
    }
}
