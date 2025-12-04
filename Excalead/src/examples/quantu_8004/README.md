# Solana ERC-8004

Here, we aim to model the smart contract https://github.com/QuantuLabs/8004-solana/tree/6eb9e4d0d88b75d7f4e84a1fc8dcb60d97d240c8 (the link includes the precise commit hash of the code we are modeling).

This is an on-going implementation of the https://eips.ethereum.org/EIPS/eip-8004 standard for Solana. A reference implementation in Solidity is available at https://github.com/erc-8004/erc-8004-contracts

There are three folders for the three sub-contracts of the project:

- `identity-registry`
- `reputation-registry`
- `validation-registry`

On the Solana side, the code will change to actually merge the three sub-contracts into a single contract, as this is more idiomatic (recommendation from [Jacob Creech](https://x.com/jacobvcreech)).
