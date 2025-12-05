From Excalead Require Import Excalead Anchor_lang.

Module IdentityError.
  Inductive t : Set :=
  | UriTooLong
  | KeyTooLong
  | ValueTooLong
  | MetadataLimitReached
  | Unauthorized
  | Overflow
  | MetadataNotFound
  | InvalidTokenAccount
  | ExtensionNotFound
  | InvalidExtensionIndex
  | InvalidCollectionMint
  | InvalidNftSupply
  | InvalidNftDecimals
  | TransferToSelf.

  Instance IdentityErrorCode_to_string : ToErrorString.C t := {|
    ToErrorString.to_error_string e :=
      match e with
      | UriTooLong => "URI too long"
      | KeyTooLong => "Key too long"
      | ValueTooLong => "Value too long"
      | MetadataLimitReached => "Metadate limit reached"
      | Unauthorized => "Unauthorized"
      | Overflow => "Overflow"
      | MetadataNotFound => "Metadate not found"
      | InvalidTokenAccount => "Invalid token account"
      | ExtensionNotFound => "Extension not found"
      | InvalidExtensionIndex => "Invalid extension index"
      | InvalidCollectionMint => "Invalid collection mint"
      | InvalidNftSupply => "Invalid nft supply"
      | InvalidNftDecimals => "Invalid nft decimals"
      | TransferToSelf => "Transfer to self"
    end;
  |}.
End IdentityError.
Export (hints) IdentityError.

