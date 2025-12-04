From Excalead Require Import Excalead Anchor_lang.

Module ValidationError.
  Inductive t : Set :=
  | RequestUriTooLong
  | ResponseUriTooLong
  | InvalidResponse
  | UnauthorizedValidator
  | UnauthorizedRequester
  | AgentNotFound
  | RequestNotFound
  | Overflow
  | InvalidNonce
  | RequestHashMismatch
  | InvalidIdentityRegistry
  | Unauthorized
  | InvalidTokenAccount.

  Instance ValidationErrorCode_to_string : ToErrorString.C t := {|
    ToErrorString.to_error_string e :=
      match e with
      | RequestUriTooLong => "Request URI too long"
      | ResponseUriTooLong => "Response URI too long"
      | InvalidResponse => "Invalid response"
      | UnauthorizedValidator => "Unauthorized validator"
      | UnauthorizedRequester => "Unauthorized requester"
      | AgentNotFound => "Agent not found"
      | RequestNotFound => "Request not found"
      | Overflow => "Overflow"
      | InvalidNonce => "Invalid nonce"
      | RequestHashMismatch => "Request hash mismatch"
      | InvalidIdentityRegistry => "Invalid identity registry"
      | Unauthorized => "Unauthorized"
      | InvalidTokenAccount => "Invalid token account"
    end;
  |}.
End ValidationError.
Export (hints) ValidationError.
