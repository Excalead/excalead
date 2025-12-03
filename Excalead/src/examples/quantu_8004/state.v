From Excalead Require Import Excalead Anchor_lang.

Module ValidationConfig.
  Record t : Set := {
    authority: Pubkey.t;
    identity_registry: Pubkey.t;
    total_requests: u64;
    total_responses: u64;
  }.

  Definition SIZE : usize := 32 + 32 + 8 + 8 + 1.
End ValidationConfig.
Export (hints) ValidationConfig.

Module ValidationRequest.
  Record t : Set := {
    agent_id: u64;
    validator_address: Pubkey.t;
    nonce: u32;
    request_hash: Hash.t;
    response_hash: Hash.t;
    response: u8;
    created_at: i64;
    responded_at: i64;
  }.

  Definition SIZE : usize := 8 + 32 + 4 + 32 + 32 + 1 + 8 + 8 + 1.

  Definition MAX_URI_LENGTH : usize := 200.

  Definition has_response (request : t) : bool :=
    request.(responded_at) >i 0.

  Definition is_pending (request : t) : bool :=
    request.(responded_at) =i 0.
End ValidationRequest.
Export (hints) ValidationRequest.
