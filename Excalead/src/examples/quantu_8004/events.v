From Excalead Require Import Excalead Anchor_lang.

Module ValidationRequested.
  Record t : Set := {
    agent_id: u64;
    validator_address: Pubkey.t;
    nonce: u32;
    request_uri: string;
    request_hash: Hash.t;
    requester: Pubkey.t;
    created_at: i64;
  }.
End ValidationRequested.

Module ValidationResponded.
  Record t : Set := {
    agent_id: u64;
    validator_address: Pubkey.t;
    nonce: u32;
    response: u8;
    response_uri: string;
    response_hash: Hash.t;
    tag: string;
    responded_at: i64;
  }.
End ValidationResponded.
