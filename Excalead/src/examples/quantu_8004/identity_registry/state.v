From Excalead Require Import Excalead Vector Anchor_lang.

From Coq Require Import Lists.List.

Module RegistryConfig.
  Record t : Set := {
    authority: Pubkey.t;
    next_agent_id: u64;
    total_agents: u64;
    collection_mint: Pubkey.t;
    collection_authority: u8;
    bump: u8;
  }.

  Definition SIZE : usize := 32 + 8 + 8 + 32  + 1 + 1.
End RegistryConfig.
Export (hints) RegistryConfig.

Module MetadataEntry.
  Record t : Set := {
    metadata_key: string;
    metadata_value: list u8;
  }.

  Definition MAX_SIZE: usize := 4 + 32 + 4 + 256.

  Definition MAX_KEY_LENGTH: usize := 32.

  Definition MAX_VALUE_LENGTH: usize := 256.
End MetadataEntry.
Export (hints) MetadataEntry.

Module AgentAccount.
  Record t : Set := {
    agent_id: u64;
    owner: Pubkey.t;
    agent_mint: Pubkey.t;
    agent_uri: Pubkey.t;
    nft_name: string;
    nft_symbol: string;
    metadata: list MetadataEntry.t;
    created_at: i64;
    bump: u8;
  }.

  Definition MAX_SIZE : usize := 8 +i 8 +i 32 +i 32 +i 4 +i 200 +i 2 +i 32 +i 4 +i 10 +i (1 *i MetadataEntry.MAX_SIZE) +i 8 +i 1.

  Definition MAX_METADATA_ENTRIES : usize := 1.

  Definition MAX_URI_LENGTH: usize := 200.

  Definition find_metadata (self: AgentAccount.t) (key: string) : option MetadataEntry.t :=
    List.find
      (fun (m : MetadataEntry.t) => m.(MetadataEntry.metadata_key) == key)
      self.(AgentAccount.metadata).

  Definition find_metadata_mut
      (self: AgentAccount.t)
      (key: string) :
      option ((MetadataEntry.t -> MetadataEntry.t) -> AgentAccount.t) :=
    match
      zipper_find
        (fun (m : MetadataEntry.t) => m.(MetadataEntry.metadata_key) == key)
        self.(AgentAccount.metadata)
    with
    | Some (metadata, (prefix, suffix)) =>
        let res handle :=
          self <|
            AgentAccount.metadata := unzipper (handle metadata) prefix suffix
          |>
        in Some res
    | None => None
    end.
End AgentAccount.
Export (hints) AgentAccount.

Module MetadataExtension.
  Record t : Set := {
    agent_mint: Pubkey.t;
    extension_index: u8;
    metadata: list MetadataEntry.t;
    bump: u8;
  }.

  Definition MAX_SIZE: usize := 8 +i 32 +i 1 +i 4 +i (10 *i MetadataEntry.MAX_SIZE) +i 1.

  Definition MAX_METADATA_ENTRIES: usize := 10.

  Definition find_metadata (self: MetadataExtension.t) (key: string) : option MetadataEntry.t :=
    List.find
      (fun (m : MetadataEntry.t) => m.(MetadataEntry.metadata_key) == key)
      self.(MetadataExtension.metadata).

  Definition find_metadata_mut
      (self: MetadataExtension.t)
      (key: string) :
      option ((MetadataEntry.t -> MetadataEntry.t) -> MetadataExtension.t) :=
    match
      zipper_find
        (fun (m : MetadataEntry.t) => m.(MetadataEntry.metadata_key) == key)
        self.(MetadataExtension.metadata)
    with
    | Some (metadata, (prefix, suffix)) =>
        let res handle :=
          self <|
            MetadataExtension.metadata := unzipper (handle metadata) prefix suffix
          |>
        in Some res
    | None => None
    end.

End MetadataExtension.
Export (hints) MetadataExtension.
