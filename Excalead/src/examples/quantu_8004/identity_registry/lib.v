From Excalead Require Import Excalead Anchor_lang Anchor_spl.
From Excalead.examples.quantu_8004.identity_registry Require Import error state.

Module Initialize.
  Record t : Set := {
    config: RegistryConfig.t;
    (* collection_mint: Mint.t; *)
    collection_metadata: UncheckedAccount.t;
    collection_master_edition: UncheckedAccount.t;
    collection_token_account: TokenAccount.t;
    collection_authority_pda: UncheckedAccount.t;
    authority: Signer.t;
    system_program: System.t;
    (* token_program: Token.t; *)
    (* associated_token_program: AssociatedToken.t; *)
    (* rent: Sysvar.t Rent.t; *)
    (* token_metadata_program: Metadata.t; *)
    sysvar_instructions: UncheckedAccount.t;
  }.
End Initialize.

Module Register.
  Record t : Set := {
    config: RegistryConfig.t;
    collection_authority_pda: UncheckedAccount.t;
    agent_account: AgentAccount.t;
    (* agent_mint: Mint.t; *)
    agent_metadata: UncheckedAccount.t;
    agent_master_edition: UncheckedAccount.t;
    agent_token_account: TokenAccount.t;
    (* colleciton_mint: Mint.t; *)
    collection_metadata: UncheckedAccount.t;
    collection_master_edition: UncheckedAccount.t;
    owner: Signer.t;
    system_program: System.t;
    (* token_program: Token.t; *)
    (* associated_token_program: AssociatedToken.t; *)
    (* rent: Sysvar.t Rent.t; *)
    (* token_metadata_program: Metadata.t; *)
    sysvar_instructions: UncheckedAccount.t;
  }.
End Register.

Module GetMetadata.
  Record t : Set := {
    agent_account: AgentAccount.t;
  }.
End GetMetadata.

Module SetMetadata.
  Record t : Set := {
    agent_account: AgentAccount.t;
    token_account: TokenAccount.t;
    owner: Signer.t;
  }.
End SetMetadata.

Module SetAgentUri.
  Record t : Set := {
    agent_account: AgentAccount.t;
    token_account: TokenAccount.t;
    agent_metadata: UncheckedAccount.t;
    (* agent_mint: Mint.t; *)
    owner: Signer.t;
    (* token_metadata_program: Metadata.t; *)
    system_program: System.t;
    sysvar_instructions: UncheckedAccount.t;
  }.
End SetAgentUri.

Module SyncOwner.
  Record t : Set := {
    agent_account: AgentAccount.t;
    token_account: TokenAccount.t;
    agent_metadata: UncheckedAccount.t;
    (* agent_mint: Mint.t; *)
    old_owner_signer: Signer.t;
    (* token_metadata_program: Metadata.t; *)
    system_program: System.t;
    sysvar_instructions: UncheckedAccount.t;
  }.
End SyncOwner.

Module OwnerOf.
  Record t : Set := {
    agent_account: AgentAccount.t;
  }.
End OwnerOf.

Module CreateMetadataExtension.
  Record t : Set := {
    metadata_extension: MetadataExtension.t;
    (* agent_mint: Mint.t; *)
    agent_account: AgentAccount.t;
    token_account: TokenAccount.t;
    owner: Signer.t;
    system_program: System.t;
  }.
End CreateMetadataExtension.

Module  SetMetadataExtended.
  Record t : Set := {
    metadata_extension: MetadataExtension.t;
    (* agent_mint: Mint.t; *)
    agent_account: AgentAccount.t;
    token_account: TokenAccount.t;
    owner: Signer.t;
  }.
End  SetMetadataExtended.

Module GetMetadataExtended.
  Record t : Set := {
    metadata_extension: MetadataExtension.t;
    (* agent_mint: Mint.t; *)
  }.
End GetMetadataExtended.

Module TransferAgent.
  Record t : Set := {
    agent_account: AgentAccount.t;
    from_token_account: TokenAccount.t;
    to_token_account: TokenAccount.t;
    (* agent_mint: Mint.t; *)
    agent_metadata: UncheckedAccount.t;
    owner: Signer.t;
    (* token_program: Token.t; *)
    (* token_metadata_program: Metadata.t; *)
    system_program: System.t;
    sysvar_instructions: UncheckedAccount.t;
  }.
End TransferAgent.

Module Registered.
  Record t : Set := {
    agent_id: u64;
    agent_uri: string;
    owner: Pubkey.t;
    agent_mint: Pubkey.t;
  }.
End Registered.

Module MetadataSet.
  Record t : Set := {
    agent_id: u64;
    indexed_key: string;
    key: string;
    value: list u8;
  }.
End MetadataSet.

Module UriUpdated.
  Record t : Set := {
    agent_id: u64;
    new_uri: string;
    updated_by: Pubkey.t;
  }.
End UriUpdated.

Module AgentOwnerSynced.
  Record t : Set := {
    agent_id: u64;
    old_owner: Pubkey.t;
    new_owner: Pubkey.t;
    agent_mint: Pubkey.t;
  }.
End AgentOwnerSynced.

Module identity_registry.
  Definition initialize
    (ctx: Context.t Initialize.t)
    : Result.t (Context.t Initialize.t)  :=

    let ctx := Context.mutate_accounts ctx (fun accounts =>
      let config := accounts.(Initialize.config)
          <| RegistryConfig.authority :=
              key ctx.(Context.accounts).(Initialize.authority) |>
          <| RegistryConfig.next_agent_id := 0 |>
          <| RegistryConfig.total_agents  := 0 |>
      (* <| RegistryConfig.collection_mint := *)
      (*     key ctx.(Context.accounts).(Initialize.collection_mint) |> *)
      (* <| RegistryConfig.bump := *)
      (*     ctx.(Context.bumps).(Bumps.config) |> *)
      in accounts <| Initialize.config := config |>) in

    (* token::mint_to( *)
    (*     CpiContext::new( *)
    (*         ctx.accounts.token_program.to_account_info(), *)
    (*         MintTo { *)
    (*             mint: ctx.accounts.collection_mint.to_account_info(), *)
    (*             to: ctx.accounts.collection_token_account.to_account_info(), *)
    (*             authority: ctx.accounts.authority.to_account_info(), *)
    (*         }, *)
    (*     ), *)
    (*     1, *)
    (* )?; *)

    (* // Create Metaplex Collection NFT metadata + master edition *)
    (* CreateV1CpiBuilder::new(&ctx.accounts.token_metadata_program.to_account_info()) *)
    (*     .metadata(&ctx.accounts.collection_metadata) *)
    (*     .master_edition(Some(&ctx.accounts.collection_master_edition)) *)
    (*     .mint(&ctx.accounts.collection_mint.to_account_info(), false) *)
    (*     .authority(&ctx.accounts.authority.to_account_info()) *)
    (*     .payer(&ctx.accounts.authority.to_account_info()) *)
    (*     .update_authority(&ctx.accounts.authority.to_account_info(), true) *)
    (*     .system_program(&ctx.accounts.system_program.to_account_info()) *)
    (*     .sysvar_instructions(&ctx.accounts.sysvar_instructions) *)
    (*     .spl_token_program(Some(&ctx.accounts.token_program.to_account_info())) *)
    (*     .name("ERC8004".to_string()) *)
    (*     .uri("".to_string()) *)
    (*     .seller_fee_basis_points(0) *)
    (*     .token_standard(TokenStandard::NonFungible) *)
    (*     .print_supply(PrintSupply::Zero) *)
    (*     .invoke()?; *)

    (* // IMMEDIATELY transfer collection update_authority to PDA (atomique!) *)
    (* // This allows the program to sign for collection verification without requiring deployer signature *)
    (* UpdateV1CpiBuilder::new(&ctx.accounts.token_metadata_program.to_account_info()) *)
    (*     .authority(&ctx.accounts.authority.to_account_info()) *)
    (*     .mint(&ctx.accounts.collection_mint.to_account_info()) *)
    (*     .metadata(&ctx.accounts.collection_metadata) *)
    (*     .payer(&ctx.accounts.authority.to_account_info()) *)
    (*     .system_program(&ctx.accounts.system_program.to_account_info()) *)
    (*     .sysvar_instructions(&ctx.accounts.sysvar_instructions) *)
    (*     .new_update_authority(ctx.accounts.collection_authority_pda.key()) *)
    (*     .invoke()?; *)

    (* // Save collection_authority_pda bump for invoke_signed in register() *)
    (* config.collection_authority_bump = ctx.bumps.collection_authority_pda; *)

    (* msg!( *)
    (*     "Identity Registry initialized with collection mint: {}", *)
    (*     config.collection_mint *)
    (* ); *)
    (* msg!( *)
    (*     "Collection authority transferred to PDA: {}", *)
    (*     ctx.accounts.collection_authority_pda.key() *)
    (* ); *)

    Result.Ok ctx.

  Definition register_internal
      (ctx: Context.t Register.t)
      (agent_uri: string)
      (metadata: list MetadataEntry.t)
      : Result.t (Context.t Register.t) :=
    require!
        Z.of_nat (String.length agent_uri) <=i AgentAccount.MAX_URI_LENGTH with
        IdentityError.UriTooLong
    in

    (* // Validate metadata *)
    require!
        Z.of_nat (List.length metadata) <=i AgentAccount.MAX_METADATA_ENTRIES with
        IdentityError.MetadataLimitReached
    in

    (* for entry in &metadata { *)
    (*     require!( *)
    (*         entry.metadata_key.len() <= MetadataEntry::MAX_KEY_LENGTH, *)
    (*         IdentityError::KeyTooLong *)
    (*     ); *)
    (*     require!( *)
    (*         entry.metadata_value.len() <= MetadataEntry::MAX_VALUE_LENGTH, *)
    (*         IdentityError::ValueTooLong *)
    (*     ); *)
    (* } *)

    (* // Extract bump before taking mutable reference (borrow checker) *)
    let collection_authority_bump :=
      ctx.(Context.accounts).(Initialize.config).(RegistryConfig.collection_authority_bump) in
    (* let collection_mint := *)
    (*   ctx.(Context.accounts).(Initialize.config).(RegistryConfig.collection_mint) in *)

    let ctx := Context.mutate_accounts ctx (fun accounts =>
      let config := accounts.(Initialize.config) in
      (* let agent_id = config.next_agent_id; *)

      (* // Increment counters with overflow protection *)
      (* config.next_agent_id = config *)
      (*     .next_agent_id *)
      (*     .checked_add(1) *)
      (*     .ok_or(IdentityError::Overflow)?; *)

      (* config.total_agents = config *)
      (*     .total_agents *)
      (*     .checked_add(1) *)
      (*     .ok_or(IdentityError::Overflow)?; *)
      accounts <| Initialize.config := config |>) in

    (* // Mint 1 agent NFT to owner *)
    (* token::mint_to( *)
    (*     CpiContext::new( *)
    (*         ctx.accounts.token_program.to_account_info(), *)
    (*         MintTo { *)
    (*             mint: ctx.accounts.agent_mint.to_account_info(), *)
    (*             to: ctx.accounts.agent_token_account.to_account_info(), *)
    (*             authority: ctx.accounts.owner.to_account_info(), *)
    (*         }, *)
    (*     ), *)
    (*     1, *)
    (* )?; *)

    (* // Create Metaplex NFT metadata + master edition WITH collection reference *)
    (* let agent_name = format!("Agent #{}", agent_id); *)
    (* let metadata_uri = if agent_uri.is_empty() { *)
    (*     String::new() *)
    (* } else { *)
    (*     agent_uri.clone() *)
    (* }; *)

    (* CreateV1CpiBuilder::new(&ctx.accounts.token_metadata_program.to_account_info()) *)
    (*     .metadata(&ctx.accounts.agent_metadata) *)
    (*     .master_edition(Some(&ctx.accounts.agent_master_edition)) *)
    (*     .mint(&ctx.accounts.agent_mint.to_account_info(), true) *)
    (*     .authority(&ctx.accounts.owner.to_account_info()) *)
    (*     .payer(&ctx.accounts.owner.to_account_info()) *)
    (*     .update_authority(&ctx.accounts.owner.to_account_info(), true) *)
    (*     .system_program(&ctx.accounts.system_program.to_account_info()) *)
    (*     .sysvar_instructions(&ctx.accounts.sysvar_instructions) *)
    (*     .spl_token_program(Some(&ctx.accounts.token_program.to_account_info())) *)
    (*     .name(agent_name.clone()) *)
    (*     .uri(metadata_uri) *)
    (*     .seller_fee_basis_points(0) *)
    (*     .token_standard(TokenStandard::NonFungible) *)
    (*     .print_supply(PrintSupply::Zero) *)
    (*     .collection(Collection { *)
    (*         verified: false, *)
    (*         key: collection_mint, *)
    (*     }) *)
    (*     .invoke()?; *)

    (* // Verify collection membership (PDA signs via invoke_signed) *)
    (* // Program can sign automatically without requiring deployer signature *)
    (* let collection_authority_seeds = &[ *)
    (*     b"collection_authority".as_ref(), *)
    (*     &[collection_authority_bump], *)
    (* ]; *)
    (* let collection_authority_signer = &[&collection_authority_seeds[..]]; *)

    (* // Use VerifyCollectionV1 instead of SetAndVerifyCollection *)
    (* // VerifyCollection doesn't require matching update_authority between agent NFT and collection *)
    (* // It only requires the collection_authority (our PDA) to sign *)
    (* VerifyCollectionV1CpiBuilder::new( *)
    (*     &ctx.accounts.token_metadata_program.to_account_info(), *)
    (* ) *)
    (* .authority(&ctx.accounts.collection_authority_pda.to_account_info()) *)
    (* .delegate_record(None) *)
    (* .metadata(&ctx.accounts.agent_metadata) *)
    (* .collection_mint(&ctx.accounts.collection_mint.to_account_info()) *)
    (* .collection_metadata(Some(&ctx.accounts.collection_metadata)) *)
    (* .collection_master_edition(Some(&ctx.accounts.collection_master_edition)) *)
    (* .system_program(&ctx.accounts.system_program.to_account_info()) *)
    (* .sysvar_instructions(&ctx.accounts.sysvar_instructions) *)
    (* .invoke_signed(collection_authority_signer)?; *)

    (* // Initialize agent account *)
    (* let agent = &mut ctx.accounts.agent_account; *)
    (* agent.agent_id = agent_id; *)
    (* agent.owner = ctx.accounts.owner.key(); *)
    (* agent.agent_mint = ctx.accounts.agent_mint.key(); *)
    (* agent.agent_uri = agent_uri.clone(); *)
    (* agent.nft_name = agent_name.clone(); *)
    (* agent.nft_symbol = String::new(); // Empty symbol for now *)
    (* agent.metadata = metadata.clone(); *)
    (* agent.created_at = Clock::get()?.unix_timestamp; *)
    (* agent.bump = ctx.bumps.agent_account; *)

    (* // Emit registration event (ERC-8004 spec: Registered event) *)
    (* emit!(Registered { *)
    (*     agent_id, *)
    (*     agent_uri, *)
    (*     owner: ctx.accounts.owner.key(), *)
    (*     agent_mint: ctx.accounts.agent_mint.key(), *)
    (* }); *)

    (* // Emit metadata events if any *)
    (* for entry in &metadata { *)
    (*     emit!(MetadataSet { *)
    (*         agent_id, *)
    (*         indexed_key: entry.metadata_key.clone(), *)
    (*         key: entry.metadata_key.clone(), *)
    (*         value: entry.metadata_value.clone(), *)
    (*     }); *)
    (* } *)

    (* msg!( *)
    (*     "Agent {} registered with mint {} in collection {}", *)
    (*     agent_id, *)
    (*     agent.agent_mint, *)
    (*     config.collection_mint *)
    (* ); *)


    Result.Ok ctx.

  Definition register_empty
      (ctx: Context.t Register.t)
      : Result.t (Context.t Register.t) :=
    register_internal ctx "" [].

  Definition register
      (ctx: Context.t Register.t)
      (agent_uri: string)
      : Result.t (Context.t Register.t) :=
    register_internal ctx agent_uri [].

  Definition register_with_metadata
      (ctx: Context.t Register.t)
      (agent_uri: string)
      (metadata: list MetadataEntry.t)
      : Result.t (Context.t Register.t) :=
    register_internal ctx agent_uri metadata.

  Definition set_agent_uri
      (ctx: Context.t SetAgentUri.t)
      (new_uri: string)
      : Result.t (Context.t SetAgentUri.t) :=
    (* require!( *)
    (*     new_uri.len() <= AgentAccount::MAX_URI_LENGTH, *)
    (*     IdentityError::UriTooLong *)
    (* ); *)

    (* let agent = &mut ctx.accounts.agent_account; *)

    (* // Update AgentAccount URI *)
    (* agent.agent_uri = new_uri.clone(); *)

    (* // Sync URI to Metaplex NFT metadata using UpdateAsUpdateAuthorityV2 *)
    (* // This ensures wallets and marketplaces display the updated URI *)
    (* let metadata_data = Data { *)
    (*     name: agent.nft_name.clone(), *)
    (*     symbol: agent.nft_symbol.clone(), *)
    (*     uri: new_uri.clone(), *)
    (*     seller_fee_basis_points: 0, *)
    (*     creators: None, *)
    (* }; *)

    (* UpdateAsUpdateAuthorityV2CpiBuilder::new(&ctx.accounts.token_metadata_program.to_account_info()) *)
    (*     .authority(&ctx.accounts.owner.to_account_info()) *)
    (*     .mint(&ctx.accounts.agent_mint.to_account_info()) *)
    (*     .metadata(&ctx.accounts.agent_metadata.to_account_info()) *)
    (*     .payer(&ctx.accounts.owner.to_account_info()) *)
    (*     .system_program(&ctx.accounts.system_program.to_account_info()) *)
    (*     .sysvar_instructions(&ctx.accounts.sysvar_instructions.to_account_info()) *)
    (*     .data(metadata_data) *)
    (*     .invoke()?; *)

    (* // Emit event (ERC-8004 spec: UriUpdated event) *)
    (* emit!(UriUpdated { *)
    (*     agent_id: agent.agent_id, *)
    (*     new_uri: new_uri.clone(), *)
    (*     updated_by: ctx.accounts.owner.key(), *)
    (* }); *)

    (* msg!( *)
    (*     "Agent {} URI updated in AgentAccount and NFT metadata synced", *)
    (*     agent.agent_id *)
    (* ); *)

    Result.Ok ctx.

    Definition sync_owner
        (ctx: Context.t SyncOwner.t)
        : Result.t (Context.t SyncOwner.t) :=
        (* let agent = &mut ctx.accounts.agent_account; *)
        (* let token_account = &ctx.accounts.token_account; *)

        (* // Verify token account holds the agent NFT (amount = 1) *)
        (* require!( *)
        (*     token_account.amount == 1, *)
        (*     IdentityError::InvalidTokenAccount *)
        (* ); *)

        (* let old_owner = agent.owner; *)
        (* let new_owner = token_account.owner; *)

        (* // Update cached owner *)
        (* agent.owner = new_owner; *)

        (* // Transfer Metaplex update_authority to new owner (ERC-8004 compliance) *)
        (* // This allows the new owner to modify tokenURI via set_agent_uri() *)
        (* UpdateV1CpiBuilder::new(&ctx.accounts.token_metadata_program.to_account_info()) *)
        (*     .authority(&ctx.accounts.old_owner_signer.to_account_info()) *)
        (*     .mint(&ctx.accounts.agent_mint.to_account_info()) *)
        (*     .metadata(&ctx.accounts.agent_metadata.to_account_info()) *)
        (*     .payer(&ctx.accounts.old_owner_signer.to_account_info()) *)
        (*     .system_program(&ctx.accounts.system_program.to_account_info()) *)
        (*     .sysvar_instructions(&ctx.accounts.sysvar_instructions.to_account_info()) *)
        (*     .new_update_authority(new_owner) *)
        (*     .invoke()?; *)
        (**)
        (* // Emit event *)
        (* emit!(AgentOwnerSynced { *)
        (*     agent_id: agent.agent_id, *)
        (*     old_owner, *)
        (*     new_owner, *)
        (*     agent_mint: agent.agent_mint, *)
        (* }); *)

        (* msg!( *)
        (*     "Agent {} owner synced: {} -> {} (update_authority transferred)", *)
        (*     agent.agent_id, *)
        (*     old_owner, *)
        (*     new_owner *)
        (* ); *)

        Result.Ok ctx.

    Definition owner_of
        (ctx: Context.t OwnerOf.t)
        : Result.t Pubkey.t :=
      Result.Ok ctx.(Context.accounts).(OwnerOf.agent_account).(AgentAccount.owner).

    Definition create_metadata_extension
        (ctx: Context.t CreateMetadataExtension.t)
        (extension_index: u8)
        : Result.t (Context.t CreateMetadataExtension.t) :=
        (* let extension = &mut ctx.accounts.metadata_extension; *)
        (* extension.agent_mint = ctx.accounts.agent_mint.key(); *)
        (* extension.extension_index = extension_index; *)
        (* extension.metadata = Vec::new(); *)
        (* extension.bump = ctx.bumps.metadata_extension; *)

        (* msg!( *)
        (*     "Created metadata extension {} for agent mint {}", *)
        (*     extension_index, *)
        (*     extension.agent_mint *)
        (* ); *)

      Result.Ok ctx.

    Definition set_metadata_extended
        (ctx: Context.t SetMetadataExtended.t)
        (_extension_index: u8)
        (key: string)
        (value: list u8)
        : Result.t (Context.t SetMetadataExtended.t) :=
    (* pub fn set_metadata_extended( *)
    (*     ctx: Context<SetMetadataExtended>, *)
    (*     _extension_index: u8, *)
    (*     key: String, *)
    (*     value: Vec<u8>, *)
    (* ) -> Result<()> { *)
        (* // Validate key and value lengths *)
        (* require!( *)
        (*     key.len() <= MetadataEntry::MAX_KEY_LENGTH, *)
        (*     IdentityError::KeyTooLong *)
        (* ); *)
        (* require!( *)
        (*     value.len() <= MetadataEntry::MAX_VALUE_LENGTH, *)
        (*     IdentityError::ValueTooLong *)
        (* ); *)

        (* let extension = &mut ctx.accounts.metadata_extension; *)

        (* // Check if metadata key already exists, update it *)
        (* if let Some(entry) = extension.find_metadata_mut(&key) { *)
        (*     entry.metadata_value = value.clone(); *)
        (* } else { *)
        (*     // Add new entry if under limit *)
        (*     require!( *)
        (*         extension.metadata.len() < MetadataExtension::MAX_METADATA_ENTRIES, *)
        (*         IdentityError::MetadataLimitReached *)
        (*     ); *)
        (*     extension.metadata.push(MetadataEntry { metadata_key: key.clone(), metadata_value: value.clone() }); *)
        (* } *)

        (* // Emit event *)
        (* emit!(MetadataSet { *)
        (*     agent_id: ctx.accounts.agent_account.agent_id, *)
        (*     indexed_key: key.clone(), *)
        (*     key, *)
        (*     value, *)
        (* }); *)

        Result.Ok ctx.

    Definition get_metadata_extended
        (ctx: Context.t GetMetadataExtended.t)
        (_extension_index: u8)
        (key: string)
        : Result.t (list u8) :=
      let extension :=
        ctx.(Context.accounts).(GetMetadataExtended.metadata_extension) in
      match MetadataExtension.find_metadata extension key with
      | Some entry => Result.Ok entry.(MetadataEntry.metadata_value)
      | None => Result.Ok []
      end.

    Definition transfer_agent
        (ctx: Context.t TransferAgent.t)
        : Result.t (Context.t TransferAgent.t) :=
        (* // Prevent self-transfer *)
        (* require!( *)
        (*     ctx.accounts.from_token_account.key() != ctx.accounts.to_token_account.key(), *)
        (*     IdentityError::TransferToSelf *)
        (* ); *)

        (* // Step 1: SPL Token transfer via CPI *)
        (* let cpi_accounts = token::Transfer { *)
        (*     from: ctx.accounts.from_token_account.to_account_info(), *)
        (*     to: ctx.accounts.to_token_account.to_account_info(), *)
        (*     authority: ctx.accounts.owner.to_account_info(), *)
        (* }; *)
        (* token::transfer( *)
        (*     CpiContext::new( *)
        (*         ctx.accounts.token_program.to_account_info(), *)
        (*         cpi_accounts, *)
        (*     ), *)
        (*     1, // NFT amount *)
        (* )?; *)

        (* // Step 2: Transfer Metaplex update_authority to new owner (ERC-8004 compliance) *)
        (* // This allows the new owner to modify tokenURI via set_agent_uri() *)
        (* let new_owner = ctx.accounts.to_token_account.owner; *)
        (* UpdateV1CpiBuilder::new(&ctx.accounts.token_metadata_program.to_account_info()) *)
        (*     .authority(&ctx.accounts.owner.to_account_info()) *)
        (*     .mint(&ctx.accounts.agent_mint.to_account_info()) *)
        (*     .metadata(&ctx.accounts.agent_metadata.to_account_info()) *)
        (*     .payer(&ctx.accounts.owner.to_account_info()) *)
        (*     .system_program(&ctx.accounts.system_program.to_account_info()) *)
        (*     .sysvar_instructions(&ctx.accounts.sysvar_instructions.to_account_info()) *)
        (*     .new_update_authority(new_owner) *)
        (*     .invoke()?; *)

        (* // Step 3: Automatic sync_owner *)
        (* let agent = &mut ctx.accounts.agent_account; *)
        (* let old_owner = agent.owner; *)
        (* agent.owner = new_owner; *)

        (* emit!(AgentOwnerSynced { *)
        (*     agent_id: agent.agent_id, *)
        (*     old_owner, *)
        (*     new_owner, *)
        (*     agent_mint: agent.agent_mint, *)
        (* }); *)

        (* msg!( *)
        (*     "Agent {} transferred: {} -> {}", *)
        (*     agent.agent_id, *)
        (*     old_owner, *)
        (*     new_owner *)
        (* ); *)

        Result.Ok ctx.
End identity_registry.
