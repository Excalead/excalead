From Excalead Require Import Excalead Anchor_lang Anchor_spl.
From Excalead.examples.quantu_8004 Require Import error events state.

Parameter IDENTITY_REGISTRY_ID : Pubkey.t.

Module Initialize.
  Record t : Set := {
    config : ValidationConfig.t;
    authority : Signer.t;
    system_program : System.t;
  }.
End Initialize.

Module RequestValidation.
  Record t : Set := {
    config : ValidationConfig.t;
    requester : Signer.t;
    payer : Signer.t;
    agent_mint : UncheckedAccount.t;
    agent_account : UncheckedAccount.t;
    token_account : TokenAccount.t;
    validation_request : ValidationRequest.t;
    identity_registry_program : UncheckedAccount.t;
    system_program : System.t;
  }.

  Parameters stored_agent_id_of_agent_account :
    forall (agent_account : UncheckedAccount.t), Result.t u64.
End RequestValidation.

Module RespondToValidation.
  Record t : Set := {
    config : ValidationConfig.t;
    validator : Signer.t;
    validation_request : ValidationRequest.t;
  }.
End RespondToValidation.

Module CloseValidation.
  Record t : Set := {
    config : ValidationConfig.t;
    closer : Signer.t;
    agent_mint : UncheckedAccount.t;
    agent_account : UncheckedAccount.t;
    token_account : TokenAccount.t;
    validation_request : ValidationRequest.t;
    identity_registry_program : UncheckedAccount.t;
    rent_receiver : SystemAccount.t;
  }.
End CloseValidation.

Module validation_registry.
  Definition initialize
      (ctx : Initialize.t)
      (identity_registry : Pubkey.t) :
      Result.t Initialize.t :=
    let config := ctx.(Initialize.config) in

    let config := config
      <| ValidationConfig.authority := key ctx.(Initialize.authority) |>
      <| ValidationConfig.identity_registry := identity_registry |>
      <| ValidationConfig.total_requests := 0 |>
      <| ValidationConfig.total_responses := 0 |> in
    let ctx := ctx <| Initialize.config := config |> in

    msg! "Validation Registry initialized" in
    msg! ("Identity Registry: {}", identity_registry) in

    Result.Ok ctx.

  Definition request_validation
      (ctx : RequestValidation.t)
      (agent_id : u64)
      (validator_address : Pubkey.t)
      (nonce : u32)
      (request_uri : string)
      (request_hash : Hash.t) :
      Result.t RequestValidation.t :=
    require!
      (Z.of_nat (String.length request_uri) <=i ValidationRequest.MAX_URI_LENGTH) with
      ValidationError.RequestUriTooLong in

    let agent_data := ctx.(RequestValidation.agent_account) in

    require!
      (AccountInfo.len (to_account_info agent_data) >=i 8 + 8) with
      ValidationError.AgentNotFound in

    let? stored_agent_id :=
      match RequestValidation.stored_agent_id_of_agent_account agent_data with
      | Result.Ok stored_agent_id => Result.Ok stored_agent_id
      | Result.Err error => Result.error ValidationError.AgentNotFound
      end in

    require! (stored_agent_id =i agent_id) with ValidationError.AgentNotFound in

    require!
      (TokenAccount.owner ctx.(RequestValidation.token_account) == key ctx.(RequestValidation.requester)) with
      ValidationError.UnauthorizedRequester in

    let? clock := Clock.get in

    let validation_request := ctx.(RequestValidation.validation_request) in
    let validation_request := validation_request
      <| ValidationRequest.agent_id := agent_id |>
      <| ValidationRequest.validator_address := validator_address |>
      <| ValidationRequest.nonce := nonce |>
      <| ValidationRequest.request_hash := request_hash |>
      <| ValidationRequest.response_hash := Hash.zero |>
      <| ValidationRequest.response := 0 |>
      <| ValidationRequest.created_at := clock.(Clock.unix_timestamp) |>
      <| ValidationRequest.responded_at := 0 |> in
    let ctx := ctx <| RequestValidation.validation_request := validation_request |> in

    let config := ctx.(RequestValidation.config) in
    let? config_total_requests :=
      match BinOp.Checked.add config.(ValidationConfig.total_requests) 1 with
      | Some config_total_requests => Result.Ok config_total_requests
      | None => Result.error ValidationError.Overflow
      end in
    let config := config <| ValidationConfig.total_requests := config_total_requests |> in
    let ctx := ctx <| RequestValidation.config := config |> in

    emit! {|
      ValidationRequested.agent_id := agent_id;
      ValidationRequested.validator_address := validator_address;
      ValidationRequested.nonce := nonce;
      ValidationRequested.request_uri := request_uri;
      ValidationRequested.request_hash := request_hash;
      ValidationRequested.requester := key ctx.(RequestValidation.requester);
      ValidationRequested.created_at := clock.(Clock.unix_timestamp);
    |} in

    msg! ("Validation requested for agent #{} by validator {}", agent_id, validator_address) in

    Result.Ok ctx.

  Definition respond_to_validation
      (ctx : RespondToValidation.t)
      (response : u8)
      (response_uri : string)
      (response_hash : Hash.t)
      (tag : string) :
      Result.t RespondToValidation.t :=
    require! (response <=i 100) with ValidationError.InvalidResponse in

    require!
      (Z.of_nat (String.length response_uri) <=i ValidationRequest.MAX_URI_LENGTH) with
      ValidationError.ResponseUriTooLong in

    let? clock := Clock.get in

    let validation_request := ctx.(RespondToValidation.validation_request) in

    let is_first_response := validation_request.(ValidationRequest.responded_at) =i 0 in

    let validation_request := validation_request
      <| ValidationRequest.response := response |>
      <| ValidationRequest.response_hash := response_hash |>
      <| ValidationRequest.responded_at := clock.(Clock.unix_timestamp) |> in
    let ctx := ctx <| RespondToValidation.validation_request := validation_request |> in

    let config := ctx.(RespondToValidation.config) in
    let? config :=
      if is_first_response then
        match BinOp.Checked.add config.(ValidationConfig.total_responses) 1 with
        | Some total_responses => Result.Ok (
           config <| ValidationConfig.total_responses := total_responses |>
          )
        | None => Result.error ValidationError.Overflow
        end
      else
        Result.Ok config in
    let ctx := ctx <| RespondToValidation.config := config |> in

    emit! {|
      ValidationResponded.agent_id := validation_request.(ValidationRequest.agent_id);
      ValidationResponded.validator_address := validation_request.(ValidationRequest.validator_address);
      ValidationResponded.nonce := validation_request.(ValidationRequest.nonce);
      ValidationResponded.response := response;
      ValidationResponded.response_uri := response_uri;
      ValidationResponded.response_hash := response_hash;
      ValidationResponded.tag := tag;
      ValidationResponded.responded_at := clock.(Clock.unix_timestamp);
    |} in

    msg! (
      "Validator {} responded to agent #{} with score {}",
      key ctx.(RespondToValidation.validator),
      validation_request.(ValidationRequest.agent_id),
      response
    ) in

    Result.Ok ctx.

  Definition update_validation
      (ctx : RespondToValidation.t)
      (response : u8)
      (response_uri : string)
      (response_hash : Hash.t)
      (tag : string) :
      Result.t RespondToValidation.t :=
    respond_to_validation ctx response response_uri response_hash tag.

  Definition close_validation
      (ctx : CloseValidation.t) :
      Result.t CloseValidation.t :=
    let is_agent_owner :=
      TokenAccount.owner ctx.(CloseValidation.token_account) == key ctx.(CloseValidation.closer) in
    let is_authority :=
      ctx.(CloseValidation.config).(ValidationConfig.authority) == key ctx.(CloseValidation.closer) in

    require! (is_agent_owner || is_authority) with ValidationError.Unauthorized in

    msg! "Validation request closed, rent recovered" in

    Result.Ok ctx.
End validation_registry.
