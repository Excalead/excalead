From Excalead Require Import Excalead.

Module Hash.
  Record t : Set := {
    value : u32;
  }.

  #[export]
  Instance Hash_JEncode : JEncode Hash.t :=
    fun x => JSON__Object [("Hash", encode x.(value))].
  #[export]
  Instance Hash_JDecode : JDecode Hash.t := 
    fun j => match j with
      | JSON__Object [("Hash", hash_json)] =>
        decode hash_json >>= fun hash =>
        inr {| value := hash |}
      | _ =>
        inl "Failed to decode Hash"
      end.

  #[export]
  Instance Hash_EqDec : EqDec Hash.t :=
    fun a b => a.(value) == b.(value).

End Hash.
Export (hints) Hash.

Module AccountInfo.
  Parameter t : Set.
End AccountInfo.
Export (hints) AccountInfo.

Module Pubkey.
  Record t : Set := {
    value : string;
  }.

  #[export]
  Instance Pubkey_JEncode : JEncode Pubkey.t :=
    fun x => JSON__Object [("Pubkey", encode x.(value))].
  #[export]
  Instance Pubkey_JDecode : JDecode Pubkey.t := 
    fun j => match j with
      | JSON__Object [("Pubkey", pubkey_json)] =>
        decode pubkey_json >>= fun pubkey =>
        inr {| value := pubkey |}
      | _ =>
        inl "Failed to decode Pubkey"
      end.

  #[export]
  Instance Pubkey_EqDec : EqDec Pubkey.t :=
    fun a b => a.(value) == b.(value).

End Pubkey.
Export (hints) Pubkey.

Module bytes.
  Parameter t : Set.
End bytes.
Export (hints) bytes.

