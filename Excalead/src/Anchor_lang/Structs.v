(* Definitions in this module will probably be separated between multiple files
   with this library's growth. *)

Require Import Traits Base.

Require Import Excalead.Excalead.

Module IsWritable.
  Inductive t : Set := Yes | No.
End IsWritable.

Module IsSigner.
  Inductive t : Set := Yes | No.
End IsSigner.

Module IsOptional.
  Inductive t : Set := Yes | No.
End IsOptional.

Module Account.
  Parameter t : IsWritable.t -> IsSigner.t -> IsOptional.t -> option Z -> option unit -> Set.
End Account.
Export Account.

Module UncheckedAccount.
  Parameter t : Set.

  Parameter ToAccountInfo_UncheckedAccount : ToAccountInfo UncheckedAccount.t.
  #[export] Existing Instance ToAccountInfo_UncheckedAccount.
End UncheckedAccount.
Export UncheckedAccount.

Module Signer.
  Parameter t : Set.

  Parameter lamports : forall (self : Signer.t), u64.

  Parameter Key_Signer : Key Signer.t.
  #[export] Existing Instance Key_Signer.

  Parameter ToAccountInfo_Signer : ToAccountInfo Signer.t.
  #[export] Existing Instance ToAccountInfo_Signer.
End Signer.
Export Signer.

Module System.
  Parameter t : Set.

  Parameter ToAccountInfo_System : ToAccountInfo System.t.
  #[export] Existing Instance ToAccountInfo_System.
End System.
Export System.

Module Context.
  Record t {Accounts : Set} : Set := {
    (* program : AccountInfo; *)
    accounts : Accounts;
  }.
  Arguments t : clear implicits.

  Parameter new : forall {Accounts : Set},
    AccountInfo.t -> Accounts -> Context.t Accounts.
End Context.
Export Context.

Module SystemProgram.
  Module Transfer.
    Record t : Set := {
      from : AccountInfo.t;
      to : AccountInfo.t;
    }.
  End Transfer.

  Parameter transfer : forall {Accounts : Set},
    Context.t Accounts -> u64 -> Result.t unit.
End SystemProgram.

Module Clock.
  Record t : Set := {
    unix_timestamp : u64;
  }.

  Parameter get : Result.t t.
End Clock.

