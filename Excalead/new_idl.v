Require Import Excalead.Excalead.

(** Constants *)
Definition BYTES_STR : bytes :=
  [116, 101, 115, 116].

Definition BYTE_STR : u8 :=
  116.

Definition I128 : i128 :=
  1000000.

Definition U8 : u8 :=
  6.

(** Error codes *)
Module ErrorCode.
  Inductive t : Set :=
  | SomeError (* Example error.) : string,
  | OtherError (* Another error.) : string,
  | ErrorWithoutMsg : string.
End ErrorCode.

(** Custom types *)
Module BarStruct.Record t : Set :={
  some_field : bool ;
  other_field : u8 .
}
End BarStruct.

Module FooEnum.Inductive t : Set :=
Unnamed |
UnnamedSingle |
Named |
Struct |
OptionStruct |
VecStruct |
NoFields.
End FooEnum.

Module FooStruct.Record t : Set :={
  field1 : u8 ;
  field2 : u16 ;
  nested : BarStruct ;
  vec_nested : list (BarStruct) ;
  option_nested : option (BarStruct) ;
  enum_field : FooEnum .
}
End FooStruct.

Module SomeEvent.Record t : Set :={
  bool_field : bool ;
  external_my_struct : external::MyStruct ;
  other_module_my_struct : idl::some_other_module::MyStruct .
}
End SomeEvent.

Module SomeRetStruct.Record t : Set :={
  some_field : u8 .
}
End SomeRetStruct.

Module SomeZcAccount.Record t : Set :={
  field : ZcStruct .
}
End SomeZcAccount.

Module State.Record t : Set :={
  bool_field : bool ;
  u8_field : u8 ;
  i8_field : i8 ;
  u16_field : u16 ;
  i16_field : i16 ;
  u32_field : u32 ;
  i32_field : i32 ;
  f32_field : f32 ;
  u64_field : u64 ;
  i64_field : i64 ;
  f64_field : f64 ;
  u128_field : u128 ;
  i128_field : i128 ;
  bytes_field : bytes ;
  string_field : string ;
  pubkey_field : Pubkey ;
  vec_field : list (u64) ;
  vec_struct_field : list (FooStruct) ;
  option_field : option (bool) ;
  option_struct_field : option (FooStruct) ;
  struct_field : FooStruct ;
  array_field : list (bool) (* [3; 3] *) ;
  enum_field_1 : FooEnum ;
  enum_field_2 : FooEnum ;
  enum_field_3 : FooEnum ;
  enum_field_4 : FooEnum .
}
End State.

Module State2.Record t : Set :={
  vec_of_option : list (option (u64)) ;
  box_field : bool .
}
End State2.

Module ZcStruct.Record t : Set :={
  some_field : u16 .
}
End ZcStruct.

Module external::MyStruct.Record t : Set :={
  some_field : u8 .
}
End external::MyStruct.

Module idl::some_other_module::MyStruct.Record t : Set :={
  some_u8 : u8 .
}
End idl::some_other_module::MyStruct.

(** Account structures *)
Module SomeZcAccount.Record t : Set :={
  field : ZcStruct .
}
End SomeZcAccount.

Module State.Record t : Set :={
  bool_field : bool ;
  u8_field : u8 ;
  i8_field : i8 ;
  u16_field : u16 ;
  i16_field : i16 ;
  u32_field : u32 ;
  i32_field : i32 ;
  f32_field : f32 ;
  u64_field : u64 ;
  i64_field : i64 ;
  f64_field : f64 ;
  u128_field : u128 ;
  i128_field : i128 ;
  bytes_field : bytes ;
  string_field : string ;
  pubkey_field : Pubkey ;
  vec_field : list (u64) ;
  vec_struct_field : list (FooStruct) ;
  option_field : option (bool) ;
  option_struct_field : option (FooStruct) ;
  struct_field : FooStruct ;
  array_field : list (bool) (* [3; 3] *) ;
  enum_field_1 : FooEnum ;
  enum_field_2 : FooEnum ;
  enum_field_3 : FooEnum ;
  enum_field_4 : FooEnum .
}
End State.

Module State2.Record t : Set :={
  vec_of_option : list (option (u64)) ;
  box_field : bool .
}
End State2.

(** Instruction contexts *)
Module cause_error.Record t : Set :={
}
End cause_error.

Module initialize.Record t : Set :={
  state : Signer.t ;
  (* TODO: composite accounts *)
  zc_account : Account.t TODO (* zc_account) ;
  token_account : Account.t TODO (* token_account) ;
  mint_account : Account.t TODO (* mint_account) ;
  token_interface_account : Account.t TODO (* token_interface_account) ;
  mint_interface_account : Account.t TODO (* mint_interface_account) ;
  payer : Signer.t ;
  system_program : Account.t TODO (* system_program) ;
}
End initialize.

Module initialize_with_values.Record t : Set :={
  state : Signer.t ;
  (* TODO: composite accounts *)
  zc_account : Account.t TODO (* zc_account) ;
  token_account : Account.t TODO (* token_account) ;
  mint_account : Account.t TODO (* mint_account) ;
  token_interface_account : Account.t TODO (* token_interface_account) ;
  mint_interface_account : Account.t TODO (* mint_interface_account) ;
  payer : Signer.t ;
  system_program : Account.t TODO (* system_program) ;
}
End initialize_with_values.

Module initialize_with_values2.Record t : Set :={
  state : Signer.t ;
  payer : Signer.t ;
  system_program : Account.t TODO (* system_program) .
}
End initialize_with_values2.

Module Result.
  Inductive t (A : Set) :=
  | Ok : A -> t A
  | Err : ErrorCode.t -> t A.
  Arguments Ok {A} _.
  Arguments Err {A} _.
End Result.

Module Context.
  Record t {Accounts Bumps : Set} : Set := {
    accounts : Accounts;
    bumps : Bumps;
  }.
  Arguments t : clear implicits.
End Context.

Module program.
  (* TODO: Implement instructions for idl)
  Definition cause_error (ctx : Context.t cause_error.t cause_errorBumps.t) : Result.t unit :=
    (* TODO *)
    Result.Ok tt.

  Definition initialize (ctx : Context.t initialize.t initializeBumps.t) : Result.t unit :=
    (* TODO *)
    Result.Ok tt.

  Definition initialize_with_values (ctx : Context.t initialize_with_values.t initialize_with_valuesBumps.t) : Result.t unit :=
    (* TODO *)
    Result.Ok tt.

  Definition initialize_with_values2 (ctx : Context.t initialize_with_values2.t initialize_with_values2Bumps.t) : Result.t unit :=
    (* TODO *)
    Result.Ok tt.

End program.
