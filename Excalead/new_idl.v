Require Import Excalead.Excalead.

(** Constants *)
(* [116, 101, 115, 116] *)
Parameter BYTES_STR : bytes.

(* 116 *)
Parameter BYTE_STR : u8.

(* 1000000 *)
Parameter I128 : i128.

(* 6 *)
Parameter U8 : u8.

(** Error codes *)
Module ErrorCode.
  Inductive t : Set :=
  (** Example error. *)
  | SomeError : t
  (** Another error. *)
  | OtherError : t
  | ErrorWithoutMsg : t.
End ErrorCode.

(** Custom types *)
Module external.
Module MyStruct.
  Record t : Set := {
    some_field : u8;
  }.
End MyStruct.
End external.

Module idl.
Module some_other_module.
Module MyStruct.
  Record t : Set := {
    some_u8 : u8;
  }.
End MyStruct.
End some_other_module.
End idl.

Module BarStruct.
  Record t : Set := {
    some_field : bool;
    other_field : u8;
  }.
End BarStruct.

Module FooEnum.
  Inductive t : Set :=
  | Unnamed (_ : bool) (_ : u8) (_ : BarStruct.t)
  | UnnamedSingle (_ : BarStruct.t)
  | Named (bool_field : bool) (u8_field : u8) (nested : BarStruct.t)
  | Struct (_ : BarStruct.t)
  | OptionStruct (_ : option (BarStruct.t))
  | VecStruct (_ : list (BarStruct.t))
  | NoFields.
End FooEnum.

Module FooStruct.
  Record t : Set := {
    field1 : u8;
    field2 : u16;
    nested : BarStruct.t;
    vec_nested : list (BarStruct.t);
    option_nested : option (BarStruct.t);
    enum_field : FooEnum.t;
  }.
End FooStruct.

Module SomeEvent.
  Record t : Set := {
    bool_field : bool;
    external_my_struct : external.MyStruct.t;
    other_module_my_struct : idl.some_other_module.MyStruct.t;
  }.
End SomeEvent.

Module SomeRetStruct.
  Record t : Set := {
    some_field : u8;
  }.
End SomeRetStruct.

Module ZcStruct.
  Record t : Set := {
    some_field : u16;
  }.
End ZcStruct.

Module SomeZcAccount.
  Record t : Set := {
    field : ZcStruct.t;
  }.
End SomeZcAccount.

Module State.
  Record t : Set := {
    bool_field : bool;
    u8_field : u8;
    i8_field : i8;
    u16_field : u16;
    i16_field : i16;
    u32_field : u32;
    i32_field : i32;
    f32_field : f32;
    u64_field : u64;
    i64_field : i64;
    f64_field : f64;
    u128_field : u128;
    i128_field : i128;
    bytes_field : bytes;
    string_field : string;
    pubkey_field : Pubkey;
    vec_field : list (u64);
    vec_struct_field : list (FooStruct.t);
    option_field : option (bool);
    option_struct_field : option (FooStruct.t);
    struct_field : FooStruct.t;
    array_field : list (bool) (* [3; 3] *);
    enum_field_1 : FooEnum.t;
    enum_field_2 : FooEnum.t;
    enum_field_3 : FooEnum.t;
    enum_field_4 : FooEnum.t;
  }.
End State.

Module State2.
  Record t : Set := {
    vec_of_option : list (option (u64));
    box_field : bool;
  }.
End State2.

(** Account structures *)
Module AccountStructure.
  Inductive t : Set :=
  | SomeZcAccount : t
  | State : t
  | State2 : t.
End AccountStructure.

(** Instruction contexts *)
Module Instruction.
  Inductive t : Set -> Set :=
  | cause_error
    (* Accounts *)
    (* Arguments *)
    (* Return *)
      : t unit
  | initialize
    (* Accounts *)
      (state : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        None
        None
      )
      (* TODO: composite accounts *)
      (zc_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (token_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (mint_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (token_interface_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (mint_interface_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (payer : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        None
        None
      )
      (system_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Some 11111111111111111111111111111111)
        None
      )
    (* Arguments *)
    (* Return *)
      : t unit
  | initialize_with_values
    (* Accounts *)
      (state : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        None
        None
      )
      (* TODO: composite accounts *)
      (zc_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (token_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (mint_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (token_interface_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (mint_interface_account : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        None
        None
      )
      (payer : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        None
        None
      )
      (system_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Some 11111111111111111111111111111111)
        None
      )
    (* Arguments *)
      (bool_field : bool)
      (u8_field : u8)
      (i8_field : i8)
      (u16_field : u16)
      (i16_field : i16)
      (u32_field : u32)
      (i32_field : i32)
      (f32_field : f32)
      (u64_field : u64)
      (i64_field : i64)
      (f64_field : f64)
      (u128_field : u128)
      (i128_field : i128)
      (bytes_field : bytes)
      (string_field : string)
      (pubkey_field : Pubkey)
      (vec_field : list (u64))
      (vec_struct_field : list (FooStruct.t))
      (option_field : option (bool))
      (option_struct_field : option (FooStruct.t))
      (struct_field : FooStruct.t)
      (array_field : list (bool) (* [3; 3] *))
      (enum_field_1 : FooEnum.t)
      (enum_field_2 : FooEnum.t)
      (enum_field_3 : FooEnum.t)
      (enum_field_4 : FooEnum.t)
    (* Return *)
      : t unit
  | initialize_with_values2
    (* Accounts *)
      (state : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        None
        None
      )
      (payer : Account.t
        IsWritable.Yes
        IsSigner.Yes
        IsOptional.No
        None
        None
      )
      (system_program : Account.t
        IsWritable.No
        IsSigner.No
        IsOptional.No
        (Some 11111111111111111111111111111111)
        None
      )
    (* Arguments *)
      (vec_of_option : list (option (u64)))
      (box_field : bool)
    (* Return *)
       : t SomeRetStruct.t.
End Instruction.

