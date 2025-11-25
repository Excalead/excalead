Require Export Coq.PArith.BinPosDef.
Require Export Coq.Strings.PrimString.
Require Export Coq.ZArith.ZArith.

Require Export Utility.RecordUpdate.
Require Export Base.Classes Base.Nums Base.Result.

Require Utility.Vector.

Require Export Lia.
From Hammer Require Export Tactics.
Require Export smpl.Smpl.
From JSON Require Export JSON Encode Decode.

(* Activate the modulo arithmetic in [lia] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope type_scope.
Global Open Scope bool_scope.
Global Open Scope pstring_scope.
Global Open Scope string_scope.
Global Open Scope Z_scope.

Export List.ListNotations.

Module Vector.
  Include Utility.Vector.
End Vector.
