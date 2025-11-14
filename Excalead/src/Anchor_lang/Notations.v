From Excalead Require Import Excalead.

Definition require (condition : bool) (message : string) : Result.t unit :=
  if condition then
    Result.Ok tt
  else
    Result.Err message.

Notation "'require!' condition 'with' message 'in' k" :=
  (let? _ := require condition message in k)
  (at level 200, condition at level 200, message at level 200, k at level 200).

(** For now we consider messaging as a no-op *)
Definition msg (message : string) : Result.t unit :=
  Result.Ok tt.

Notation "'msg!' message 'in' k" :=
  (let? _ := msg message in k)
  (at level 200, message at level 200, k at level 200).


