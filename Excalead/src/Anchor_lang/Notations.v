From Excalead Require Import Excalead.

Definition require {Error : Set} `{ToErrorString.C Error} (condition : bool) (error : Error) :
    Result.t unit :=
  if condition then
    Result.Ok tt
  else
    Result.error error.

Notation "'require!' condition 'with' message 'in' k" :=
  (let? _ := require condition message in k)
  (at level 200, condition at level 200, message at level 200, k at level 200).

(** For now we consider messaging as a no-op. We take any arguments, such that we can easily
    represent pretty-printing from the Rust side by directly giving any value in Rocq. *)
Definition msg {A : Set} (message : A) : Result.t unit :=
  Result.Ok tt.

Notation "'msg!' message 'in' k" :=
  (let? _ := msg message in k)
  (at level 200, message at level 200, k at level 200).

(** For now an event is a no-op. *)
Definition emit {Event : Set} (event : Event) : Result.t unit :=
  Result.Ok tt.

Notation "'emit!' event 'in' k" :=
  (let? _ := emit event in k)
  (at level 200, event at level 200, k at level 200).
