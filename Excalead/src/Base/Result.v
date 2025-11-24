Require Export Coq.Strings.String.

Inductive t (A : Set) :=
| Ok : A -> t A
| Err : string -> t A.
Arguments Ok {A} _.
Arguments Err {A} _.

Definition bind {A B : Set} (result : t A) (f : A -> t B) : t B :=
  match result with
  | Ok a => f a
  | Err e => Err e
  end.

Notation "'let?' x ':=' e 'in' k" :=
  (Result.bind e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

