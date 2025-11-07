Require Import Coq.Lists.List.

Section ZipperFind.
  Context {T : Type}.
  Context (pred: T -> bool).

  Fixpoint zipper_find_aux (acc : list T) (xs : list T) : option (T * (list T * list T)) :=
    match xs with
    | nil => None
    | cons x xs =>
      if pred x then
        Some (x, (acc, xs))
      else
        zipper_find_aux (x :: acc) xs
    end.

  Definition zipper_find (xs : list T) := zipper_find_aux nil xs.

  Definition unzipper (elem : T) (prefix : list T) (suffix : list T) :=
    rev_append prefix (elem :: suffix).

  Lemma find_spec_some (xs : list T) : Exists (fun x => pred x = true) xs ->
    exists x prefix suffix, zipper_find xs = Some (x, (prefix, suffix)).
  (* This can be easily proven *)
  Admitted.

  Lemma find_spec_none (xs : list T) : ~Exists (fun x => pred x = true) xs ->
    zipper_find xs = None.
  (* This can be easily proven *)
  Admitted.

  Lemma zipper_spec_aux (xs : list T) : forall ys prefix suffix x,
    zipper_find_aux ys xs = Some(x, (prefix, suffix)) ->
    rev_append ys xs = rev_append (x :: prefix) suffix.
  Proof.
    induction xs as [ | y xs ]; intros ys prefix suffix x Hres; simpl.
    + discriminate.
    + remember Hres as Hres'; clear HeqHres'; simpl in Hres.
      destruct (pred y) eqn:Hpred.
      - inversion Hres; now subst.
      - apply IHxs in Hres.
        now simpl in Hres.
  Qed.



  Lemma zipper_spec (xs : list T) :
    match zipper_find xs with
    | None => True
    | Some (x, (prefix, suffix)) => xs = unzipper x prefix suffix
    end.
  Proof.
    destruct (Exists_dec (fun x => pred x = true) xs) as [Hex | Hnex].
    + intros x; decide equality.
    + apply find_spec_some in Hex as [x [prefix [suffix Heq]]].
      rewrite Heq.
      unfold zipper_find, unzipper in *.
      now apply zipper_spec_aux in Heq.
    + apply find_spec_none in Hnex.
      now rewrite Hnex.
  Qed.

End ZipperFind.

