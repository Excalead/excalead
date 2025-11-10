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

  Lemma find_spec_some_aux (xs : list T) : Exists (fun x => pred x = true) xs ->
    forall ys, Forall (fun y => pred y = false) ys ->
    exists x prefix suffix,
      zipper_find_aux ys xs = Some (x, (prefix, suffix)) /\
      Forall (fun y => pred y = false) prefix.
  Proof.
    intros HEx.
    induction xs as [| x xs ]; [ inversion HEx |]; intros ys HysFa.
    destruct (pred x) eqn:Hpred;
     [| apply Exists_exists in HEx as [x' [[Heq|HIn] Hpred']] ].
    + exists x, ys, xs; cbv.
      split; [ now rewrite Hpred | assumption ].
    + subst.
      exists x', ys, xs; cbv.
      split; [ now rewrite Hpred' | assumption ].
    + edestruct IHxs as [y [prefix [suffix [Heq HFa]]]].
      - apply Exists_exists.
        eexists; eauto.
      - apply Forall_cons; eassumption.
      - exists y, prefix, suffix; cbv; fold zipper_find_aux.
        split; [ rewrite Hpred | ]; assumption.
  Qed.


  Lemma find_spec_some (xs : list T) : Exists (fun x => pred x = true) xs ->
    exists x prefix suffix,
      zipper_find xs = Some (x, (prefix, suffix)) /\
      Forall (fun y => pred y = false) prefix.
  Proof.
    intros HEx.
    apply find_spec_some_aux; [ assumption | constructor ].
  Qed.

  Lemma find_spec_none_aux (xs : list T) :
    Forall (fun y => pred y <> true) xs ->
    forall ys, Forall (fun y => pred y = false) ys ->
    zipper_find_aux ys xs = None.
  Proof.
    induction xs as [| x xs ]; intros HxsFa ys HysFa; [ reflexivity |].
    inversion HxsFa; subst; cbv; fold zipper_find_aux.
    match goal with
    | Hpred: pred x <> true |- _ =>
        apply Bool.not_true_is_false in Hpred; rewrite Hpred
    end.
    apply IHxs; auto.
  Qed.


  Lemma find_spec_none (xs : list T) : ~Exists (fun x => pred x = true) xs ->
    zipper_find xs = None /\ Forall (fun x => pred x = false) xs.
  Proof.
    intros HnEx.
    apply Forall_Exists_neg in HnEx.
    split.
    + apply find_spec_none_aux; [ assumption | constructor ].
    + apply Forall_forall; rewrite Forall_forall in HnEx.
      intros x HIn.
      apply Bool.not_true_is_false, HnEx, HIn.
  Qed.

  Lemma zipper_spec_aux (xs : list T) : forall ys prefix suffix x,
    zipper_find_aux ys xs = Some(x, (prefix, suffix)) ->
    rev_append ys xs = rev_append (x :: prefix) suffix /\
        pred x = true.
  Proof.
    induction xs as [ | y xs ]; intros ys prefix suffix x Hres; simpl.
    + discriminate.
    + remember Hres as Hres'; clear HeqHres'; simpl in Hres.
      destruct (pred y) eqn:Hpred.
      - inversion Hres; subst.
        repeat split; try assumption.
      - apply IHxs in Hres.
        now simpl in Hres.
  Qed.

  Lemma zipper_spec (xs : list T) :
    match zipper_find xs with
    | None => Forall (fun x => pred x = false) xs
    | Some (x, (prefix, suffix)) =>
        xs = unzipper x prefix suffix /\
        pred x = true /\
        Forall (fun x => pred x = false) prefix
    end.
  Proof.
    destruct (Exists_dec (fun x => pred x = true) xs) as [Hex | Hnex].
    + intros x; decide equality.
    + apply find_spec_some in Hex as [x [prefix [suffix [Heq HFa]]]].
      rewrite Heq.
      unfold zipper_find, unzipper in *.
      apply zipper_spec_aux in Heq as [Hres Hpred].
      repeat split; try assumption.
    + apply find_spec_none in Hnex as [Heq HFa].
      rewrite Heq; apply HFa.
  Qed.

End ZipperFind.

