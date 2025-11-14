From Excalead Require Import Excalead.

Require Import Anchor_lang.

(* (**  Monadic bind for propositions, checking that there are no internal errors. *) *)
(*  Definition bind_prop {a : Set} (x : M? a) (f : a → Prop) : Prop := *)
(*   match x with *)
(*   | Pervasives.Ok x ⇒ f x *)
(*   | Pervasives.Error err ⇒ Error.not_internal err *)
(*   end. *)
(**)
(*  (** Monadic bind for propositions, checking that there are no errors (either internal or user-related). *) *)
(* Definition bind_prop_strict {a : Set} (x : M? a) (f : a → Prop) : Prop := *)
(*   match x with *)
(*   | Pervasives.Ok x ⇒ f x *)
(*   | Pervasives.Error err ⇒ False *)
(*   end. *)
(**)
(* (** Monadic bind for propositions, allowing any kinds of errors (including internal errors). Ideally, we should not need this combinator. It is there mainly for historical reasons. *) *)
(* Definition bind_prop_relaxed {a : Set} (x : M? a) (f : a → Prop) : Prop := *)
(*   match x with *)
(*   | Pervasives.Ok x ⇒ f x *)
(*   | Pervasives.Error err ⇒ True *)
(*   end. *)
(**)
(* Notation "'letP?' x ':=' X 'in' Y" := *)
(*   (bind_prop X (fun x => Y)) *)
(*   (at level 200, x name, X at level 100, Y at level 200). *)
(**)
(* Notation "'letP?' ' x ':=' X 'in' Y" := *)
(*   (bind_prop X (fun x ⇒ Y)) *)
(*   (at level 200, x pattern, X at level 100, Y at level 200). *)
(**)
(* Notation "'letP?!' x ':=' X 'in' Y" := *)
(*   (bind_prop_strict X (fun x ⇒ Y)) *)
(*   (at level 200, x name, X at level 100, Y at level 200). *)
(**)
(* Notation "'letP?!' ' x ':=' X 'in' Y" := *)
(*   (bind_prop_strict X (fun x ⇒ Y)) *)
(*   (at level 200, x pattern, X at level 100, Y at level 200). *)
(**)
(* Notation "'letP?relaxed' x ':=' X 'in' Y" := *)
(*   (bind_prop_relaxed X (fun x ⇒ Y)) *)
(*   (at level 200, x name, X at level 100, Y at level 200). *)
(**)
(* Notation "'letP?relaxed' ' x ':=' X 'in' Y" := *)
(*   (bind_prop_relaxed X (fun x ⇒ Y)) *)
(*   (at level 200, x pattern, X at level 100, Y at level 200). *)

(** Destruct the matched value in an expression [e]. *)
Ltac destruct_match_in e :=
  lazymatch e with
  | let? _ := ?e in _ =>
    unfold Result.bind at 1;
    destruct_match_in e
  | match ?e with | _ => _ end =>
    destruct_match_in e
  | context[let? _ := ?e in _] =>
    destruct_match_in e
  | context[match ?e with | _ => _ end] =>
    destruct_match_in e
  | _ =>
    destruct e eqn:?
  end.

Ltac deconstruct_require :=
  let H := fresh "H" in
  match goal with
  | H: require ?cond _ = Result.Ok ?res |- _ =>
    assert (cond = true); [
      unfold require in H;
      destruct cond; [ reflexivity | discriminate ] |];
    clear H res
  | H: require ?cond _ = Result.Err ?res |- _ =>
    assert (cond = false); [
      unfold require in H;
      destruct cond; [ discriminate | reflexivity  ] |];
    clear H res
  end.

Ltac clear_units :=
  repeat match goal with
    | u: unit |- _ => destruct u
    end.

(** Destruct one matched value in the goal. *)
Ltac step :=
  match goal with
  | |- context[match ?e with | _ => _ end] =>
    destruct_match_in e
  | |- context[let? _ := ?e in _] =>
    destruct_match_in e
  end; try tauto; try deconstruct_require;
  clear_units.

