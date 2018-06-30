Require Import Omega.
Require Import Nat.
Require Import ZArith.
Require Import Ring.
Require Import List.
Require Import Ncring.
Require Import Ring_tac.
Require Import FunctionalExtensionality.
Require Import Maps.

Definition option_bind
           {A B: Type}
           (oa: option A)
           (f: A -> option B) : option B :=
  match oa with
  | None => None
  | Some a => f a
  end.

Infix ">>=" := option_bind (at level 100).