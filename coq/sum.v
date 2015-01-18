Require Import List.
Require Import Coq.Arith.Arith_base.
Import ListNotations.
Require Import NAxioms NSub NZDiv.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition natSum (n : nat) : nat :=
  (n * (n + 1)) / 2.

Check fold_right.

Fixpoint downFrom (n:nat) : list nat :=
  match n with
    | 0 => [0]
    | S x => S x :: downFrom x
  end.

Definition regularSum (n : nat) : nat :=
  fold_right (plus) 0 (downFrom n).

Theorem regularSum__natSum : forall (n : nat),
  natSum n = regularSum n.
Proof.
  induction n.
  compute.
  reflexivity.

  unfold regularSum.
  simpl.
  unfold regularSum in IHn.

  unfold natSum.
  unfold natSum in IHn.
  rewrite <- IHn.
  
  rewrite mult_succ_l.
  
  rewrite add_1_r.
  rewrite mult_succ_r.