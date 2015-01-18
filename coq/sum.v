Require Import List.
Require Import Coq.Arith.Arith_base.
Import ListNotations.
Require Import NAxioms NSub NZDiv.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition natSum (n : nat) : nat :=
  (n * (n + 1)) / 2.

Fixpoint downFrom (n:nat) : list nat :=
  match n with
    | 0 => [0]
    | S x => S x :: downFrom x
  end.

Eval compute in downFrom 10.

Fixpoint regularSum (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => n + regularSum n'
  end.

Theorem natSum_S : forall (n : nat),
                     natSum (S n) = S n + natSum n.
Proof.
  intros n.
  unfold natSum.
  replace (S n) with (n + 1).

  rewrite <- Nat.div_add_l.
  replace ((n + 1) * (n + 1 + 1)) with ((n + 1) * 2 + (n * (n + 1))).
  reflexivity.

  rewrite <- plus_assoc.
  simpl.
  replace (n * (n + 1)) with ((n + 1) * n).
  rewrite <- mult_plus_distr_l.
  replace (2 + n) with (n + 2).
  reflexivity.

  rewrite plus_comm.
  reflexivity.

  rewrite mult_comm.
  reflexivity.

  auto.
  apply Nat.add_1_r.
Qed.

Theorem regularSum__natSum : forall (n : nat),
  natSum n = regularSum n.
Proof.
  induction n.
  compute.
  reflexivity.

  unfold regularSum.
  fold regularSum.
  rewrite <- IHn.
  apply natSum_S.
Qed.