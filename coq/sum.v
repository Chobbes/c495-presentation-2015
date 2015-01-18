Require Import List.
Require Import Coq.Arith.Arith_base.
Import ListNotations.
Require Import NAxioms NSub NZDiv.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Require Import Coq.Numbers.Natural.Peano.NPeano.

(* Definition for a sum from 1..n *)
Definition natSum (n : nat) : nat :=
  (n * (n + 1)) / 2.

(* We could also write this recursively, but this is obviously less efficient. *)
Fixpoint regularSum (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => n + regularSum n' (* Match the natural number with a successor of a nat *)
  end.

(* Note that these compute the same values... *)
Eval compute in natSum 10.
Eval compute in regularSum 10.

(* So, maybe we should show that these two definitions are actually equivalent! *)

(* First let's start with a lemma. Sum from 1 to S n (successor, or n + 1) is the same as
   The S n plus the sum from 1 to n.
*)

Lemma natSum_S : forall (n : nat),
                     natSum (S n) = S n + natSum n.
Proof.
  intros n.  (* Introduce our variable n *)
  unfold natSum.  (* replace natSum with its definition *)

  (* We'll change all of the successors to addition with 1 *)
  (* Replacement will gives us an extra goal, because we have to prove that S n = n + 1 later *)
  replace (S n) with (n + 1).

  (* Move the addition on the right hand side into the division. This requires
     that the denomenator is non-zero, so that's added as a goal as well.
  *)
  rewrite <- Nat.div_add_l.

  (* Now we replace the numerator to make them equal. We have to show that this
     replacement is valid too, so another goal is added.
  *)
  replace ((n + 1) * (n + 1 + 1)) with ((n + 1) * 2 + (n * (n + 1))).
  reflexivity. (* Reflexivity finishes the current goal. *)

  (* We will use associativity, and simplification to show that n + 1 + 1 = n + 2 *)
  rewrite <- plus_assoc.
  simpl.

  (* Commute one particular term -- adds a goal *)
  replace (n * (n + 1)) with ((n + 1) * n).
  rewrite <- mult_plus_distr_l.  (* Use distribution principle *)
  replace (2 + n) with (n + 2).  (* Commutativity of addition of a specific term *)
  reflexivity.  (* Now both sides are equal, so we can use reflexivity to finish *)

  (* This is solved with commutativity of addition *)
  apply plus_comm.

  (* This is just commutativity of multiplication *)
  apply mult_comm.

  (* Coq can automatically solve this *)
  auto.

  (* And this is an existing theorem too! *)
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