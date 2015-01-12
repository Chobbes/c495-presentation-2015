Require Import List.
Require Import Coq.Arith.Arith_base.
Import ListNotations.
Require Import Recdef.
  
Fixpoint Partition (x : nat) (l : list nat) :=
  match l with
    | nil => (nil, nil)
    | h :: t => match (Partition x t) with
                  | (less, greater) => if (lt_dec h x) then
                                         (h :: less, greater)
                                       else
                                         (less, h :: greater)
                end
  end.
                    

Fixpoint min (l : list nat) :=
  match l with
    | nil => 0
    | h :: t => let min_rest := min t
                in if lt_dec min_rest h
                   then min_rest
                   else h
  end.

Fixpoint less_than_all (x : nat) (l : list nat) :=
  match l with
    | nil => True
    | h :: t => if lt_dec h x
                then False
                else less_than_all x t
  end.


Lemma zero_less : forall (n : nat),
  0 < S n.
Proof.
  induction n.
    unfold lt.
    trivial.
  inversion IHn.
  unfold lt.
  
Qed.


Function SortList (l : list nat) {measure length l} : list nat :=
  match l with
    | nil => nil
    | h :: t => let (less, greater) := (Partition h t) in
          (SortList less) ++ [h] ++ (SortList greater)
  end.

Proof.
  intros l h t l_ht less greater.
  induction t.
  simpl.
  intros.
  inversion teq0.
  simpl.
  apply gt_Sn_0.
Qed.