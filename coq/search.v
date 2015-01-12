Require Import List.
Require Import Coq.Arith.Arith_base.
Import ListNotations.
Require Import Recdef.
Require Import Coq.Classes.EquivDec.


Inductive NatTree : Type :=
  | Leaf : NatTree
  | Node : NatTree -> nat -> NatTree -> NatTree.


Definition maxNat (a : nat) (b : nat) : nat :=
  if ge_dec a b then a else b.

Definition minNat (a : nat) (b : nat) : nat :=
  if ge_dec a b then b else a.

Fixpoint max (t : NatTree) : option nat :=
  match t with
    | Leaf => None
    | Node lTree v rTree => Some
                              match max lTree with
                                | None => match max rTree with
                                            | None => v
                                            | Some rMax => maxNat rMax v
                                          end
                                | Some lMax => match max rTree with
                                                 | None => maxNat lMax v
                                                 | Some rMax => maxNat v (maxNat lMax rMax)
                                               end
                              end
  end.

Fixpoint min (t : NatTree) : option nat :=
  match t with
    | Leaf => None
    | Node lTree v rTree => Some
                              match min lTree with
                                | None => match min rTree with
                                            | None => v
                                            | Some rMin => minNat rMin v
                                          end
                                | Some lMin => match min rTree with
                                                 | None => minNat lMin v
                                                 | Some rMin => minNat v (minNat lMin rMin)
                                               end
                              end
  end.

Definition opt_le (o : option nat) (n : nat) : Prop :=
  match o with
    | None => True
    | Some x => x <= n
  end.


Definition opt_ge (o : option nat) (n : nat) : Prop :=
  match o with
    | None => True
    | Some x => x >= n
  end.
  
Inductive SearchTree : NatTree -> Prop :=
  | LeafSearch : SearchTree Leaf
  | NodeSearch : forall (n : nat) (lTree rTree : NatTree),
                   SearchTree lTree ->
                   SearchTree rTree ->
                   opt_ge (min rTree) n ->
                   opt_le (max lTree) n ->
                   SearchTree (Node lTree n rTree).

Theorem leaf__is_search :
  SearchTree Leaf.
Proof.
  apply LeafSearch.
Qed.  


Fixpoint insert (n : nat) (t : NatTree) : NatTree :=
  match t with
    | Leaf => Node Leaf n Leaf
    | Node leftTree v rightTree => if le_dec n v
                                   then Node (insert n leftTree) v rightTree
                                   else Node leftTree v (insert n rightTree)
  end.


Eval simpl in insert 2 (insert 1 Leaf).

(* 
  H6 : opt_le (max t1) n0
  H0 : lTree = t1
  H1 : n1 = n0
  H2 : rTree = t2
  ============================
   opt_le (max (insert n t1)) n0
 *)

Fixpoint insert_max t :
  forall (n n0 : nat),
    n <= n0 -> opt_le (max t) n0 -> opt_le (max (insert n t)) n0.
Proof.
  induction t.
  simpl.
  intros n n0 H1 H2.
  apply H1.

  intros n0 n1 H1 H2.
  simpl.
  destruct (le_dec n0 n).

  apply insert_max.
  apply H1.
  apply H2.
Qed.

Theorem insert__search :
  forall (t : NatTree) (n : nat),
    SearchTree t -> SearchTree (insert n t).
Proof.
  intros t n.
  induction t.
  simpl.
  intros H.
  apply NodeSearch.
  apply H.
  apply H.
  simpl.
  trivial.
  simpl.
  trivial.

  simpl.
  destruct (le_dec n n0).
  intros H.
  inversion H.
  apply NodeSearch.
  apply IHt1.
  apply H3.
  apply H4.
  apply H5.
  unfold opt_le.
Qed.

Fixpoint dfs (n : nat) (t : NatTree) : bool :=
  match t with
    | Leaf => false
    | Node leftTree v rightTree => if beq_nat v n
                                   then true
                                   else (dfs n leftTree) || (dfs n rightTree)
  end.

Fixpoint search (n : nat) (t : NatTree) : bool :=
  match t with
    | Leaf => false
    | Node leftTree v rightTree => if lt_dec n v
                                   then search n leftTree
                                   else if gt_dec n v
                                        then search n rightTree
                                        else true
  end.

Theorem dfs__search : forall (n : nat) (t : NatTree),
                        dfs n t = search n t.
Proof.
  intros n t.
  induction t.
    simpl.
    reflexivity.

    induction n.
    induction n0.
    simpl.
    reflexivity.

    simpl.
    