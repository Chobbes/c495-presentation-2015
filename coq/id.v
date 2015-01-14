Theorem id : forall A, A -> A.
Proof.
  trivial.
Qed.

Definition id1 (A : Type) (x : A) : A :=
  x.

Check id.
Check id1.

Theorem id2 : forall A, A -> A.
  apply id1.
Qed.
