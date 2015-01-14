Theorem plus_associative : forall (a b c : nat),
                             a + (b + c) = (a + b) + c.
Proof.
  induction a.
  simpl.
  reflexivity.

  simpl.
  intros.
  rewrite IHa.
  reflexivity.
Qed.
