Theorem plus_associative : forall (a b c : nat),
                             a + (b + c) = (a + b) + c.
Proof.
  intros a b c. (* Introduce a b and c. *)
  induction a.  (* Perform induction on a. This gives us two goals. One for the base case, and one for the induction hypothesis. *)
  
  simpl.        (* This is the base case. We should be able to simplify this expression some *)
  reflexivity.  (* This got rid of the 0 term, so we can finish the goal with reflexivity. *)

  (* Now we're in the second case. Need to show that given the induction hypothesis it's true for the successor to a *)
  simpl.        (* Again we can try to simplify. This does some basic evaluation, and tells us that S a + n is the same as S (a + n) *)
  rewrite IHa.  (* Notice that these aren't quite the same yet. The associativity is different. We can use the induction hypothesis to rewrite one side *)
  reflexivity.  (* And again, reflexivity finishes the goal *)
Qed.
