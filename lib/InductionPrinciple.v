Section InductionPrinciple.

(* http://pldev.blogspot.dk/2012/02/proving-strong-induction-principle-for.html *)

Require Export Datatypes.




Lemma le_S :
  forall n m : nat,
    n <= S m -> n <= m \/ n = S m.
Proof.
  intros.
  inversion H.
  right. reflexivity.
  left. assumption.
Qed.

Theorem strongind_aux : forall P: nat -> Prop,
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, (forall m, ((m <= n) -> P m)).
Proof.
  induction n as [ | n' IHn' ].
    intros m H1.
    inversion H1.
    assumption.
    intros.
    assert (m <= n' \/ m = S n'). apply le_S. assumption.
    inversion H2.
    apply IHn'; assumption.
    rewrite H3.
    apply (H0 n'); assumption.
Qed.

Lemma weaken : forall P : nat -> Prop,
  (forall n, (forall m, ((m <= n) -> P m))) -> (forall n, P n).
Proof.
  intros P H n.
  apply (H n n).
  apply le_n.
Qed.

Theorem strongind : forall P : nat -> Prop,
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, P n.
Proof.
  intros.
  apply weaken.
  apply strongind_aux; assumption.
Qed.

End InductionPrinciple.
