Require Import Bool Arith List CpdtTactics SfLib.
Set Implicit Arguments.



Inductive id: Type := 
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p.
Proof.
  intros.
  destruct (eq_id_dec x x).
  Case "x = x".
    reflexivity.
  Case "x <> x (impossible)".
    apply ex_falso_quodlibet; apply n; reflexivity. 
Qed.

Lemma neq_id : forall (T: Type) x y ( p q : T ),  x <> y ->
  (if eq_id_dec x y then p else q) = q.
Proof.
  intros.
  destruct (eq_id_dec x y); crush.
Qed.



