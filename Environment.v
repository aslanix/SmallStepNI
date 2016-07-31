Require Import Bool Arith List CpdtTactics SfLib.
Set Implicit Arguments.
Require Import Identifier.

Definition Env {X : Type } := id -> option X.

Definition empty_env {X : Type} : @Env X :=
   fun _ => None.

Definition update_env {X : Type} (st: @Env X) (x: id) (n: X) : @Env X:=
 fun x' => if eq_id_dec x x' then (Some n) else st x'.
Hint Unfold update_env.

Ltac update_destruct := intros; unfold update_env; destruct eq_id_dec; crush.

Theorem update_eq {X: Type}: forall (n:X) x st,
 (update_env st x n) x = Some n.
Proof.
  update_destruct.
Qed.

Theorem update_neq {X : Type} : forall x2 x1 (n:X) st,
  x1 <> x2 -> 
   (update_env st x2 n) x1 = (st x1).
Proof.
  update_destruct.
Qed.


Theorem update_same {X: Type}: forall (n1:X) x1 x2 (st: Env),
  st x1 = Some n1 -> (update_env st x1 n1) x2 = st x2.
Proof.
  update_destruct.
Qed.

Theorem update_shadow {X: Type}: forall (n1:X) (n2:X) x1 x2 (st: Env),
  (update_env (update_env st x2 n1) x2 n2) x1 = (update_env st x2 n2) x1.
Proof.
  update_destruct.
Qed.

Theorem update_permute {X: Type} : forall (n1:X) (n2:X) x1 x2 x3 (st:Env),
  x2 <> x1 -> 
  (update_env (update_env st x2 n1) x1 n2) x3 = (update_env (update_env st x1 n2) x2 n1) x3.
Proof.  
  intros. unfold update_env.  repeat (destruct eq_id_dec; crush).
Qed.
