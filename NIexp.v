Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Require Import Identifier Environment Imperative WellFormedness LowEq Types.

(* Non-interference for expressions *)
Theorem ni_exp: forall Γ m1 m2 e u v ℓ,
  {{ Γ ⊢ e : ℓ }} ->
  state_low_eq Γ m1 m2 ->
  eval e m1 u ->
  eval e m2 v ->
  val_low_eq ℓ u v.
Proof.  
  intros.
  generalize dependent v.
  generalize dependent u.
  exp_has_level_cases(induction H) Case.
  Case "T_Const".
    intros.
    assert (u = n) as Hu.
    apply eval_const_aux with m1; assumption.
    assert (v = n) as Hv. 
    apply eval_const_aux with m2; assumption.
    crush.
    induction ℓ ;[ apply VLEqL | apply VLEqH]; crush.
  Case "T_Id".
    intros.
    apply vars_low_eq with Γ m1 m2 x; 
      repeat (try assumption; apply eval_var_aux).    
  Case "T_Plus".            
    intros.
    level_cases (induction ℓ) SCase; [ | apply VLEqH]; crush.
    inversion H2.
    inversion H3.
    crush.

    Ltac lleq a b :=
      assert (val_low_eq Low a b); auto.

    lleq u0 u1.
    lleq v0 v1.
   
    assert (u0 = u1); inversion H6 ; inversion H7; auto.
    apply VLEqL. auto.
  Case "T_Sub".
    intros.
    induction ℓ'; [ | apply VLEqH]; crush.
    assert (ℓ = Low).
    inversion H1; auto.
    rewrite H5 in H4.
    apply H4; crush.
Qed.


