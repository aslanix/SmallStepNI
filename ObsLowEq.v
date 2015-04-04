Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Require Import Identifier Environment Imperative.

(**********)

Inductive obs_low_eq: obs -> obs -> Prop :=
| obs_low_eq_high_high: forall i n i' n', obs_low_eq (Effect High i n) (Effect High i' n') 
| obs_low_eq_high_halt: forall i n, obs_low_eq (Effect High i n) Halt
| obs_low_eq_halt_high: forall i n, obs_low_eq Halt (Effect High i n)
| obs_low_eq_halt_halt: obs_low_eq Halt Halt 
| obs_low_eq_low : forall i n, 
                     obs_low_eq (Effect Low i n) (Effect Low i n).

Notation "o '≜' o'" := (obs_low_eq o o') (at level 40).


Lemma obs_low_eq_ref:
  forall o, o ≜ o.
Proof.
  intro.
  destruct o; auto with Sec.
  constructor.
  destruct l; constructor.
Qed.  


Lemma obs_low_eq_sym:
  forall o o',
    obs_low_eq o o' ->
    obs_low_eq o' o.
Proof.
  intros.
  inversion H; constructor.
Qed.


Lemma obs_low_eq_is_low_effect: 
  forall o1 o2, 
    o1 ≜ o2 -> 
    is_low_effect o1 -> 
    is_low_effect o2.
Proof.
  intros.
  inversion H0;
  inversion H;
  crush.  
Qed.


Lemma obs_low_eq_aux:
  forall o1 o2,  
    o1 ≜ o2 ->
    is_low_effect o1 ->
    o1 = o2.
Proof.
  intros.
  inversion H; inversion H0; crush.
Qed.

(* the following lemam makes assignment case simpler *)
Lemma eq_obs_are_low_related: 
  forall o1 o2, 
    o1 = o2 -> o1 ≜ o2.
Proof.
  intros.
  destruct H.
  apply obs_low_eq_ref.
Qed.  


Lemma non_low_effects_are_related:
  forall o1 o2, 
    ~is_low_effect o1 ->
    ~is_low_effect o2 ->
    o1 ≜ o2.
Proof.
  intros.
  destruct o1, o2; 
  repeat match goal with 
      | [ H: context [Effect ?l ?i ?n] |- _ ]=>
        assert (l = High) by 
            ( destruct l; 
              assert (is_low_effect (Effect Low i n)) by (constructor; auto);
              crush);          
          subst;
          clear H
         end; 
  constructor.
Qed.  
