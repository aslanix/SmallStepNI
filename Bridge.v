Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Require Import Identifier Environment Imperative Types Augmented.

(* 
Inductive obs :=
  | Halt : obs
  | Effect : {  evt | evt <> EmptyEvent } -> obs.


Print Effect.


Lemma eq_obs_dec: forall ev1 ev2: obs, {ev1 = ev2} + { ev1<>ev2 }.
Proof.
  decide equality.

Qed.
Local Hint Resolve eq_obs_dec.


Definition is_effect (o:obs) :Prop :=
  exists ℓ x v, o = Effect ℓ x v.

Definition is_low_effect (o: obs) : Prop :=
  exists x v, o = Effect Low x v.


Lemma low_effects_are_effects:
  forall o,
    is_low_effect o -> is_effect o.
Proof.
  intros.
  unfold is_effect.
  unfold is_low_effect in *.
  exists Low.
  auto.
Qed.
Hint Resolve low_effects_are_effects : Sec.
 *)

Inductive low_event : typenv -> level -> event -> Prop :=
| low_assigment_is_low_event:
    forall Γ ℓ ℓ' x u,
      ( ℓ' ⊑ ℓ) ->
      low_event Γ ℓ (AssignmentEvent ℓ' x u).

Definition high_event Γ ℓ evt := ~low_event Γ ℓ evt.

Definition low_event_step  Γ ℓ evt cfg cfg' := event_step Γ evt cfg cfg' /\ low_event Γ ℓ evt.
Definition high_event_step Γ ℓ evt cfg cfg' := event_step Γ evt cfg cfg' /\ high_event Γ ℓ evt.

(*
Inductive bridge_step:
  typenv -> level -> config -> config -> event -> Prop:=
| bridge_low :
    forall Γ ℓ evt cfg cfg',
      low_event_step Γ ℓ evt cfg cfg' ->
      bridge_step Γ ℓ cfg cfg' evt
| bridge_stop :
    forall Γ ℓ evt cfg cfg',
      high_event_step Γ ℓ evt cfg cfg' ->
      is_stop_config cfg' ->
      bridge_step Γ ℓ cfg cfg' evt
| bridge_trans:
    forall Γ ℓ evt' evt'' cfg cfg' cfg'',
      high_event_step Γ ℓ evt' cfg cfg' ->
      is_not_stop_config cfg' ->
      bridge_step Γ ℓ evt'' cfg' cfg'' ->
      bridge_step Γ ℓ evt'' cfg cfg''.
*)


Inductive bridge_step_num:
  typenv -> level -> config -> config -> event -> nat -> Prop :=
| bridge_low_num:
    forall Γ ℓ evt cfg cfg',
      low_event_step Γ ℓ evt cfg cfg' ->
      bridge_step_num Γ ℓ cfg cfg' evt 1
| bridge_stop_num:
    forall Γ ℓ evt cfg cfg',
      high_event_step Γ ℓ evt cfg cfg' ->
      is_stop_config cfg' ->
      bridge_step_num Γ ℓ cfg cfg' EmptyEvent 1
| bridge_trans_num:
    forall Γ ℓ evt' evt'' cfg cfg' cfg'' n,
      n >=1 ->
      high_event_step Γ ℓ evt' cfg cfg' ->
      is_not_stop_config cfg' ->
      bridge_step_num Γ ℓ  cfg' cfg'' evt''  n ->
      bridge_step_num Γ ℓ  cfg cfg'' evt'' (S n).




Tactic Notation "bridge_num_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "bridge_low_num" | Case_aux c "bridge_stop_num" | Case_aux c "bridge_trans_num" ].


Notation " t '⇨+/(SL,' Γ ',' obs ',' n ')'  t' " :=
  (bridge_step_num Γ Low t t' obs n) (at level 40).

Definition bridge_step Γ ℓ  evt cfg cfg' :=
  exists n, bridge_step_num Γ ℓ  evt cfg cfg' (S n).


Notation " t '⇒+/(SL,' Γ ',' obs ')'  t' " :=
  (bridge_step Γ Low t t' obs) (at level 40).


(* Not sure if we will need this after all *)


(* Multi-step reduction *)

Inductive multi {X:Type} (R: relation X): relation X :=
   | multi_refl : forall (x : X), multi R x x
   | multi_step : forall (x y z : X),
         R x y ->
         multi R y z ->
         multi R x z.
Local Hint Resolve multi_refl.


Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].


Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl. Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
   intros.
   multi_cases (induction H) Case.
   Case "multi_refl".
      assumption.
  Case "multi_step".
      apply multi_step with y; try apply IHmulti; assumption.

Qed.





(* Multi-step transitions *)
Definition multistep := multi step.
Notation " t '⇒*' t' " := (multistep t t') (at level 40).
