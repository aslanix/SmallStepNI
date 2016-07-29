Require Import Bool Arith List CpdtTactics SfLib LibTactics Omega.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Require Import Identifier Environment Imperative Types Augmented.


Inductive low_event : typenv -> level -> event -> Prop :=
| low_assigment_is_low_event:
    forall Γ ℓ ℓ' x u,
      ( ℓ' ⊑ ℓ) ->
      low_event Γ ℓ (AssignmentEvent ℓ' x u).

Definition high_event Γ ℓ evt := ~low_event Γ ℓ evt.

Definition low_event_step  Γ ℓ evt cfg cfg' := event_step Γ evt cfg cfg' /\ low_event Γ ℓ evt.
Definition high_event_step Γ ℓ evt cfg cfg' := event_step Γ evt cfg cfg' /\ high_event Γ ℓ evt.

Hint Constructors low_event.
Hint Unfold high_event.
Hint Unfold high_event_step.
Hint Unfold low_event_step.


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


(* Multi-step reduction *)

Inductive multi {X:Type} (R: relation X): relation X :=
   | multi_refl : forall (x : X), multi R x x
   | multi_step : forall (x y z : X),
         R x y ->
         multi R y z ->
         multi R x z.
Hint Resolve multi_refl.


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






Definition relation_idx := fun X : Type => X -> X -> nat -> Prop.

Inductive multi_idx {X:Type} (R: relation X) :relation_idx X :=
   | multi_refl_zero : forall (x : X), multi_idx R x x 0
   | multi_step_more : forall (x y z : X) n,
                         R x y ->
                         multi_idx R y z n ->
                         multi_idx R x z (S n).


Hint Resolve multi_refl_zero.


Tactic Notation "multi_idx_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl_zero" | Case_aux c "multi_step_more" ].



(* Multi-step transitions *)
Definition multistep_idx := multi_idx step.
Notation " t '⇒/+' n '+/' s" := (multi_idx step t s n) (at level 40).


Theorem multi_idx_R:
  forall (X:Type) (R: relation X) ( x y : X),
    R x y -> (multi_idx R) x y 1.
Proof.                     
  intros.
  eapply multi_step_more; eauto.
Qed.  

Theorem multi_idx_trans:
  forall n (X: Type) (R: relation X) ( x y z: X ) m,
    multi_idx R x y n ->
    multi_idx R y z m ->
    multi_idx R x z (n + m).
Proof.    
  intros n X R.
  induction n; intros.
  -     inverts* H.
        
  - inversion H; subst; auto.
    assert (multi_idx R x y0 1) by (econstructor; eauto).
    
    specialize (IHn y0 y z m H5 H0).
    replace (S n + m) with (S (n + m)) by omega.
    eapply multi_step_more; eauto.
Qed.    


Theorem from_multi_to_multi_idx:
  forall (X:Type) (R:relation X) (x y : X),
    multi R x y -> exists n, (multi_idx R x y n).
Proof.
  intros.
  induction H.
  - (exists 0; constructor).
  - destruct IHmulti as [n ?IHmulti].
    (exists (S n)).
    econstructor; eauto.
Qed.

(* TODO: 2016-07-28: move multi_idx someplace else *)


