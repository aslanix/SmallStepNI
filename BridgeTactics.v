(*

General tactics to help discharge properties about Bridge relation
Author: Aslan Askarov
Created: 2016-07-26

*)

Require Import Bool Arith List CpdtTactics SfLib LibTactics Omega.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Require Import Identifier Environment Imperative Types Augmented Bridge.
Require Import WellFormedness LowEq.
Require Import InductionPrinciple.
Require Import UtilTactics.

Ltac invert_low_event:=
        match goal with [ H: low_event _ _ _ |- _ ] => inversion H end.

Ltac invert_low_steps :=
  repeat
    match
      goal with
      | [ H: context [low_event_step] |- _ ] => inversion H; subst; clear H
      | [ H: context [event_step]     |- _ ] => inversion H; subst; clear H
      | [ H: context [low_event ]     |- _ ] => inversion H; subst; clear H
    end.

Ltac invert_high_steps :=
  repeat
    match
      goal with
      | [ H: context [high_event_step] |- _ ] => inversion H; subst; clear H
      | [ H: context [event_step]     |- _ ] => inversion H; subst; clear H
    end.





Ltac stop_contradiction:=
  match goal with [H: context [is_stop] |- _ ] => repeat unfolds in H ; inverts H end.

(*
      match goal with
      | [ H : context [is_not_stop_config 〈STOP, ?M 〉]|- _ ] =>
        unfold is_not_stop_config in H;
          unfold not in H;
          assert (is_stop_config 〈STOP, M 〉) by ( exists M; crush);
          contradiction
    end.
*)

(*

Ltac prove_is_not_stop_config:=
  unfold is_not_stop_config;
  unfold not; intros;
  match goal with
    | [ H: is_stop_config 〈?C, ?S 〉 |- _] =>
      (inversion H;
       match goal with
         | [ H': 〈C, S〉 = 〈STOP, _〉 |- _] => inversion H'; contradiction
       end
      )
  end.

*)

Ltac impossible_flows:=
  match goal with
    | [ H: High ⊑ Low |- _ ] => inverts H
  end.




Ltac invert_bridge_step_num:=
  match goal with
    | [H : context [bridge_step_num] |- _ ] => inverts H
  end.


Ltac invert_low_event_step:=
   match goal with
        | [H : context [low_event_step ] |-_ ]=> inverts H
   end.

Ltac invert_high_event_step:=
   match goal with
        | [H : context [high_event_step ] |-_  ]=> inverts H
   end.


Ltac _find keyword:=
  match goal with
    | [H : context [keyword] |- _ ] => H
  end.


Ltac _eapply_in_ctxt keyw what :=
  let H := _find (keyw)
  in eapply what in H.




(* LEMMAS that go into Hints *)

Lemma is_stop_trivial : forall m, is_stop 〈STOP, m 〉.
            Proof.
              intros.
              unfolds.
              constructor.
            Qed.

Hint Resolve is_stop_trivial.




Lemma is_not_stop_config_inversion:
  forall c st,
    is_not_stop 〈c, st 〉 ->
    c <> STOP.
  intros.
  unfolds.
  intros.
  unfolds in H.
  unfolds in H.
  subst.
  destruct H.
  unfolds.
  auto.
Qed.

Hint Resolve is_not_stop_config_inversion.


Lemma is_stop_config_inversion:
  forall c st,
    is_stop 〈c, st 〉 ->
    c = STOP.
  intros.
  unfolds in H.
  unfolds in H.
  auto.

Qed.

Hint Resolve is_stop_config_inversion.


Lemma empty_event_is_high :
  forall Γ,
  high_event Γ Low EmptyEvent.
Proof.
  intros.
  do 2 unfolds; intros;
  match goal with [H : context [low_event] |- _ ] => inverts H end.
Qed.

Hint Resolve empty_event_is_high.




Lemma bridge_steps_are_nonneg:
         forall Γ c m ev n cfg,
           〈 c, m 〉 ⇨+/(SL, Γ, ev, n) cfg ->
           n >= 0.
         Proof.
           intros; inverts * H; omega.
Qed.

Hint Resolve bridge_steps_are_nonneg.


Lemma is_non_stop_config_trivial:
         forall c st,
           c <> STOP ->
           is_not_stop 〈c, st 〉.
Proof.
         intros.
         do 2 unfolds.
         intros.
         inversion H0.
         inversion H1.
         subst.
         tauto.
       Qed.
Hint Resolve is_non_stop_config_trivial.


Lemma multi_stop_trivial:
  forall m m',
    〈 STOP, m 〉⇒*〈STOP, m' 〉 ->
    m = m'.
Proof.
  intros.
  inverts* H.
  inverts H0.
Qed.
Hint Resolve multi_stop_trivial.


Lemma multi_idx_stop_trivial:
   forall m m' n,
    〈 STOP, m 〉⇒/+ n +/ 〈STOP, m' 〉 ->
    m = m'.
Proof.
  intros.
  inverts* H.
  inversion H0.
Qed.
Hint Resolve multi_idx_stop_trivial.

Lemma high_assignments_are_high_events:
  forall Γ x u,
    high_event Γ Low (AssignmentEvent High x u).
Proof.
  intros.
  do 2 unfolds.
  intros.
  inversion H.
  subst.
  impossible_flows.
Qed.
Hint Resolve high_assignments_are_high_events.




Ltac stop_contradiction_more:=
  match goal with
    | [ H: is_stop 〈?C, ?M 〉, H' : ?C <> STOP |- _ ] =>
      inverts*  H
  end.

Lemma stop_contradiction_more_lemma :
  forall c m, is_stop 〈c, m 〉 -> c <> STOP -> False.
Proof.
  intros.
  stop_contradiction_more.
Qed.

Hint Resolve stop_contradiction_more_lemma.


Ltac stop_contradiction_alt :=
  match goal with [ H : is_not_stop 〈 STOP, ?m 〉 |- _ ] =>
    do 2 unfolds in H;
    assert (cmd_of 〈STOP, m 〉 = STOP ) by
    (
      unfolds;
      auto
    );
    specialize_gen;
    exfalso;
    assumption
  end.

Lemma stop_contradiction_alt_lemma_exf :
  forall m,  is_not_stop 〈 STOP, m 〉 -> False.
Proof.
  intros.
  stop_contradiction_alt.
Qed.

Hint Resolve stop_contradiction_alt_lemma_exf.

Ltac invert_step:=
  match goal with [H : context[step] |- _ ] => inverts H end.
