(* 

General tactics to help discharge properties about Bridge relation 
Author: Aslan Askarov 
Created: 2016-07-26

*)

Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Require Import Identifier Environment Imperative Types Augmented Bridge.
Require Import WellFormedness LowEq.
Require Import InductionPrinciple.
Require Import UtilTactics.


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
      match goal with
      | [ H : context [is_not_stop_config 〈STOP, ?M 〉]|- _ ] =>
        unfold is_not_stop_config in H;
          unfold not in H;
          assert (is_stop_config 〈STOP, M 〉) by ( exists M; crush);
          contradiction
    end.

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


