(*
(Single-trace) properties of bridge relation

Author: Aslan Askarov
Created: 2016-07-26

*)

Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.
Require Import Omega.
Set Implicit Arguments.

Require Import Identifier Environment Imperative Types Augmented Bridge.
Require Import WellFormedness LowEq NIexp.
Require Import InductionPrinciple.
Require Import UtilTactics.
Require Import BridgeTactics.







(* TODO : move these lemmas outside *)




(* 2016-07-25
   - auxiliarly ltac to deal with inductive cases
      (when inducting over n in bridge definition)
     to disregard impossible cases;
   - useful in the following two lemmas about inverting properties of skip and assign
*)


Ltac bridge_inductive_impossible_aux H:=
    intros; inversion H; subst; invert_high_steps; eauto; stop_contradiction_alt.



Lemma preservation_bridge:
  forall Γ pc c c' m m' ev n,
    -{ Γ , pc ⊢ c }- ->
    〈c, m 〉 ⇨+/(SL, Γ, ev, S n) 〈c', m' 〉 ->
    wf_mem m Γ ->
    (wf_mem m' Γ  /\ (c' <> STOP -> -{ Γ , pc ⊢ c' }- )) .

Proof.
  intros.
  dependent induction H0.

  - invert_low_event_step.
    forwards : preservation_event_step evt; eauto.

  - invert_high_event_step.
    forwards : preservation_event_step; eauto.

  - invert_high_event_step.
    destruct cfg' as [c'' m''].
    forwards* (H_wf' & H_wt' ): preservation_event_step evt' c m c'' m''.
    specializes* H_wt'.
    replace n with (S (n - 1)) in * by omega.
    specializes IHbridge_step_num c'' c' ___.
Qed.    



Lemma while_bridge_properties:
  forall Γ n e c m ev c_end m_end,
    〈WHILE e DO c END, m 〉 ⇨+/(SL, Γ, ev, S n) 〈c_end, m_end 〉
    ->
    n > 0 /\
    〈 IFB e THEN c;; WHILE e DO c END ELSE SKIP FI, m〉 ⇨+/(SL, Γ, ev, n) 〈c_end, m_end 〉.
Proof.
  intros.
  bridge_num_cases (inverts~ H) Case.
  - Case "bridge_low_num".
    invert_low_steps.
  - Case "bridge_stop_num".
    invert_high_steps.
    exfalso.
    invert_step.
    auto.
    
  - Case "bridge_trans_num".
    invert_high_steps.
    invert_step; intros; subst; splits~; try omega.
Qed.





Lemma if_bridge_properties:
  forall Γ n e c1 c2 m ev c_end m_end,
    〈IFB e THEN c1 ELSE c2 FI, m 〉 ⇨+/(SL, Γ, ev, S n) 〈c_end, m_end 〉
    ->
    n > 0 /\
    (
      ( exists u, (eval e m u) /\ u <> 0 /\ 〈c1, m 〉 ⇨+/(SL, Γ, ev, n) 〈c_end, m_end 〉)
      \/
      ( (eval e m 0 ) /\ 〈c2, m 〉 ⇨+/(SL, Γ, ev, n) 〈c_end, m_end 〉)
    ).
Proof.
  intros.
  bridge_num_cases (inversion H) Case; subst.

  - Case "bridge_low_num".
    + invert_low_steps.

  - Case "bridge_stop_num".
    + invert_high_steps.
      * exfalso.
        {  - invert_step; stop_contradiction_more. }

  -  Case "bridge_trans_num".
     + invert_high_steps.
       * invert_step; intros; subst; split; try omega.
         { - left; exists u; split~. }
         { - right; splits~. }
Qed.



Lemma is_not_stop_trivial_exf: forall m,
                                 is_not_stop 〈STOP, m 〉 -> False.

Proof.
  intros.
  unfolds in H.
  unfolds in H.
  assert ( cmd_of 〈STOP, m 〉= STOP). 
  auto.
  specialize_gen.
  assumption.
Qed.  

Hint Resolve is_not_stop_trivial_exf.

Lemma skip_bridge_properties:
  forall Γ n m ev c_end m_end,
    〈SKIP, m 〉 ⇨+/(SL, Γ, ev, S n) 〈c_end, m_end 〉->
    m_end = m /\ c_end = STOP /\ n = 0 /\ ev = EmptyEvent.
Proof.
  intros Γ n; induction n.
  {
    intros.
    invert_bridge_step_num.
    - invert_low_steps.
    - invert_high_steps.
      splits~ .
    - omega.
  }
  (* inductive case *)
  {
    
    bridge_inductive_impossible_aux H.
    
  }
Qed.


    
Lemma assign_bridge_properties:
  forall Γ n x e m ev c_end m_end,
    〈x ::= e, m 〉 ⇨+/(SL, Γ, ev, S n) 〈c_end, m_end 〉
    -> (exists v ℓ,
          eval e m v /\ m_end = update_st m x v
          /\ Γ (x) = Some ℓ /\
          ( ℓ  ⊑ Low  -> ev = AssignmentEvent ℓ x v )
          /\
          (~ℓ  ⊑ Low  -> ev = EmptyEvent)
       )
       /\ (c_end = STOP)
       /\ (n = 0).
Proof.
  intros Γ n x e.
  induction n; intros.
  {
  (*base case n = 0 *)

  inversion H; [ invert_low_steps | invert_high_steps | omega ]; split; auto;
  repeat
    match goal with
      | [ H: context [step] |- _ ] => (inverts  H;  clear H )
      | [ H: Γ x = Some ?L, H': eval _ _ ?V |- exists _ _, _] =>
        (exists V L)
      | [ _ : eval ?E ?M ?V1, H' : eval ?E ?M ?V2 |- _ ] =>
        (assert (V1 = V2) by (apply eval_is_det with (e:=E) (st:=M); crush); subst; clear H'; crush)
      | [ H: context [AssignmentEvent ?L ?X ?V ] |- _ ] => (
          unfold high_event in H; unfold not in H;
          assert (low_event Γ Low (AssignmentEvent L X V))
            by (constructor; assumption);
          contradiction)
    end.
  }
  (* inductive case *)
  {
    bridge_inductive_impossible_aux H.
  }
Qed.



Lemma seq_comp_bridge_property:
  forall Γ n c1 c2 m ev c_end m_end,
    〈c1;; c2, m 〉 ⇨+/(SL, Γ, ev, S n) 〈c_end, m_end 〉
    ->
    (exists c1', 〈c1, m 〉 ⇨+/(SL, Γ, ev, S n) 〈 c1', m_end 〉
                 /\ (c1' <> STOP -> c_end = (c1';; c2))
                 /\ (c1' = STOP -> c_end = c2)
                 /\ low_event Γ Low ev
    )
    \/
    (exists m1' k,
        k < n /\ n  > 0 /\
       〈c1, m 〉 ⇨+/(SL, Γ, EmptyEvent, S k) 〈 STOP, m1' 〉
       /\ 〈c2, m1' 〉 ⇨+/(SL, Γ, ev, n - k ) 〈 c_end, m_end 〉
    ).
Proof.
  intros Γ n.
  induction n.
  (* base case *)
  {
    left.
   intros.
   bridge_num_cases (inversion H) Case; subst.
   Case "bridge_low_num".
   {
     do 2
        match goal with
          | [ H : context [low_event_step] |- _ ] =>
            (inversion H ; subst; clear H)
          | [ H : context [event_step _ _ 〈 c1;; c2, _ 〉 _] |- _ ] =>
            (inversion H ; subst; clear H);
              match goal with
                | [ H : context [event_step _ _ 〈c1, _ 〉〈?C1, _ 〉] |- _ ] =>
                  (exists C1; repeat ( constructor || assumption))
              end
        end;
     match goal with | [ H :  context [low_event] |- _ ] => inversion H end;
     crush.
   }
   Case "bridge_stop_num".
   {
     
     repeat
       match goal with
         | [ H : context [high_event_step] |- _ ] =>
           unfold high_event_step in H

         | [ H : context [event_step _ _ 〈 c1;; c2, _  〉 _  ] |- _ ] =>
           inversion H; subst; clear H

         | [ H : context [is_stop] |- _ ] =>
           do 2 unfolds in H; inverts* H

         | [ H : context [ _ = 〈 STOP, _ 〉] |- _ ] =>
           inversion H; clear H; contradiction
       end.
   }
   Case "bridge_trans_num".
   {
     omega.
   }
  }
  (* inductive case *)
  {
    intros.
    inversion H.
    subst.

    do 3
       match goal with
         | [ H : context [high_event_step] |- _ ] =>
           unfold high_event_step in H

         | [ H : context [event_step _ _ 〈 c1;; c2, _  〉 _  ] |- _ ] =>
           inversion H; subst; clear H

       end.
    {

      match goal with
        | [ H: 〈?c1';; c2, ?st' 〉 ⇨+/(SL, Γ, ev, S n) 〈c_end, m_end 〉 |- _ ]
          => specialize (IHn c1' c2 st' ev c_end m_end H)
      end.
      destruct IHn.
      {
        super_destruct.
        match goal with [ H:〈c1', st' 〉 ⇨+/(SL, Γ, ev, S n) 〈?x, m_end 〉 |- _ ] =>
                        rename x into c1_end
        end.
        left.
        exists c1_end.
        compare c1_end STOP; intros;
        repeat (specialize_gen; subst; split; auto);
        apply bridge_trans_num with evt' 〈c1', st' 〉; eauto.
      }
      {
        super_destruct.
        match goal with [ H:〈c2, ?X 〉 ⇨+/(SL, Γ, ev, n - ?K ) 〈c_end, m_end 〉|- _ ] =>
                        rename X into m1_end;
                          rename K into k
        end.
        right; exists m1_end (S k).
        repeat (split || auto || omega).
        apply bridge_trans_num with evt' 〈c1', st' 〉; eauto.
      }
    }
    {
      right; exists st' 0;
      split.
      omega.

      split.
      omega.
      split.
      apply bridge_stop_num with evt'; eauto.
      
      unfolds is_not_stop;
      assert (( S n) - 0 = S n ) as X  by omega.
      rewrite X.
      assumption.
    }
  }

Qed.



Lemma event_low_eq_empty:
  forall Γ,
    event_low_eq Γ EmptyEvent EmptyEvent.
Proof.                            
  intros.
  unfolds.
  repeat (splits; auto).
Qed.  
Hint Resolve event_low_eq_empty.

Lemma event_low_eq_high:
  forall Γ x v y u,
    event_low_eq Γ (AssignmentEvent High x v) (AssignmentEvent High y u).

Proof.
  intros; unfolds.
  repeat split; intros; inversion H; impossible_flows.
Qed.

Hint Resolve event_low_eq_high.

Lemma event_low_eq_low:
  forall Γ x v,
    event_low_eq Γ (AssignmentEvent Low x v) (AssignmentEvent Low x v).
Proof.
  intros.
  unfolds.
  repeat split; auto.
Qed.      

Hint Resolve event_low_eq_low.

Lemma config_low_eq_trivial:
  forall Γ m s c,
    state_low_eq Γ m s ->
    config_low_eq Γ 〈 c, m 〉 〈c, s 〉.
Proof.
  intros; constructor; auto.
Qed.  
Hint Resolve config_low_eq_trivial.
