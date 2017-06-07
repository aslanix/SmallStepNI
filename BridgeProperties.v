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
    〈c, m 〉 ⇨+/(SL, Γ, ev, n) 〈c', m' 〉 ->
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
Qed.



Lemma while_bridge_properties:
  forall Γ n e c m ev c_end m_end,
    〈WHILE e DO c END, m 〉 ⇨+/(SL, Γ, ev, n) 〈c_end, m_end 〉
    ->
    n >= 1 /\
    〈 IFB e THEN c;; WHILE e DO c END ELSE SKIP FI, m〉 ⇨+/(SL, Γ, ev, n - 1) 〈c_end, m_end 〉.
Proof.
  intros.
  inverts~ H.

  split*.

  -  exfalso. invert_low_steps.
  - exfalso. invert_low_steps.
  - exfalso. invert_high_steps. eauto.
  -
    invert_high_steps.
    invert_step.
    split; try omega.
    match goal with [ |- context [S ?x - 1]] =>
                    replace (S x - 1 ) with x by omega
    end; eauto.
Qed.





Lemma if_bridge_properties:
  forall Γ n e c1 c2 m ev c_end m_end,
    〈IFB e THEN c1 ELSE c2 FI, m 〉 ⇨+/(SL, Γ, ev, n) 〈c_end, m_end 〉
    ->
    n >= 1 /\
    (
      ( exists u, (eval e m u) /\ u <> 0 /\ 〈c1, m 〉 ⇨+/(SL, Γ, ev, n - 1) 〈c_end, m_end 〉)
      \/
      ( (eval e m 0 ) /\ 〈c2, m 〉 ⇨+/(SL, Γ, ev, n - 1) 〈c_end, m_end 〉)
    ).
Proof.
  intros.
  inverts H.
  - exfalso. invert_low_steps.
  - exfalso. invert_high_steps. eauto.
  - split~ ; try omega.

    invert_high_steps.
    invert_step; [left; exists u | right];
    match goal with [ |- context [S ?x - 1]] =>
                    replace (S x - 1 ) with x by omega
    end; eauto.
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
    〈SKIP, m 〉 ⇨+/(SL, Γ, ev, n) 〈c_end, m_end 〉->
    m_end = m /\ c_end = STOP /\ n = 0 /\ ev = EmptyEvent.
Proof.
  intros.
  bridge_num_cases (inverts* H) Case.
  - inverts H0.
    inverts* H.
  - inverts H0.
    inverts H.
    split ~ .
  - invert_high_steps.
    exfalso.
    eauto.
Qed.

Ltac eval_determinism :=
  match goal with
    | [ H : eval ?E ?M ?V1, H' : eval ?E ?M ?V2 |- _ ] =>
      forwards* : eval_is_det V1 V2; clear H
  end.





Lemma assign_bridge_properties:
  forall Γ n x e m ev c_end m_end,
    〈x ::= e, m 〉 ⇨+/(SL, Γ, ev, n) 〈c_end, m_end 〉
    -> (exists v ℓ,
          eval e m v /\ m_end = update_st m x v
          /\ Γ (x) = Some ℓ /\
          ( ℓ  ⊑ Low  -> ev = AssignmentEvent ℓ x v )
          /\
          (~ℓ  ⊑ Low  -> high_event Γ Low ev)
       )
       /\ (c_end = STOP)
       /\ (n = 0).
Proof.
  intros Γ n x e. intros.

  inverts* H.
  - invert_low_steps; subst.
    split ~ .
    match goal with
        [_: context [eval e m ?v] |- _ ] =>
        (exists v Low)
    end.
    splits * .
    + invert_step. eval_determinism.
    + intros. destruct ℓ; eauto; impossible_flows.
    + intros.  destruct ℓ; eauto; impossible_flows.

  - invert_high_steps; subst.
    splits ~ .
    match goal with
        [_: context [eval e m ?v], _:  Γ _ = Some ?ℓ |- _ ] =>
        (exists v ℓ)
    end.

    splits ~ .
    + invert_step. eval_determinism.

  - exfalso.
    invert_high_steps.
    eauto.
Qed.



Lemma seq_comp_bridge_property:
  forall Γ n c1 c2 m ev c_end m_end,
    〈c1;; c2, m 〉 ⇨+/(SL, Γ, ev, n) 〈c_end, m_end 〉
    ->
    (exists c1', 〈c1, m 〉 ⇨+/(SL, Γ, ev, n) 〈 c1', m_end 〉
                 /\ (c1' <> STOP -> c_end = (c1';; c2))
                 /\ (c1' = STOP -> c_end = c2)
                 /\ low_event Γ Low ev
    )
    \/
    (exists m1' k evt,
       k < n /\ n > 0 /\
       high_event Γ Low evt /\
       〈c1, m 〉 ⇨+/(SL, Γ, evt, k) 〈 STOP, m1' 〉
       /\ 〈c2, m1' 〉 ⇨+/(SL, Γ, ev, n - k - 1 ) 〈 c_end, m_end 〉
    ).
Proof.
  intros Γ n.
  induction n.
  (* base case *)
  {
    left.
    intros.

    inverts* H.
    (* 2 cases *)
    - (* low-step*)
      do 2
      match goal with
          | [ H : context [low_event_step] |- _ ] =>
            (inverts H ; clear H)
          | [ H : context [event_step _ _ 〈 c1;; c2, _ 〉 _] |- _ ] =>
            (inverts H ; clear H);
              match goal with
                  | [ H : context [event_step _ _ 〈c1, _ 〉〈?C1, _ 〉] |- _ ] =>
                    (exists C1; repeat ( constructor || assumption))
                end;
              intros;         exfalso;eauto

        end.
    - (* high_step *)

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
       end; crush.

  }
  (* inductive case *)
  {
    intros.
    inverts H.



    do 3
       match goal with
         | [ H : context [high_event_step] |- _ ] =>
           unfold high_event_step in H

         | [ H : context [event_step _ _ 〈 c1;; c2, _  〉 _  ] |- _ ] =>
           inversion H; subst; clear H

       end.


    {

      match goal with
        | [ H: 〈?c1';; c2, ?st' 〉 ⇨+/(SL, Γ, ev, n) 〈c_end, m_end 〉 |- _ ]
          => specialize (IHn c1' c2 st' ev c_end m_end H)
      end.
      destruct IHn.
      {
        super_destruct.
        match goal with [ H:〈c1', st' 〉 ⇨+/(SL, Γ, ev,  n) 〈?x, m_end 〉 |- _ ] =>
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
        match goal with [ H:〈c2, ?X 〉 ⇨+/(SL, Γ, ev, n - ?K -1 ) 〈c_end, m_end 〉|- _ ] =>
                        rename X into m1_end;
                          rename K into k
        end.


        right; exists m1_end (S k).
        match goal with
            [ _ :  〈 c1', _ 〉 ⇨+/(SL, Γ, ?EV, k) 〈 STOP, _ 〉 |- _ ]
            => (exists EV)
        end.
        splits*; try omega.
        apply bridge_trans_num with evt' 〈c1', st' 〉; eauto.
      }
    }
    {

      right; exists st' 0 evt'.

      splits; try omega; eauto.
      - apply bridge_stop_num; eauto.
      -  unfolds is_not_stop.
         assert (( S n - 0 - 1 =  n )) as X  by omega.
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
