(** Adequacy of the bridge semantics w.r.t. standard semantics for
well-typed programs.

Author: Aslan Askarov
Created: 2016-07-27

- Note: that well-typedness is required may potentially be relaxed,
  but we leave that for future investigation.

 *)



Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.
Require Import Omega.

Set Implicit Arguments.

Require Import Identifier Environment Imperative Types Augmented Bridge.
Require Import WellFormedness.
Require Import InductionPrinciple.
Require Import UtilTactics.
Require Import BridgeTactics.
Require Import BridgeProperties.



Lemma adequacy_of_event_steps:
  forall Γ pc c m cfg',
    wf_mem m Γ ->
    -{ Γ, pc ⊢ c }- ->
    〈c, m 〉 ⇒ cfg' ->
    exists ev, event_step Γ ev 〈c, m 〉 cfg'.
Proof.
  intros Γ pc c m [c' m']; intros.
  cmd_cases (dependent induction c) Case.
  Case "STOP".
  { invert_step. }
  Case "SKIP".
  { exists EmptyEvent.
    assert (c' = STOP /\ m' = m).
    {
      inverts H1.
      splits~.
    }
    super_destruct. subst.
    constructor; auto.
  }
  Case "::=".
  {
    inverts keep H1.
    inverts H0.
    exists (AssignmentEvent ℓ' i v).
    constructor~.
  }
  Case ";;".
  { assert (-{ Γ, pc ⊢ c1 }-) by
        (match goal with [ H:  -{ Γ, pc ⊢ c1;; c2 }- |- _ ] => inverts keep H end; auto).
    inverts H1;
      repeat match goal
           with
             | [ H:  〈 c1, m 〉 ⇒ 〈 ?c1', m' 〉|- _  ] =>
                  (specializes IHc1 m c1' m' H;
                   destruct IHc1 as [ev];
                   (exists ev);
                   constructor~ )
             |  [ H:  -{ Γ, pc ⊢ c1;; c' }- |- _ ] =>
                ( inverts H;
                  applys* wt_programs_are_not_stop
                )
           end.
  }
  Case "IFB".
  {
    exists EmptyEvent.
    assert (c' = c1 \/ c' = c2) as H_cmd
        by (inverts keep H1; tauto).
    match goal with
      | [ H:  -{ Γ, pc ⊢ IFB e THEN c1 ELSE c2 FI }- |- _ ]
        => inverts keep H
    end.
    assert (  -{ Γ, pc ⊢ c' }- )
      by ( destruct H_cmd; subst; applys* pc_lowering).

    assert ( m = m') by (inverts* H1); subst.
    constructor~ .
    applys* wt_programs_are_not_stop.
  }
  Case "WHILE".
  {
    exists EmptyEvent.
    inverts keep H1.
    constructor~ .
  }
Qed.

(* TODO: 2016-07-28: simplify the above lemma *)





Theorem bridge_adequacy:
  forall Γ (n:nat) c m m_end ,
    〈c, m 〉 ⇒/+ n +/ 〈STOP, m_end 〉 ->
    forall pc, -{ Γ, pc ⊢ c }-  ->
    wf_mem m Γ  ->
    (c = STOP \/
     exists ev n' cfg' k,
       〈 c, m 〉 ⇨+/(SL, Γ, ev, n') cfg' /\
       cfg' ⇒/+ k +/ 〈STOP, m_end 〉 /\ k < n).

Proof.
  intros Γ n.


  dependent induction n.
  (* n = 0 *)
  {
    left~.
    inverts H. auto.
  }


  (* inductive case *)
  {
    right; subst.
    inversion H.


    match goal with  [ H : 〈 c, m 〉 ⇒ ?y |- _ ] => destruct y as [c' m'] end; subst.
    match goal with [ H:  〈 c', m' 〉 ⇒/+ n +/ 〈 STOP, m_end 〉 |- _ ] => rename H into H_n end.
    match goal with [ H:  〈 c, m 〉 ⇒ 〈c', m' 〉 |- _ ] => rename H into H_step end.


    specialize (IHn c' m' m_end H_n pc).

    lets* (ev & H_ev) : adequacy_of_event_steps H_step.

    (* We define two auxiliary local propositions that consider the
       cases of a high and a low event respectively; these are then
       used in the case analysis afterwards *)

    assert ( low_event Γ Low ev ->
              exists ev0 n' cfg' k,
                〈 c, m 〉 ⇨+/(SL, Γ, ev0, n') cfg' /\ cfg' ⇒/+ k +/ 〈 STOP, m_end 〉/\ k < S n) as LemmaLowEvent.
    {
      intros H_low.
      inverts H_low.
      assert (ℓ' = Low) by
        ( destruct ℓ'; auto; try impossible_flows; subst ); subst.
      (exists   (AssignmentEvent Low x u) 1).
      forwards* (H_wf' & H_wt' ): preservation.
      compare c' STOP; intros;subst.
      * clear IHn.


        lets : multi_idx_stop_trivial H_n; subst.
        (exists*〈STOP, m_end 〉0).
        splits~ ; try omega.
        applys~ bridge_low_num.

      * specializes~ H_wt' __ .
        specializes~ H_n.
        exists 〈c', m' 〉.
        exists n.
        splits~ .
        applys* bridge_low_num.
    }

    assert ( high_event Γ Low ev ->
              exists ev0 n' cfg' k,
                〈 c, m 〉 ⇨+/(SL, Γ, ev0, n') cfg' /\ cfg' ⇒/+ k +/ 〈 STOP, m_end 〉/\ k < S n) as LemmaHighEvent.
    { clear LemmaLowEvent.
      intros H_high.
      compare c' STOP; intros; subst.
      - (exists EmptyEvent 1 〈STOP, m' 〉 0).
        lets : multi_idx_stop_trivial H_n; subst.
        splits~ ; try omega.
        applys*  bridge_stop_num.
      - forwards*   (H_wf' & H_wt') : preservation.
        specializes~ H_wt'.
        specializes~ IHn.
        destruct* IHn as [? | ?IHH_multi].

        lets (?ev' & ?n' &  ?cfg' & k & ?H_bridge & ?H_tail & ?H_k ): IHH_multi.
        exists ev' (S n') cfg' k.
        splits~ ; try omega.
        applys* bridge_trans_num.
    }


    (* now we are ready to do the case analysis of the event, using the above assertions *)
    destruct ev.
    - (* Empty Event *)
      apply* LemmaHighEvent.
    - (* Assignment Event *)
      destruct l.
      + (* l is Low *)
        apply* LemmaLowEvent.
      + (* l is High *)
        applys* LemmaHighEvent.
  }
Qed.
