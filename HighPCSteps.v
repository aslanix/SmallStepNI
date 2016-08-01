(** Properties of the computation when the program counter is high *)

(*   
  Author: Aslan Askarov
  File Created: 2016-07-26 (the content is from 2015)
 *)


Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.
Require Import Omega.

Set Implicit Arguments.

Require Import Identifier Environment Imperative Types Augmented
        Bridge BridgeTactics BridgeProperties.
Require Import WellFormedness LowEq. (* NIexp. *)
Require Import UtilTactics.







(* Note that this lemma is defined in terms of basic steps >> 2015-04-03 *)

(** The main lemma in this file states that a program typed with a
high pc-label does not update low parts of the memory. Formally, this
means that the initial and the final memories are low-equivalent. The
proof procedes by induction on the command.  *)

Lemma high_pc_does_not_update_low_states:
  forall Γ  c m c_end s,
    -{Γ, High ⊢ c}- ->
    〈 c, m 〉⇒ 〈 c_end, s 〉 ->
    wf_mem m Γ
    -> state_low_eq Γ m s.
Proof.
  intros Γ c m c_end s H_wt H H_wf.
  cmd_cases (dependent induction c) Case.
  Case "STOP". 
  {
    exfalso.
    eapply wt_programs_are_not_stop; eauto.
  }


  Case "SKIP".
  {
    inversion H;  crush.
    apply state_low_eq_wf_refl; auto.
  }
  Case "::=".
  {
    inversion H; crush.

    match goal with
      | [ H: context [STOP] |- _ ] =>
        apply preservation with ( Γ := Γ) (pc := High) in H; auto
    end.

    destruct_conj; cleanup.
    apply state_low_eq_; auto; intros.
    repeat
      match goal with
        | [ H : wf_mem _ Γ |- _] =>
          unfold wf_mem in H;
            destruct_conj; repeat specialize_gen
        | [ H: exists _, _ x = Some _  |- _ ] => destruct H
      end.

    match goal with
        [  _ : m x = Some ?U, _ : _ x = Some ?V |- _ ] =>
        apply var_low_eq_ with (ℓ := ℓ) (u := U) (v := V)
    end; auto.
    unfold update_st in *;   unfold update_env in *.
    inversion H_wt; subst.
    assert (ℓ' = High) by (destruct ℓ'; crush); subst.
    destruct (eq_id_dec i x); subst.
    {
      assert (ℓ  = High) by (crush; auto).
      subst;
        constructor.
    }
    {
      assert (x0 = x1) by (crush; auto).
      subst.
      apply val_low_eq_refl.
    }
  }
  Case ";;".
  (* this is the only place where we will be using the IH? *)
  {
    inversion H_wt;
    inversion H; subst;
    match goal with
        [ H : 〈c1, m 〉 ⇒ 〈?C, s 〉 |- _  ]
        =>      specialize (IHc1  m C  s H4 H H_wf); auto
    end.
  }
  Case "IFB".
  {
    inversion H; apply state_low_eq_wf_refl; crush.
  }
  Case "WHILE".
  {
    inversion H; apply state_low_eq_wf_refl; crush.

  }
Qed.


(** We lift the above proof to the event step relation *)


Lemma high_pc_does_not_update_low_states_event_step:
  forall Γ e c m c_end s,
    -{Γ, High ⊢ c}- ->
    event_step Γ e 〈 c, m 〉 〈 c_end, s 〉 ->
    wf_mem m Γ
    -> state_low_eq Γ m s /\ high_event Γ Low e.
Proof.

  intros Γ e c m c_end s H_wt H H_wf.
  event_step_cases (dependent induction H) Case; subst;

  (* the easy case delegates the prove to the parent lemma
     and also applies that empty event is high *)
  let immediate_base_case :=
      (split;
       [ eapply high_pc_does_not_update_low_states; eauto |
         apply empty_event_is_high])
  in match goal with
       | [ H : context [SKIP] |- _ ] => immediate_base_case
       | [ H : context [ IFB _ THEN _ ELSE _ FI] |- _ ] => immediate_base_case
       | [ H : context [ WHILE _ DO _ END ]  |- _ ] => immediate_base_case
       | [ H : context [_ ;; _ ] |- _ ]  =>
         (* inductive cases *)
         (inverts~ H_wt; eapply IHevent_step; auto)
         (* we consider the remaining base cases *)
       | _ => idtac
     end.

  - Case "event_step_assign".
    split.
    + eapply high_pc_does_not_update_low_states; eauto.
    + unfolds. unfolds. intros.
      assert ( ℓ = High ).
      {
        inverts H_wt.
        match goal with | [ H : High ⊑ _ |- _ ] => inverts H end.
        congruence.
      }
      subst.
      repeat
        let H :=
          match goal with
            | [ H: context [low_event] |- _ ] => H
            | [ H: High ⊑ Low |- _ ] => H
          end
        in inverts H.

Qed.

(** Finally, it is also lifted to the bridge relation *)


Lemma high_pc_bridge:
            forall n Γ c m ev c_end m_end,
              -{ Γ, High ⊢ c }- ->
              wf_mem m Γ ->
              〈c, m 〉 ⇨+/(SL, Γ, ev,  n) 〈c_end, m_end 〉->
              state_low_eq Γ m m_end /\ c_end = STOP /\ high_event Γ Low ev.
Proof.
  intro n; induction n; intros.
  -  invert_bridge_step_num.
     + invert_low_event_step.

       _eapply_in_ctxt event_step high_pc_does_not_update_low_states_event_step; eauto.
       super_destruct.
       contradiction.
     + invert_high_event_step.
       splits.
       * _eapply_in_ctxt event_step high_pc_does_not_update_low_states_event_step; eauto.
         super_destruct; auto.
       * eapply is_stop_config_inversion; eauto.
       * apply empty_event_is_high.

  - match goal with | [H : context [bridge_step_num] |- _ ] => inverts H end.
    destruct cfg' as [c' m'].
    specialize (IHn Γ c' m' ev c_end m_end).


    match goal with [H : context [high_event_step ] |-_  ]=> inverts~ H end.
    assert (state_low_eq Γ m m')
      by (eapply high_pc_does_not_update_low_states_event_step; eauto).

    asserts [?H ?H] : (-{ Γ, High ⊢ c' }- /\ wf_mem m' Γ ).
    { (eapply preservation_event_step in H1; eauto;
       destruct H1 as [wf_m' H_non_stop];
       split; [eapply H_non_stop; eapply is_not_stop_config_inversion| idtac];
       eauto).
    }

    specializes IHn; eauto.
    super_destruct.
    splits; auto.
    eapply state_low_eq_trans; eauto.

Qed.
