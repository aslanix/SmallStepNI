Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.



Set Implicit Arguments.


Require Import Identifier Environment.
Require Import Imperative UtilTactics.
Require Import Types Augmented.



Hint Resolve eq_exp_dec : Sec.
Hint Resolve eq_id_dec : Sec.
Hint Resolve eq_cmd_dec : Sec.
Hint Resolve eq_level_dec : Sec.
Hint Resolve eq_event_dec: Sec.
(* Hint Resolve eq_obs_dec : Sec. *)
(* Hint Resolve multi_refl : Sec. *)
Hint Resolve flowsto_sym : Sec.
Hint Resolve high_does_not_flow_to_low :Sec.
(* Hint Resolve config_is_stop_config : Sec. *)


Lemma pc_lowering:
        forall Γ pc c pc',
          -{ Γ, pc' ⊢ c}- -> pc ⊑ pc' -> -{ Γ, pc ⊢ c}-.
Proof.
  intros.
  dependent induction H; try constructor; eauto.
  {
    apply T_Assign with (ℓ := ℓ) (ℓ' := ℓ') ;auto.
    destruct pc0, ℓ', pc; eauto.
  }
  {
    apply T_If with (ℓ := ℓ) (pc' := pc'); auto.
    destruct pc', pc0, pc; eauto.
  }
  {
    apply T_While with (ℓ := ℓ) (pc' := pc'); auto.
    destruct pc', pc0, pc; eauto.
  }
Qed.


Definition wf_mem (m:state )  ( Γ: typenv): Prop :=
  (forall x u, m x = Some u-> exists ℓ, Γ x = Some ℓ)
  /\
 (forall  x ℓ, Γ x = Some ℓ -> exists u, m x = Some u).


Definition wt_cfg (cfg: config) ( Γ: typenv) (pc: level): Prop :=
  match cfg with
    | Config c m => wf_mem m Γ /\ ( c <> STOP -> -{ Γ, pc ⊢ c }- )
  end.
Hint Unfold wt_cfg.
     
Notation  "'={' Γ ',' pc '⊢' cfg '}='" := 
  (wt_cfg cfg Γ pc ) (at level 40).

Local Hint Resolve eq_nat_dec.

(* TODO : move this hint someplace else *) 
Hint Extern 4 (_ <> STOP) => let X:= fresh in unfolds; intros X; inverts X. 

Theorem preservation_cfg:
  forall Γ pc cfg cfg',
    ={ Γ, pc ⊢ cfg }= ->
    cfg ⇒ cfg' ->
    ={ Γ, pc ⊢ cfg'}= .

Proof.
  intros Γ pc [c m] [c' m'] [H_wt ?H] H_step.
  cmd_cases (dependent induction c) Case.
  Case "STOP". inversion H_step.
  Case "SKIP". inversion H_step; subst~ ; split *.
  Case "::=". 
  {
    inverts H_step.
    specializes* H.

    splits*.
    splits*.
    - intros. compare i x; eauto; intros; subst.
      + inverts*  H.
      + unfolds wf_mem.
        destruct H_wt as [H_wf_mem ?].
        assert (m x = Some u).
        {
          unfolds update_st. unfold update_env in *.
          destruct eq_id_dec; subst*.
        }
        specializes H_wf_mem x u __.
    - intros.
      compare i x; intros; subst*.
      + (exists v).
        unfold update_st.
        unfold update_env.
        destruct eq_id_dec; subst* .
      + unfold wf_mem in H_wt.
        destruct H_wt as [? ?H_wt_mem].
        unfold update_st.
        unfold update_env.
        destruct eq_id_dec; subst*.
  }
  Case ";;".
  {
    specializes* H.
    inverts* H.
    inverts* H_step.
    - specializes* IHc1.
      lets (X & Y): IHc1.
      specialize_gens.
      econstructor; intros; eauto.
      constructor; auto.
    - specializes* IHc1.
      lets (X & Y): IHc1.
      unfolds. split*.
  }
  Case "IFB".
  {
    specializes* H.
    inverts* H.
    inverts* H_step;
      split*;
      intros;
      applys* pc_lowering.
  }
  Case "WHILE".
  {
    specializes *H.
    inverts *H.
    inverts* H_step.
    split*; intros.
    apply T_If with (ℓ:=ℓ) (pc' := pc'); repeat constructor; auto. 
    apply T_While with (ℓ:=ℓ) (pc' := pc'); repeat constructor; auto.
  }
Qed.


Theorem preservation:
  forall Γ c m c' m' pc,
    -{ Γ, pc ⊢ c}- ->
    step 〈c, m 〉 〈c', m' 〉->
    wf_mem m Γ ->
    wf_mem m' Γ /\ ( c' <> STOP -> -{Γ, pc ⊢ c'}- ).
Proof.
  intros Γ c m c' m' pc H_wt H H_wf.
  forwards* : preservation_cfg.
  unfolds.
  split *.
Qed.

(* liftings of preservation to various relations. *)


Lemma event_step_inversion:
  forall Γ ev cfg cfg',
    event_step Γ ev cfg cfg' ->
    step cfg cfg'.
Proof.
  intros.
  dependent induction H; auto; repeat (constructor; auto).

Qed.    

Hint Rewrite event_step_inversion.

Lemma preservation_evt_cfg:
  forall Γ evt pc cfg cfg',
  ={ Γ, pc ⊢ cfg }= ->
  event_step Γ evt cfg cfg' ->
  ={ Γ, pc ⊢ cfg'}= .

Proof.
  intros.
  forwards* : event_step_inversion.
  applys* preservation_cfg.
Qed.


Lemma preservation_event_step:
  forall Γ e c m c' m' pc,
    -{ Γ, pc ⊢ c}- ->
    event_step Γ e 〈c, m 〉 〈c', m' 〉->
    wf_mem m Γ ->
    wf_mem m' Γ /\ ( c' <> STOP -> -{Γ, pc ⊢ c'}- ).
Proof.
  intros.
  forwards * : preservation_evt_cfg.
  unfolds.
  split *.
Qed.