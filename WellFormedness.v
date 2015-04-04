Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.



Set Implicit Arguments.


Require Import Identifier Environment.
Require Import Imperative UtilTactics.


Hint Resolve eq_exp_dec : Sec.
Hint Resolve eq_id_dec : Sec.
Hint Resolve eq_cmd_dec : Sec.
Hint Resolve eq_level_dec : Sec.
Hint Resolve eq_event_dec: Sec.
Hint Resolve eq_obs_dec : Sec.
Hint Resolve multi_refl : Sec.
Hint Resolve flowsto_sym : Sec.
Hint Resolve high_does_not_flow_to_low :Sec.
Hint Resolve config_is_stop_config : Sec.


Lemma pc_lowering:
        forall Γ pc c pc',
          { Γ, pc' ⊢ c} -> pc ⊑ pc' -> { Γ, pc ⊢ c}.
Proof.
  intros.
  dependent induction H; try constructor; crush.
  {
    apply T_Assign with (ℓ := ℓ) (ℓ' := ℓ') ;auto.
    destruct pc0, ℓ', pc; crush.
  }
  {
    apply T_If with (ℓ := ℓ) (pc' := pc'); auto.
    destruct pc', pc0, pc; crush.
  }
  {
    apply T_While with (ℓ := ℓ) (pc' := pc'); auto.
    destruct pc', pc0, pc; crush.
  }
Qed.


Definition wf_mem (m:state )  ( Γ: typenv): Prop :=
  (forall x u, m x = Some u-> exists ℓ, Γ x = Some ℓ)
  /\
 (forall  x ℓ, Γ x = Some ℓ -> exists u, m x = Some u).


Theorem preservation:
  forall Γ c m c' m' pc,
    { Γ, pc ⊢ c} ->
    step 〈c, m 〉 〈c', m' 〉->
    wf_mem m Γ ->
    wf_mem m' Γ /\ ( c' <> STOP -> {Γ, pc ⊢ c'} ).
Proof.
  intros Γ c m c' m' pc H_wt H H_wf.
  cmd_cases (dependent induction c) Case.
  Case "STOP".
  {
    inversion H.
  }
  Case "SKIP".
  {
    inversion H.
    subst; auto.
    split.
    auto.
    crush.
  }
  Case "::=".
  {
    inversion H.
    inversion H_wt.
    subst.
    split; [idtac | crush].
    unfold wf_mem in *.
    split.
    {
      intros.
      unfold update_st; unfold update_env. 
      destruct H_wf as [ H_wf' H_wf''].
    
      compare i x; try apply eq_nat_dec; intros.
      {
        rewrite -> e0 in *.
        exists ℓ'.
        auto.
      }
      {
        unfold wf_mem in *.
        specialize (H_wf' x u).
        unfold update_st in *; unfold update_env in *.
        destruct eq_id_dec. crush.
        specialize (H_wf' H0).
        auto.
      }

    }
    {
      intros.
      unfold update_st; unfold update_env.
      destruct H_wf as [ H_wf' H_wf''].
      compare i x; try apply eq_nat_dec; intros.
      {
        exists v.
        destruct eq_id_dec; crush.
      }
      {
        specialize (H_wf'' x ℓ0).
        unfold update_st in *; unfold update_env in *.
        destruct eq_id_dec; crush.
      }
    }
  }
  Case ";;".
  {
    inversion H_wt.
    inversion H; auto; subst.

      
    {
      specialize (IHc1 m c1' m' pc H4 H8 H_wf); 
      split; crush.
      intros.
      apply T_Seq; auto.
    }
    {
      specialize (IHc1 m STOP m' pc H4 H7 H_wf); crush.
    }
  }
  Case "IFB".
  {
    inversion H_wt; 
    inversion H; subst;

      split; auto;

      intros;
      apply pc_lowering with (pc' := pc'); auto.
  }
  Case "WHILE".
  {
    inversion H_wt; inversion H; subst.
    split; auto.
    intros.
    apply T_If with (ℓ:=ℓ) (pc' := pc'); auto; try constructor; auto.
    apply T_While with (ℓ:=ℓ) (pc' := pc'); auto; try constructor; auto.

  }
Qed.


(* liftings of preservation to various relations. *)

Lemma preservation_event_step:
  forall Γ e c m c' m' pc,
    { Γ, pc ⊢ c} ->
    event_step Γ e 〈c, m 〉 〈c', m' 〉->
    wf_mem m Γ ->
    wf_mem m' Γ /\ ( c' <> STOP -> {Γ, pc ⊢ c'} ).
Proof.
  intros.
  dependent induction H0; subst;
  try 
    match goal with
      | [ H : 〈?C, ?M 〉 ⇒ 〈?C', ?M' 〉, H': wf_mem ?M Γ |- _ ] =>
        apply preservation with (c := C) (m := M); auto
    end.



  {
  inversion H;
  repeat specialize_gen;
  destruct_conj;
    split; auto;
  intros;
  repeat specialize_gen;
  constructor; assumption.
  }
  {
    inv_event_step; subst; auto.
    split.

     match goal with
      | [ H : 〈?C, ?M 〉 ⇒ 〈?C', ?M' 〉, H': wf_mem ?M Γ |- _ ] =>
        apply preservation with ( Γ := Γ) (pc := pc)  in H; auto
     end.
     destruct_conj; auto.
     inversion H; crush.
     intros.
     inversion H; crush.
     false.
  }
  {
    inv_event_step; subst; auto.
     match goal with
      | [ H : 〈?C, ?M 〉 ⇒ 〈?C', ?M' 〉, H': wf_mem ?M Γ |- _ ] =>
        apply preservation with ( Γ := Γ) (pc := pc)  in H; auto
     end.
     split; auto.

     intros.
     inversion H; crush.
     constructor.
  }
Qed.  





Lemma preservation_nh_event:
  forall Γ pc c m c_end s, 
    { Γ, pc ⊢ c} ->
    〈 c, m 〉⇒/(H, Γ) 〈 c_end, s 〉 ->
    wf_mem m Γ ->
    wf_mem s Γ /\ (c_end <> STOP -> {Γ, pc ⊢ c_end}  ).

Proof.
  intros.
  inversion H0;
  match goal with 
      | [ H: event_step _ ?EV _ _ |- _ ] =>              
        apply preservation_event_step with (e:=EV) (c:=c) (m:=m); crush
  end.
Qed.



