Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.


Set Implicit Arguments.


Require Import Identifier Environment Imperative UtilTactics.


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


Ltac super_destruct_split_sec :=
  repeat (destruct_split; subst; auto with Sec).


Ltac env_is_det Γ :=
  match goal with 
    | [ H: Γ ?x = Some ?ℓ1 , H':  Γ ?x = Some ?ℓ2 |- _ ]
      => assert (ℓ1 = ℓ2) by
          (inversion H; inversion H'; congruence)
  end.



                


Ltac contra_env_is_det Γ :=
  match goal with 
    | [ H: Γ ?x = ?F , H':  Γ ?x <> ?F |- _ ]
      => (destruct H, H'; congruence)
  end.
      
Ltac destruct_var_level Γ x:=
  match goal with 
    | [ H: Γ x = Some ?L |- _] => destruct L
  end.


Ltac specialize_levels Γ :=
  match goal with 
              [  H  : Γ  ?X = Some ?L -> _ , 
                 H' : Γ  ?X = Some ?L |- _] =>
              specialize (H H')
  end.
        



Ltac clear_na_levels Γ :=
  match goal with 
    |   [  H  : Γ  ?X <> Some ?L -> _ , 
           H' : Γ  ?X = Some ?L |- _] =>
        clear H
    |   [  H  : Γ  ?X = Some ?L -> _ , 
           H' : Γ  ?X <> Some ?L |- _] =>
        clear H                     
  end.


Ltac super_destruct_var_level Γ x:=
  destruct_var_level Γ x;
  try (contra_env_is_det Γ);
  repeat specialize_levels Γ;
  repeat clear_na_levels Γ.
  






 
(*** low_bridge_step ***)



(** 2015-03-25: the plan is to try a different formulation **)

Inductive bridge_step: 
  typenv -> level -> config -> config -> obs -> Prop :=
| bridge_low:
    forall Γ ℓ cfg cfg' obs,
      low_or_stop_event Γ ℓ cfg cfg' obs ->
      bridge_step Γ ℓ cfg cfg' obs

| bridge_nh: 
    forall Γ ℓ cfg cfg' cfg'' obs,
      nonstophigh_or_empty_event Γ ℓ cfg cfg' ->
      bridge_step Γ ℓ cfg' cfg'' obs ->
      bridge_step Γ ℓ cfg cfg'' obs.

Tactic Notation "bridge_cases" 
tactic (first) ident (c) :=
 first; 
 [ Case_aux c "bridge_low" 
 | Case_aux c "bridge_nh" ].


Notation " t '⇒+/(SL,' Γ ',' obs ')'  t' " :=
  (bridge_step Γ Low t t' obs) (at level 40).





Ltac inv_bridge:=
  match goal with
      [ H : _  ⇒+/(SL, _, _) _ |- _ ] => inversion H
  end.








Lemma stop_makes_no_bridge_steps: 
  forall Γ i c m m',
    〈STOP, m 〉⇒+/(SL, Γ, i) 〈c,m'〉 ->
    False.

Proof.
  intros.
  bridge_cases (inversion H) Case;
  match goal with 
      |[ H: context [ _  ⇒/(SL, _, _) _ ] |- _] 
         => inversion H
      | [H : context [ _ ⇒/(NH, _) _ ] |- _] 
        => inversion H
  end; inv_event_step; crush.
Qed.


Lemma low_assignments_are_bridge_events:
  forall Γ ℓ x u c c' m m',
    ℓ  ⊑ Low ->
    event_step Γ (AssignmentEvent ℓ x u) 〈c, m 〉 〈c', m' 〉->
    〈c, m 〉 ⇒+/(SL, Γ, Effect ℓ x u)〈c', m' 〉.
Proof.
  intros.
  repeat constructor; crush.
Qed.


Lemma seq_decomp_low: 
    forall Γ i ca cb m c_end m_end,
      〈ca;; cb, m 〉 ⇒+/(SL, Γ, i)〈c_end, m_end 〉->
      ca <> STOP -> 
      cb <> STOP ->
      (exists ca_mid,
         〈 ca, m 〉⇒+/(SL, Γ, i)〈ca_mid, m_end 〉/\
         (ca_mid <> STOP -> c_end = (ca_mid;; cb)) /\
         (ca_mid = STOP ->  c_end = cb) /\
         is_low_effect i
      )
      \/
      (exists s,
         〈 ca, m 〉⇓/(H, Γ)  s /\
         〈 cb, s 〉⇒+/(SL, Γ, i)〈c_end, m_end 〉
      ).
Proof.
  intros.  

  bridge_cases (dependent induction H) Case.
  Case "bridge_low".
  {        
    left.
    apply first_seq_comp_low_step in H.
    destruct H as [ca']. 
    super_destruct.
    exists ca'; repeat split; try constructor; auto.
  }
  Case "bridge_nh".
  {        
    match goal with 
        [ H: context [ _ ⇒/(NH, Γ) ?cfg'] |- _] 
        => destruct cfg'; 
          apply first_step_comp_nonstop_high_step in H;
          destruct H as [ca'];
          super_destruct
    end.    
    compare ca' STOP; auto with Sec; intros SS; cleanup.
    SCase "ca' = STOP".
    {
      right; 
      exists st; split; cleanup;
      try (apply high_step_converges with 〈ca, m 〉); 
      auto with Sec.
    }
    SCase "ca' <> STOP".
    {
      match goal  with
              | [ H : context [_  ⇒/(H, Γ)  _ ] |- _ ] =>
                apply high_event_to_nonstop_high_event in H; auto
      end.

      specialize_gen; cleanup.
      specialize (IHbridge_step ca' cb st c_end m_end).
      assert (〈ca';; cb, st 〉 = 〈ca';; cb, st 〉) as XX by auto.
      assert (〈ca';; cb, st 〉 = 〈ca';; cb, st 〉) as YY by auto.
      repeat specialize_gen.
      clear XX YY.
      
      destruct IHbridge_step; [left | right ]; super_destruct;
      repeat 
        match goal with 
          | [ H : 〈ca', st 〉 ⇒+/(SL, Γ, obs)〈?CC, m_end 〉 |- _ ]
            => (exists CC); 
              super_destruct_split;
              apply bridge_nh with (cfg' := 〈  ca', st 〉)
          | [ H: 〈ca', st 〉 ⇓/(H, Γ) ?M |- _ ]
            => (exists M); 
              super_destruct_split; 
              apply high_step_converges_alt with ca' st
        end; auto.       
    }   
  }
Qed.  
  
    


Lemma skip_bridges_no_mem_change: 
  forall Γ obs m c m',
    〈 SKIP, m 〉 ⇒+/(SL, Γ, obs)〈c, m' 〉->
                  c = STOP /\ m' = m /\ obs = Halt.
Proof.
  intros; inversion H; subst.
  {
    assert (c = STOP /\ m' = m) as X' by
          (lift_inversion_low 〈SKIP, m 〉; crush);
    rewrite_conj X';inv_sl_step; try (inv_event_step_no_clear); crush.
  }
  {
    destruct cfg'.
    inv_nh_step; inv_event_step_clear.
  }
  
Qed.



Lemma assign_bridges_to_stop_val : 
  forall Γ o x e m c_end m_end,                                    
    〈x ::= e, m 〉 ⇒+/(SL, Γ, o)〈c_end, m_end 〉->
    c_end = STOP /\
    (exists v, 
       (eval e m v /\ m_end = update_st m x v) /\
       ( Γ x = Some Low -> o = Effect Low x v) /\
       ( Γ x = Some High -> o = Halt )
    ).
Proof.
  intros.
  inv_bridge;
  repeat split;

  try match goal with 
       | [ H : context [ _ ⇒/(NH, _) ?cfg' ] |- _ ] =>
         destruct cfg'; inv_nh_step; inv_event_step; cleanup;
         inv_non_stop_config; crush
       | [ |- c_end = STOP ] => 
        compare c_end STOP; auto with Sec; inv_sl_step;
        try (inv_non_stop_config); try (inv_stop_config); crush;
        inv_event_step; auto
    end;
  
  inv_sl_step; inv_event_step; crush;
  repeat 
    match goal with
        [ H : _ ⇒ _ |- _ ] => inversion H; clear H 
      | [ U:  eval e m ?u, V : eval _ _ ?v |- _ ] 
        => (exists u); crush; assert (u = v) by tt_eval_is_det; subst;
           clear U V
    end; auto.
Qed.
  



Lemma assign_bridges_to_stop_val_inversion : 
  forall Γ o x e m c_end m_end,                                    
    〈x ::= e, m 〉 ⇒+/(SL, Γ, o)〈c_end, m_end 〉-> 
    〈x ::= e, m 〉 ⇒/(SL, Γ, o)〈c_end, m_end 〉/\
    c_end = STOP /\
    (exists v, 
       (eval e m v /\ m_end = update_st m x v) /\
       ( Γ x = Some Low -> o = Effect Low x v) /\
       ( Γ x = Some High -> o = Halt )
    ).
Proof.
  intros.
  split.
  {
    inversion H; auto.
    inversion H0.
    inv_event_step_clear.
    inv_event_step_clear.
    inv_non_stop_config.
    crush.
  }
  apply assign_bridges_to_stop_val; auto.
Qed.

  
Inductive nh_step_count  : typenv -> config -> config -> nat -> Prop := 
  | nh_step_count_zero:
      forall Γ cfg, 
        nh_step_count Γ cfg cfg O
  | nh_step_count_step:
      forall Γ cfg cfg' cfg'' n,
        cfg ⇒/(NH, Γ) cfg' ->
        nh_step_count Γ cfg' cfg'' n ->

        nh_step_count Γ cfg cfg'' (S n).


Lemma from_multi_nh_to_nh_step_count:
  forall Γ cfg cfg', 
    cfg ⇒*/(NH, Γ) cfg' ->
    exists n, nh_step_count Γ cfg cfg' n.
Proof.
  intros.
  multi_cases (induction H) Case.
  {
    exists O.
    constructor.
  }
  {
    destruct IHmulti as [m IH].
    exists (S m).
    apply nh_step_count_step with (cfg' := y);
    crush.
  }
Qed.



Lemma extending_bridge_steps_nh_step:
  forall Γ obs cfg_start cfg_mid cfg_end n,
    nh_step_count Γ cfg_start cfg_mid n ->
    cfg_mid  ⇒+/(SL, Γ, obs)  cfg_end  ->
    cfg_start   ⇒+/(SL, Γ, obs)  cfg_end.
Proof.
  intros Γ obs cfg_start cfg_mid cfg_end n H1 H2.
  generalize dependent cfg_mid.
  generalize dependent cfg_start.
  induction n.
  {
    intros.
    match goal with 
      | [ H: context[nh_step_count] |- _ ] => inversion H
    end.
    crush.
  }
  {
    intros.
    match goal with 
        | [ H: context [nh_step_count] |- _ ] => inversion H; subst
    end.
    match goal with 
        | [ _ : context [_  ⇒/(NH, Γ) ?CFG],  
           H  : nh_step_count _ ?CFG _ _,
           H' :  _ ⇒+/(SL, Γ, obs) _ |- _  ] =>
          specialize (IHn CFG cfg_mid H H');
            apply bridge_nh with (cfg' := CFG); crush
    end.
    
  }
Qed.
Lemma extending_bridge_steps_nh:
  forall Γ obs cfg_start cfg_mid cfg_end,
    cfg_start  ⇒*/(NH, Γ)  cfg_mid ->
    cfg_mid  ⇒+/(SL, Γ, obs)  cfg_end  ->
    cfg_start   ⇒+/(SL, Γ, obs)  cfg_end.
Proof.
  intros.
  apply from_multi_nh_to_nh_step_count in H.
  destruct H as [n].
  apply extending_bridge_steps_nh_step with (cfg_mid:=cfg_mid) (n := n); crush.
Qed.  



Lemma from_converges_to_stop_event:
  forall Γ c m s,
    〈c, m〉 ⇓/(H, Γ) s ->
    c <> STOP ->
     〈c, m〉 ⇒+/(SL, Γ, Halt)  〈STOP, s〉.
Proof.
  intros.
  inversion H ; crush.
  apply extending_bridge_steps_nh with (cfg_mid := cfg'); crush.
  
  apply from_high_stop_event_to_low_stop_event in H2.
  constructor; auto.
Qed.  




Lemma first_seq_comp_low_step':
            forall Γ d o ca cb m m_end,
              (〈ca, m 〉 ⇒/(SL, Γ, o) 〈d, m_end 〉 ) ->
              o <> Halt ->
              cb <> STOP ->
              exists c_end, 
                〈ca;; cb, m 〉 ⇒/(SL, Γ, o) 〈c_end, m_end 〉
                /\ ( d <> STOP -> c_end = (d;; cb))
                /\ ( d =  STOP -> c_end = cb). 
Proof.
            intros.
            low_or_stop_event_cases (inversion H) Case; crush.
            
            compare d STOP; auto with Sec; intros; subst; auto;
            [exists cb | exists (d;;cb)];
              super_destruct_split_sec; auto; (try congruence);              
              apply low_or_stop_event_low_assign; auto;
              [apply event_step_seq2 | apply event_step_seq1];
              congruence.
Qed.







          
Lemma halt_ends_in_stop:
            forall Γ c m c_end m_end,
              〈c, m 〉 ⇒+/(SL, Γ, Halt)〈c_end, m_end 〉 ->
              c <> STOP ->                
              (c_end = STOP) .
Proof.
      intros. dependent induction H; auto; subst.
      
      
      {
        inv_sl_step; auto; inv_event_step;
        match goal with [ H : context[is_stop_config] |- _] => inversion H end; crush.
      }
      {
        destruct cfg'; subst.
        specialize (IHbridge_step c0 st c_end m_end); crush.
        apply nonstopcommands_do_not_end_in_stop' in H.
        crush.
      }

Qed.



Lemma seq_comp_halt: 
      forall Γ c1 c2 m c_end m_end,
        〈c1;; c2, m 〉 ⇒+/(SL, Γ, Halt)〈c_end, m_end 〉 ->
        c1 <> STOP ->
        c2 <> STOP ->                
        (exists s, 
           〈c1, m 〉 ⇒+/(SL, Γ, Halt)〈STOP, s 〉 /\
           〈c2, s 〉 ⇒+/(SL, Γ, Halt)〈STOP, m_end 〉           
        ).
Proof.
      intros; assert (H_saved := H);
      dependent induction H; auto; subst.
      
      assert (c_end = STOP ) by   (apply halt_ends_in_stop in H_saved; crush);

      subst.

      {
        match goal with 
            |[ H: 〈c1;; c2, m 〉 ⇒/(SL, Γ, Halt) 〈STOP, m_end 〉 |- _ ] =>
             inversion H
        end; inv_event_step; crush.
      }
      {
        destruct cfg'.
        match goal 
        with [ H : context [ _  ⇒/(NH, Γ) _ ] |- _ ] => 
             apply first_step_comp_nonstop_high_step in H;
               destruct H as [d]; super_destruct_split
        end.
        compare d STOP; auto with Sec; subst; super_destruct_split; specialize_gen;cleanup.
        {
          exists st; split.
          {
            apply from_high_stop_event_to_low_stop_event in H.
            constructor; auto.
          }
          {
            assert (c_end = STOP) by (apply halt_ends_in_stop in H0; crush).
            subst. assumption.
          }
        }
        {
          specialize (IHbridge_step d c2 st c_end m_end); repeat specialize_gen.
          destruct IHbridge_step as [s'].
          exists s'.
          split; super_destruct_split; subst.
          apply high_event_to_nonstop_high_event in H; auto.
          apply bridge_nh with (cfg' := 〈 d, st 〉); auto.
        }          
      }
Qed.



(* an auxiliary relation that we escape into for the 
   convenience of counting steps in the bridge events *)

Inductive bridge_step_num: 
  typenv -> level -> config -> config -> obs -> nat -> Prop :=
| bridge_low_num:
    forall Γ ℓ cfg cfg' obs,
      low_or_stop_event Γ ℓ cfg cfg' obs ->
      bridge_step_num Γ ℓ cfg cfg' obs 1

| bridge_nh_num: 
    forall Γ ℓ cfg cfg' cfg'' obs n,
      n >= 1 ->
      nonstophigh_or_empty_event Γ ℓ cfg cfg' ->
      bridge_step_num Γ ℓ cfg' cfg'' obs n ->
      bridge_step_num Γ ℓ cfg cfg'' obs (S n).

Tactic Notation "bridge_num_cases" 
tactic (first) ident (c) :=
 first; 
 [ Case_aux c "bridge_low_num" 
 | Case_aux c "bridge_nh_num" ].


Notation " t '⇨+/(SL,' Γ ',' obs ',' n ')'  t' " :=
  (bridge_step_num Γ Low t t' obs n) (at level 40).


(* from ⇒ to ⇨ *)

Lemma from_bridge_step_to_bridge_step_num:
  forall Γ cfg cfg' obs,
    cfg ⇒+/(SL, Γ, obs ) cfg' -> 
  exists n, 
    (n >= 1) /\  cfg ⇨+/(SL, Γ, obs, n ) cfg'.
Proof.
  intros.
  dependent induction H.
  {
    exists 1. split; constructor; auto.
  }
  {
    destruct IHbridge_step as [m].
    destruct H1.
    exists (S m).
    split; auto.
    apply bridge_nh_num with (cfg' := cfg'); auto.
  }
Qed.


Lemma from_bridge_step_num_to_bridge_step:
  forall Γ cfg cfg' obs n, 
    cfg ⇨+/(SL, Γ, obs, n ) cfg'  ->
    cfg ⇒+/(SL, Γ, obs ) cfg'.
Proof.
  intros; dependent induction H.

  {
    constructor; auto.
  }
  {

    apply bridge_nh with (cfg' := cfg'); auto.
  }
Qed.


Ltac tt_from_bridge_step_num_to_bridge_step:=
  match goal with
      | [H :  context [_ ⇨+/(SL, _, _, _ ) _ ]  |- _ ] => 
        apply from_bridge_step_num_to_bridge_step in H 
  end.

  
Hint Resolve low_effects_are_effects : Sec.


Ltac inv_effect:=
  match goal with 
      [ H: context [is_effect _ ] |- _ ]  => inversion H
  end.

Ltac inv_low_effect:=
  match goal with 
      [ H: context [is_low_effect _ ] |- _ ]  => inversion H
  end.




Ltac inv_bridge_num:= 
 match goal with
      | [H :  context [_ ⇨+/(SL, _, _, _ ) _ ]  |- _ ] => 
        inversion H
  end.





(* 2015-03-31: an aux lemma, could probably be
           strengthened, but i'm keeping it brief for now. *)
Lemma seq_comp_decomp_nh: 
          forall Γ c1 c2 m cfg,
          〈c1;; c2, m 〉 ⇒/(NH, Γ) cfg-> exists cfg',
          〈c1, m 〉 ⇒/(H, Γ) cfg'.
Proof.
          intros.
          inversion H; subst; inv_event_step_clear; auto;
          match goal with 
              | [ H: event_step _ _ 〈c1, m 〉 ?CFG |- _ ] 
                => (exists CFG); subst; auto
          end;
          repeat           
            match goal with
              | [H : event_step _ EmptyEvent 〈 c1, m 〉 ?CFG |- _ ] 
                   => apply high_term_event_other 
                      with (ℓ := Low) in H; auto

              | [H : event_step _ StopEvent 〈 c1, m 〉 ?CFG |- _ ] 
                   => apply high_term_event_other 
                      with (ℓ := Low) in H; auto

              | [H : event_step _ (AssignmentEvent _ _ _) 〈 c1, m 〉 ?CFG |- _ ] 
                   =>  
                   apply high_event_assign with (ℓ := Low) in H; auto
              
            end.
            
Qed.


Ltac tt_impossible_bridge_num_consntructor:=
  assert (0 >=1 -> False) by omega; 
  repeat specialize_gen; 
  contradiction.




Lemma first_seq_comp_low_step'' : 
  forall Γ o ca cb m m_end,
    〈 ca, m 〉 ⇒/(SL, Γ, o) 〈 STOP, m_end 〉 ->
    cb <> STOP ->
    is_low_effect o ->
    〈 ca;; cb, m 〉 ⇒/(SL, Γ, o) 〈 cb, m_end 〉.
Proof.
  intros.              
  low_or_stop_event_cases (inversion H) Case; inv_low_effect; crush;
  apply event_step_seq2  with (c2 := cb) in H2;
  try constructor; auto.
Qed.
            





Lemma seq_decomp_low_num: 
        forall Γ n o ca cb m c_end m_end,
          〈ca;; cb, m 〉 ⇨+/(SL, Γ, o, n)〈c_end, m_end 〉->
          ca <> STOP -> 
          cb <> STOP ->
          (exists ca_mid,
             〈 ca, m 〉⇨+/(SL, Γ, o, n)〈ca_mid, m_end 〉/\
             (ca_mid <> STOP -> c_end = (ca_mid;; cb)) /\
             (ca_mid = STOP ->  c_end = cb) /\
             is_low_effect o
          )
          \/
          (exists k k' s,
             〈 ca, m 〉 ⇨+/(SL, Γ, Halt, k) 〈 STOP, s 〉 /\
             〈 cb, s 〉⇨+/(SL, Γ, o, k')〈c_end, m_end 〉 /\
              k < n /\ k' < n /\ k + k' = n
          ).

Proof.
        intros. 
        bridge_num_cases (dependent induction H) Case.
        Case "bridge_low_num".
        {
          left.
          apply first_seq_comp_low_step in H.
          destruct H as [ca'].
          super_destruct.
          exists ca'; repeat split; try constructor; auto.
        }
        Case "bridge_nh_num".
        {
          match goal with 
              [ H: context [ _ ⇒/(NH, Γ) ?cfg'] |- _] 
              => destruct cfg'; 
                apply first_step_comp_nonstop_high_step in H;
                destruct H as [ca'];
                super_destruct
          end.  
          compare ca' STOP; auto with Sec; intro SS; cleanup.
          SCase "ca' = STOP".
          {
            right; 
            exists 1 n st; repeat split; cleanup;
            try 
              match goal with 
                | [ H : _  ⇒/(H, Γ) _ |- _  ] =>
                  apply from_high_stop_event_to_low_stop_event in H;
                apply bridge_low_num in H
              end;auto; omega.
          }
          SCase "ca' <> STOP".
          {
            match goal with 
                | [H : context [ _  ⇒/(H, Γ) _ ] |- _ ] =>
                  apply high_event_to_nonstop_high_event in H; auto
            end.
            specialize_gen;cleanup.
             specialize (IHbridge_step_num ca' cb st c_end m_end).
             assert (〈ca';; cb, st 〉 = 〈ca';; cb, st 〉) as XX by auto.
             assert (〈ca';; cb, st 〉 = 〈ca';; cb, st 〉) as YY by auto.
             repeat specialize_gen.
             clear XX YY.
             
             destruct IHbridge_step_num; [left | right ]; super_destruct.
             {
               
               match goal with 
                 | [ H : 〈ca', st 〉⇨+/(SL, Γ, obs, ?N)〈?CC, m_end 〉 |- _ ]
                   => (exists CC); rename CC into cmd_
                        
               end.
               super_destruct_split.

               match goal with
                   |  [H : _  ⇒/(NH, Γ) _ |- _ ] 
                        => apply bridge_nh_num with  
                             (cfg'' := 〈 cmd_, m_end 〉) 
                               (n := n)
                             (obs :=obs) 
                          in H; auto; inv_bridge_num; auto
               end.
             }
             {
               match goal with 
                 | [ H :  〈ca', st 〉⇨+/(SL, Γ, Halt, ?N)〈STOP, ?M 〉,
                     H':  〈cb,  ?M〉 ⇨+/(SL, Γ, obs, ?N') 〈c_end, m_end 〉
                     |- _ ]
                   => 
                   rename N into k0; 
                     rename N' into k';
                     rename M into s;
                     exists (S k0) k' s
               end.               
               subst.
               repeat split; auto.
               match goal with
                   |  [H : _  ⇒/(NH, Γ) _ |- _ ] 
                        => apply bridge_nh_num with  
                           (cfg' := 〈  ca', st 〉) 


               end; auto;
               inversion H4; auto.
               omega.
             }
          }
        }
Qed.





Lemma seq_comp_nh_tail: (* 2015-04-02; TODO: streamline this proof. *)
  forall Γ c1 c2 m s,
    c2 <> STOP ->
    〈 c1, m 〉 ⇒+/(SL, Γ, Halt) 〈 STOP, s 〉 ->
    〈 c1;; c2, m 〉 ⇒*/(NH, Γ) 〈 c2, s 〉.
Proof.
  intros.
  bridge_cases (dependent induction H0) Case.
  {
    inversion H0; subst.
    {
      assert (ev = StopEvent) as E by (destruct H3; inv_event_step; crush).
      clear H3; subst.      
      assert (m = s) by (inversion H1; auto); subst.
      assert (event_step Γ EmptyEvent 〈 c1;; c2, s 〉 〈 c2, s 〉) 
        by ( apply event_step_seq3; auto).      
      assert (〈c1;; c2, s 〉 ⇒/(NH, Γ) 〈c2, s 〉 ) by (constructor; auto).
      apply multi_step with 〈c2, s 〉; auto.
      apply multi_refl.
    }
    {
      assert (event_step Γ (AssignmentEvent ℓ' x u) 〈c1;;c2, m 〉 〈c2, s 〉)
             by  (apply event_step_seq2; auto).
      assert (〈c1;; c2, m 〉 ⇒/(NH, Γ) 〈c2, s 〉 ).
      {
        apply nonstophigh_or_empty_event_assign with (ℓ' := ℓ' ) ( x := x ) (u := u);
        auto;
        constructor; auto.
      }      
      apply multi_step with 〈c2, s 〉; auto.
      apply multi_refl.
    }
  }
  Case "bridge_nh".
  {
    destruct cfg'.
    
    apply nonstop_high_event_is_a_high_event_and_does_not_end_in_stop in H1.
    destruct_conj.
    
    
    apply first_step_comp_high_step' with (cb := c2)in H1; auto.
    destruct_exists; destruct_conj.
    specialize (H3 H2); subst.

    assert ((c;;c2) <> STOP) by crush.
    apply high_event_to_nonstop_high_event in H1; auto.
    specialize (IHbridge_step c st s).
    repeat specialize_gen.
    apply multi_step  with (y := 〈 c;; c2, st 〉); auto.
  }

Qed.

Lemma seq_comp_nh_tail':
  forall Γ c1 c2 d m m' s, 
    c2 <> STOP ->
    〈 c1, m 〉 ⇒+/(SL, Γ, Halt) 〈 STOP, m' 〉 ->
    〈 c2, m' 〉 ⇒*/(NH, Γ) 〈 d, s 〉 ->
    〈 c1;; c2, m 〉 ⇒*/(NH, Γ) 〈 d, s 〉.
Proof.
  intros.
  apply seq_comp_nh_tail with (c2 := c2) in H0; auto.
  apply multi_trans with (y := 〈 c2, m' 〉 ); auto.
Qed.            



Ltac impossible_sl_step:=             
  inv_sl_step; subst; auto;
  inv_event_step; subst; auto;
  inv_stop_config;
  congruence.

Ltac inv_step:=
    match goal with 
                | [ H : _ ⇒ _  |- _ ] => inversion H
    end.

Lemma while_step_count_decreases:
  forall n Γ e o c m c_end m_end,
    〈 WHILE e DO c END, m 〉 ⇨+/(SL, Γ, o, S n) 〈c_end, m_end 〉 ->
    〈 IFB e THEN c;; WHILE e DO c END ELSE SKIP FI, m 〉 ⇨+/(SL, Γ, o, n) 〈c_end, m_end 〉.
Proof.
  intros.
  bridge_num_cases (inversion H) Case.
  {
    impossible_sl_step.
  }
  {
    inv_nh_step; subst; auto; inv_event_step; subst; auto.
    inv_step; crush.
  }

Qed.


Lemma exists_predecessor:
  forall x, x >= 1 -> exists x' , S x' = x.
Proof.
  intros.
  induction H.
  exists 0.
  auto.
  exists m.
  auto.
Qed.    

Ltac tt_exists_predecessor:=
  match goal with 
      [  H : ?x >= 1 |- _ ] =>

      assert (exists x', S x' = x) by (apply exists_predecessor; assumption)
  end.

Lemma while_step_count_decreases_weakened:
  forall Γ e o c m c_end m_end,
    〈 WHILE e DO c END, m 〉 ⇒+/(SL, Γ, o) 〈c_end, m_end 〉 ->
    〈 IFB e THEN c;; WHILE e DO c END ELSE SKIP FI, m 〉 ⇒+/(SL, Γ, o) 〈c_end, m_end 〉.
Proof.
  intros.
  apply from_bridge_step_to_bridge_step_num in H.
  destruct_exists_conj.
  tt_exists_predecessor.
  destruct_exists_conj.
  subst.
  apply while_step_count_decreases in H0.
  apply from_bridge_step_num_to_bridge_step with (n := x0).
  auto.
Qed.

Lemma if_step_count_decreases:
  forall n Γ e o c1 c2 m c_end m_end, 
    〈IFB e THEN c1 ELSE c2 FI, m 〉 ⇨+/(SL, Γ, o, S n) 〈c_end, m_end 〉 ->
    exists v, 
      eval e m v /\ ( v = 0 \/ v = 1) /\      
      ( v = 1 -> 〈 c1 , m 〉 ⇨+/(SL, Γ, o, n) 〈c_end, m_end 〉  )   /\
       ( v = 0 -> 〈 c2 , m 〉 ⇨+/(SL, Γ, o, n) 〈c_end, m_end 〉  ).
Proof.
          
          intros.
          bridge_num_cases (inversion H) Case.
          {
            impossible_sl_step.
          }
          Case "bridge_nh_num".
          {
            inv_nh_step; subst; auto ; [idtac | inv_event_step].
            inv_event_step; subst; auto.
            match goal with 
                | [ H : _ ⇒ _  |- _ ] => inversion H; [exists 1 | exists 0]
            end; subst; auto; repeat split; auto; intros; crush.
          }
Qed.


         
Lemma if_step_count_decreases_weakened :
           forall Γ e o c1 c2 m c_end m_end, 
            〈IFB e THEN c1 ELSE c2 FI, m 〉 ⇒+/(SL, Γ, o) 〈c_end, m_end 〉 ->
            exists v,
            eval e m v /\ ( v = 0 \/ v = 1) /\
            ( v = 1 -> 〈 c1 , m 〉 ⇒+/(SL, Γ, o) 〈c_end, m_end 〉  ) /\
            ( v = 0 -> 〈 c2 , m 〉 ⇒+/(SL, Γ, o) 〈c_end, m_end 〉  ).
Proof.
          
          intros.
          apply from_bridge_step_to_bridge_step_num in H.
          destruct_exists_conj.
          tt_exists_predecessor.
          destruct H1.
          subst.
          apply if_step_count_decreases in H0.
          destruct_exists_conj.
          exists x;
            repeat split; auto;
            intros;
            subst;
            specialize_gen;
            match goal 
            with | [ H : _  ⇨+/(SL, Γ, o, ?XX) _ |- _ ] 
                   => apply from_bridge_step_num_to_bridge_step with (n := XX); auto
            end.
Qed.





