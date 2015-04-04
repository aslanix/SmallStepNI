Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.


Set Implicit Arguments.

Require Import InductionPrinciple UtilTactics.

Require Import Identifier Environment Imperative BridgeSteps WellFormedness LowEq NIexp ObsLowEq.

Create HintDb Sec.

Hint Resolve eq_exp_dec :Sec.
Hint Resolve eq_nat_dec : Sec.
Hint Resolve eq_id_dec : Sec.
Hint Resolve eq_cmd_dec :Sec.
Hint Resolve eq_level_dec : Sec.
Hint Resolve eq_event_dec : Sec.
Hint Resolve eq_obs_dec : Sec.
Hint Resolve multi_refl : Sec.
Hint Resolve flowsto_sym : Sec.
Hint Resolve high_does_not_flow_to_low : Sec.
Hint Resolve config_is_stop_config : Sec.



Ltac tt_SSn_ne_1 :=
            try match goal with 
              | [ H: S (S ?n) = 1|- _]  =>
                assert (S (S n) <> 1) by omega;
                  contradiction
                end.        

Ltac clear_trivial:=
          match goal with 
            | [ H: ?X = ?X |- _ ] => clear H
          end.
 

Ltac tt_wt_cmd_is_not_stop_save_name c H_new :=
  match goal with 
      [H : { _, _ ⊢ c } |- _ ]
            
      =>
      assert (H_new := H);
        apply wt_programs_are_not_stop in H; auto
  end.
      



(* Note that this lemma is defined in terms of basic steps >> 2015-04-03 *)

Lemma high_pc_does_not_update_low_states:
  forall Γ c m c_end s,
    {Γ, High ⊢ c} ->
    〈 c, m 〉⇒ 〈 c_end, s 〉 ->
    wf_mem m Γ
    -> state_low_eq Γ m s.
Proof.
  intros Γ c m c_end s H_wt H H_wf.
  cmd_cases (dependent induction c) Case.
  Case "STOP".
  {        
    tt_wt_cmd_is_not_stop_save_name STOP H_wt'; false.
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




Lemma high_pc_does_not_update_low_states_event_step:
  forall Γ e c m c_end s,
    {Γ, High ⊢ c} ->
    event_step Γ e 〈 c, m 〉 〈 c_end, s 〉 ->
    wf_mem m Γ
    -> state_low_eq Γ m s.
Proof.
  intros Γ e c m c_end s H_wt H H_wf.
  dependent induction H; subst;
  try
    match goal with
      |[  H : 〈?C, ?M 〉 ⇒ 〈 ?C', ?S'〉 |- _ ] =>
       apply high_pc_does_not_update_low_states with (Γ := Γ) in H; auto
    end;
  inversion H_wt; subst.
  {
    specialize (IHevent_step H6); crush.
  }
  {
    specialize (IHevent_step STOP) .
    crush.
  }
  {
    specialize (IHevent_step STOP). crush.
  }

Qed.

Lemma high_pc_does_not_update_low_states_h:
  forall Γ  c m c_end s,
    {Γ, High ⊢ c} ->
    〈 c, m 〉 ⇒/(H, Γ) 〈 c_end, s 〉 ->
    wf_mem m Γ
    -> state_low_eq Γ m s.
Proof.
  intros.
  inversion H0; auto;           
  match goal with
    | [ H: event_step _ ?E 〈?C, ?M 〉 _ |- _ ]=>
      apply high_pc_does_not_update_low_states_event_step
            with (e:= E) (c := C) (m := M) (c_end := c_end); auto
  end.
Qed.  



Lemma no_assignment_events_in_high_contexts:
  forall Γ c,
    {Γ, High ⊢ c} ->
    forall x u m c' m',
      event_step Γ (AssignmentEvent Low x u) 〈 c, m 〉〈 c', m' 〉->
      False.
Proof.

  intros Γ c H_wt.
  cmd_has_type_cases(dependent induction H_wt) Case;
    intros y u m c' m' H';
    try
      match goal with
        | [ Case:="T_Assign" :_ |- _ ] =>
          inversion H'; subst;
          assert (ℓ' = High) by (destruct ℓ'; crush); subst;
          crush
        |  _  => solve [inversion H']
      end.
  Case "T_Seq".
  {
    inv_event_step_clear; subst.
    apply (IHH_wt1 y u m c1' m'); auto.


    inv_event_step; subst.
    apply (IHH_wt1 y u m STOP m'); auto.


    inversion H_wt1.
    inversion H6.
  }
 
Qed.

  
Lemma high_pc_does_not_update_low_states_sl_aux:
  forall Γ c,
    {Γ, High ⊢ c} ->
     forall o m c_end s,
    〈 c, m 〉 ⇒/(SL, Γ, o) 〈 c_end, s 〉 ->
    c_end = STOP.
Proof.
  intros Γ c H_wt.
  assert (H_wt' := H_wt).
  cmd_has_type_cases (dependent induction H_wt) Case;
    intros o m c' m' H'
    ; inversion H'; subst; auto
    ; solve
        [ inv_stop_config; auto
        | inv_event_step
        |  match goal with
             | [ H : context [AssignmentEvent ?L _ _ ] ,
                     _ : ?L ⊑ Low |- _ ] =>
               assert (L = Low) by (destruct L; crush); subst;
               apply no_assignment_events_in_high_contexts in H; auto
           end; contradiction
        ].
Qed.
  
Lemma high_pc_does_not_update_low_states_sl:
  forall Γ o c m c_end s,
    {Γ, High ⊢ c} ->
    〈 c, m 〉 ⇒/(SL, Γ, o) 〈 c_end, s 〉 ->
    wf_mem m Γ
    -> ~is_low_effect o /\ state_low_eq Γ m s  /\ c_end = STOP.
Proof.
  intros.
  split.
  {
    inversion H0;subst;
    try match goal with
      | [ |- ~is_low_effect Halt ] =>
        unfold not; intros; inv_low_effect

      | [ H : context [AssignmentEvent ?L _ _ ] ,
              _ : ?L ⊑ Low |- _ ] =>
        assert (L = Low) by (destruct L; crush); subst;
        apply no_assignment_events_in_high_contexts in H; auto
    end.
  }
  split.
  {
    inversion H0; subst; auto;
    match goal with
      | [ H: event_step _ ?E 〈?C, ?M 〉 _ |- _ ]=>
        apply high_pc_does_not_update_low_states_event_step
            with (e:= E) (c := C) (m := M) (c_end := c_end); auto
    end.
  }
  {
    eapply high_pc_does_not_update_low_states_sl_aux.
    apply H.
    apply H0.
  }    
Qed.

    
    


  
Lemma high_pc_does_not_update_low_state:
  forall n Γ c m c_end s o,
    {Γ, High ⊢ c} ->
    〈 c, m 〉⇨+/(SL, Γ, o, S n) 〈 c_end, s 〉->
    wf_mem m Γ 
    -> ~ is_low_effect o /\ state_low_eq Γ m s /\ c_end = STOP.
Proof.
  intro n.
  induction n.
  (* base case *)
  {
    intros.
    inv_bridge_num; auto; subst;
    try (match goal with |[ H : 0 >= 1 |- _ ] => inversion H end).
    apply high_pc_does_not_update_low_states_sl with (c:=c); auto.
  }
  (* inductive case *)
  {
    intros.
    inversion H0.
    destruct cfg'.
    subst.

    match goal
    with [ H: _ ⇒/(NH, Γ) _ |- _ ]=>
         apply nonstop_high_event_is_a_high_event_and_does_not_end_in_stop in H;
           
           destruct H as [XX YY];
           assert (XX' := XX);
           apply  high_pc_does_not_update_low_states_h in XX; auto
                                                                
    end.
    
    apply preservation_nh_event with (pc:=High) in XX'; auto.
    destruct_conj.
    specialize_gen.
    
    specialize (IHn Γ c0 st c_end s o).
    repeat specialize_gen.

    destruct_conj. (split; auto); (split; auto).

    eapply state_low_eq_trans.
    apply XX.
    apply H6.
  }
Qed.



Lemma only_wf_mems_are_loweq:
  forall Γ m s,
    state_low_eq Γ m s ->
    wf_mem m Γ.
Proof.
  intros.
  inversion H.
  auto.
Qed.

Definition NI_idx (n:nat): Prop :=
  forall Γ pc c, 
    { Γ, pc ⊢ c } ->    
    forall m s obs1 obs2 c2 d2 m2 s2,
      state_low_eq Γ m s ->
      〈c, m〉⇨+/(SL, Γ, obs1, n ) 〈c2, m2〉->
      〈c, s〉⇒+/(SL, Γ, obs2 ) 〈d2, s2〉->
      state_low_eq Γ m2 s2 /\ c2 = d2 /\
      (obs1 ≜ obs2)
      /\ ( is_low_effect obs1 ->
           exists cmd_low m1 s1, 
             obs1 = obs2 /\
             state_low_eq Γ m1 s1 /\ 
             〈c, m〉 ⇒*/(NH, Γ) 〈cmd_low, m1〉 /\
             〈cmd_low, m1〉⇒/(SL, Γ, obs1 ) 〈c2, m2〉 /\
             〈c, s〉 ⇒*/(NH, Γ) 〈cmd_low, s1〉 /\
             〈cmd_low, s1〉⇒/(SL, Γ, obs2 ) 〈c2, s2〉/\
             (n = 1 -> cmd_low = c /\ m1 = m /\ s1 = s)
         ).

Theorem ni_cmd_num: 
  forall n, NI_idx (S n).
Proof.

  
  apply strongind.
  
  
  (* Base case *)
  {
    unfold NI_idx. intros Γ pc c H; subst.
    cmd_has_type_cases (induction H) Case;
      intros m s o1 o2 c_end d_end m_end s_end; intros leq H_m H_s.
    
    Case "T_Skip".
    {
      tt_from_bridge_step_num_to_bridge_step.
      repeat 
        match goal 
        with 
          | [ H :  _ ⇒+/(SL, Γ, _ ) _ |- _ ] =>
            apply skip_bridges_no_mem_change with (Γ:=Γ) in H
        end; super_destruct_split.
      constructor.
      inv_low_effect.
    }
    Case "T_Assign".
    { 

      tt_from_bridge_step_num_to_bridge_step.            
      repeat
        match goal 
        with [ H : _  ⇒+/(SL, Γ, _) _ |- _ ] =>
             apply assign_bridges_to_stop_val_inversion in H; 
               super_destruct; subst
        end.
      split; subst.
      {        
        apply leq_updates with ℓ'; auto;
        apply ni_exp with Γ m s e; auto;
        apply T_Sub with ℓ; auto.
      }
      split;auto.
      {
        assert (o1 = o2) as OO.
        {
          compare  (Γ x)  (Some Low); super_destruct; (auto with Sec).
          {
            intros.
            repeat specialize_gen.
            
            env_is_det Γ; subst; remove_duplicate_hypothesis;
            match goal with
              | [  H_e :  {{Γ ⊢ e : ℓ}},
                          _   : eval e s ?X1,
                              _ : eval e m ?X2  |- _ ] =>
                assert (val_low_eq Low X1 X2) as LL      
                    by ( 
                        apply ni_exp with Γ s m e; auto;
                        apply T_Sub with ( ℓ' := Low ) in H_e ;
                      auto;          
                      apply state_low_eq_sym; auto
                      );
                  inversion LL; crush                
            end.
          }
          {
            intro.
            assert (ℓ' = High) by (destruct ℓ'; crush); subst.
            repeat specialize_gen.
            intros. subst. auto.
          }
        }
        split.
        {
          apply eq_obs_are_low_related; auto.
        }
        {
          intros.
          exists ( x ::= e) m s ; crush.
        }
      }


    }      

    Case "T_Seq".
    {


      
      tt_wt_cmd_is_not_stop_save_name c1 H_wt_c1;
      tt_wt_cmd_is_not_stop_save_name c2 H_wt_c2.

 
      
      inversion H_m; try tt_impossible_bridge_num_consntructor.
      

      match goal with 
        | [ H:  〈 _, m 〉 ⇒/(SL, _, _) _ |- _ ] 
          => 
          assert (Hm_saved := H);
            apply first_seq_comp_low_step in H; 
            destruct H as [d1_m]
                              
      end; super_destruct; subst.
      assert ( 〈c1, m 〉 ⇨+/(SL, Γ, o1, 1) 〈d1_m, m_end 〉)  as Hd1 
          by (constructor; auto).


      apply seq_decomp_low in H_s; subst; auto.

      super_destruct; subst.
      

      
      {
        
        (* case in both runs the low event is produced by c1 *)
        
        
        match goal with 
          | [ H : 〈c1, s 〉 ⇒+/(SL, Γ, o2) 〈?xx, s_end 〉 |- _] =>
            rename xx into d1_s;
            specialize 
              (IHcmd_has_type1 m s o1 o2 d1_m d1_s m_end s_end leq Hd1 H)          
        end; subst. 
        repeat 
          match 
            goal with [ H : context [_ /\ _ ] |- _ ] 
                      => destruct H 
          end; auto; subst.
        split; auto.
        repeat split; auto.
        compare d1_s STOP; auto with Sec; intros; subst;
        repeat specialize_gen; subst; auto with Sec; cleanup.
        
        
        intros; exists (c1;;c2) m s. split; auto with Sec . split; auto. 
        repeat split; auto with Sec.
        remove_duplicate_hypothesis.
        compare d1_s STOP; auto with Sec; intros; subst; cleanup;

        match goal with 
            | [ H : 〈c1, s 〉 ⇒/(SL, Γ, o2) 〈_, s_end 〉|- _ ] =>
                apply first_seq_comp_low_step'  with (cb := c2) in H;              
              auto; try (inv_low_effect; crush)
        end.

      }
      
      (* in the second run c1 is silently consumed; this should 
         by impossible *)
      
      
      (* Case when s-run steps to a nh-event; should be impossible *)
      {
        match goal with 
            | [ H : _ ⇓/(H, _) ?S |- _] =>
              apply from_converges_to_stop_event in H
        end; auto.
        
        match goal with
            | [ H: 〈c1, s 〉 ⇒+/(SL, Γ, Halt) 〈STOP, ?S 〉  |- _ ]
                =>
                specialize (IHcmd_has_type1 m s o1 Halt d1_m STOP m_end S leq Hd1 H)
                  
        end; subst.
        
        repeat 
          match 
            goal with [ H : context [_ /\ _ ] |- _ ] 
                      => destruct H 
          end; auto; subst.
        

        inv_low_effect.               
      }
    }

    Case "T_if".
    {
      inversion H_m;try tt_impossible_bridge_num_consntructor;

                auto;
      inv_sl_step; auto;
      inv_event_step; inv_stop_config; subst; crush.
    }

    Case "T_While".
    {
      inversion H_m; try tt_impossible_bridge_num_consntructor; auto;
      inv_sl_step; auto;
      inv_event_step; inv_stop_config; subst; crush.
    }

  }
  (* Inductive case *)
  {
    intros. 
    unfold NI_idx in *.
    intros Γ pc c H_wt. 

    cmd_has_type_cases (induction H_wt) Case; 
      intros m s o1 o2 c_end d_end m_end s_end  leq H_m H_s.
    
    Case "T_Skip".
    {
      (* case impossible *)
      inv_bridge_num;
      inv_nh_step;   
      inv_event_step;   
      inv_event_step.
    }
    Case "T_Assign".
    {
      (* case impossible *)
      inv_bridge_num;
      inv_nh_step;
      inv_event_step_clear;
      subst;
      inv_non_stop_config; crush.      
    }
    Case "T_Seq".
    {

      
      tt_wt_cmd_is_not_stop_save_name c1 H_wt_c1;
      tt_wt_cmd_is_not_stop_save_name c2 H_wt_c2.

      apply seq_decomp_low_num in H_m; auto.
      destruct H_m as [H_m_left | H_m_right].
      {
        destruct H_m_left as [ca_mid  H_m_left].
        destruct H_m_left as [H_m_left   H_m_left'].
        destruct H_m_left' as [H_m_left'   H_m_left''].
        
        
        apply seq_decomp_low in H_s; auto.
        destruct H_s as [ H_s_left | H_s_right].
        (* m_left , s_left *)
        {

          (* clean unnecessary hyps *)
          clear H IHH_wt2.
          destruct H_s_left as [ca_mid_s  H_s_left].
          destruct H_s_left as [H_s_left H_s_left'].
          destruct H_s_left' as [H_s_left' H_s_left''].
          specialize (IHH_wt1 m s o1 o2 ca_mid ca_mid_s m_end s_end leq H_m_left H_s_left).
          
          destruct_conj; subst.
          split; auto; repeat split; auto.
          compare ca_mid_s STOP; auto with Sec; intros; subst;
          (repeat specialize_gen); subst; auto.
          intros; subst; auto.
          repeat specialize_gen.
          
          repeat match goal with 
                   | [ H: exists _, _ |- _] => destruct H
                   | [ H : _/\ _ |- _] => destruct H
          end; subst.
          
          match goal with 
              | [H:  〈c1, m 〉 ⇒*/(NH, Γ) 〈?C, ?M 〉,
                 H':  〈c1, s 〉 ⇒*/(NH, Γ) 〈?C, ?S 〉|- _
                 ] =>
                rename C into c1_last;
                  rename M into M_last;
                  rename S into S_last
          end.
         
          compare ca_mid_s STOP; auto with Sec;
            subst; intros; 
            (repeat specialize_gen); 
            
            exists (c1_last;;c2) M_last S_last; subst; cleanup;
            repeat (split; auto); 
            try ((repeat specialize_gen); destruct_conj;  subst; auto);
              match goal with 
                   | [ |- _ ⇒*/(NH, Γ) _ ] =>            
                     apply seq_com_aux_nonstopmany; auto

                   | [ H: 〈c1_last, ?M 〉 ⇒/(SL, Γ, o2) 〈_, _ 〉
                      |- 〈 _, ?M 〉  ⇒/(SL, Γ, o2) _ ] 
                    => 
                    apply first_seq_comp_low_step' with (cb := c2) in H; 
                      auto;
                      destruct_exists; 
                      destruct_conj; 
                      (repeat specialize_gen); 
                      subst; 
                      auto;
                      inv_low_effect
                 end;
             subst; crush.
        }
        
        (* m_left , s_right *)
        {
          destruct_exists; destruct_conj;
          match goal with 
              | [ H : _ ⇓/(H, _) ?M |- _ ] =>
                rename M into s1_end;
                  apply from_converges_to_stop_event in H;
                  rename H into H_s_right
          end; auto;

          specialize (IHH_wt1 m s o1 Halt ca_mid STOP m_end s1_end
                              leq H_m_left H_s_right);          
            repeat destruct_conj; subst.
          match goal with 
            | [ H : _ ≜  Halt |- _ ] => 
              apply obs_low_eq_aux in H;auto; subst
          end;
          inv_low_effect.

        }
        
      }
      (* m_right *)
      {
        Ltac tt_converges_to_halt_bridge:=
          match goal with 
            | [ H : _ ⇓/(H, _) ?M |- _ ] =>
                apply from_converges_to_stop_event in H; auto
          end.



        
        repeat destruct_exists; destruct_conj.

        (* save the outer IH because we may need to use it twice. *)
        assert (IH_outer := H).
        match goal with            
          | [ H : 〈c1, m 〉 ⇨+/(SL, Γ, Halt, ?K) 〈STOP, ?M1_END 〉|- _ ]
              =>
              assert (K - 1 <= n) as K1 by omega;
                rename K into k;
                rename M1_END into m1_end
        end.

        specialize (H (k-1) K1 Γ pc c1 H_wt_c1 m s).
        assert (S (k - 1 ) = k) as K2 by omega;
        rewrite -> K2 in *;
        clear K1 K2.
        
        apply seq_decomp_low in H_s; auto.
        destruct H_s as [ H_s_left | H_s_right];
          repeat destruct_exists; destruct_conj.
        

        (* m_right, s_left -- should be impossible *)
        {
          clear IH_outer. (* don't need it here, so we just clean things up *)
          match goal with 
            | [ H_m: 〈c1, m 〉 ⇨+/(SL, Γ, Halt, k) 〈STOP, m1_end 〉, 
                H_s: 〈c1, s 〉 ⇒+/(SL, Γ, o2) 〈?c1_end, s_end 〉 |- _ ]
                  =>
                  specialize (H Halt o2 STOP c1_end m1_end s_end leq H_m H_s)
          end.
          destruct_conj; subst.

          match goal with 
            | [ H : Halt ≜  ?O |- _ ] => 
              (apply obs_low_eq_sym in H; auto);
                apply obs_low_eq_aux in H; auto; subst;
                inv_low_effect
          end.
        }
        (* m_right, s_right -- should be possible; gotta use outer IH *)
        {
          tt_converges_to_halt_bridge.

          match goal with 
            | [ H_m: 〈c1, m 〉 ⇨+/(SL, Γ, Halt, k) 〈STOP, m1_end 〉, 
                H_s: 〈c1, s 〉 ⇒+/(SL, Γ, ?O) 〈?c1_end, ?s_end 〉 |- _ ]
                  =>
                  specialize (H Halt O STOP c1_end m1_end s_end leq H_m H_s)
          end.
          destruct_conj; subst.

          (*
          repeat match goal with 
              | [ H: context [c1] |- _ ] => clear H
              | [ H : context [k] |- _ ] => clear H
              | [ H : ?X = ?X |- _ ] => clear H
          end.
          clear leq IHH_wt2.
          *)

          (* renaming for convenience *)
          match goal with 
              |   [H1 : 〈c2, m1_end 〉 ⇨+/(SL, Γ, o1, ?X) 〈c_end, m_end 〉,
                   H2 : 〈c2, ?S 〉 ⇒+/(SL, Γ, o2) 〈d_end, s_end 〉,
                   H3 : state_low_eq Γ m1_end _
                  |- _] 
                    => rename X into k';rename S into s1_end; rename H1 into H_m;
                       rename H2 into H_s; rename H3 into H_leq'
          end.
          assert (k' - 1 <=n ) as K1' by omega.
          
          assert ( S (k' - 1 ) = k') as K2' by 
                (assert (k' >= 1) by (inversion H_m; auto); omega ).
          
          specialize (IH_outer (k'-1) K1' Γ pc c2 H_wt_c2 m1_end s1_end).
          rewrite -> K2' in *.
          specialize (IH_outer o1 o2 c_end d_end m_end s_end H_leq' H_m H_s).
          clear K1' K2'.
          destruct_conj; subst.
          split; auto; repeat split; auto.
          intro; specialize_gen.
          repeat destruct_exists; destruct_conj.

          (* show existence *)
          match goal with
              | [ H:  〈c2, m1_end 〉 ⇒*/(NH, Γ) 〈?CC, ?M' 〉,
                 H':  〈c2, s1_end 〉 ⇒*/(NH, Γ) 〈?CC, ?S' 〉 |- _ ]
                  =>
                  rename CC into cmd_low;
                    rename M' into m_last;
                    rename S' into s_last
          end.

          exists cmd_low m_last s_last.
          repeat (split; auto; subst);
          try match goal with 
              | [ H: S (S n) = 1|- _]  =>
                assert (S (S n) <> 1) by omega;
                  contradiction
              end.
          {
            clear IHH_wt1 IHH_wt2 H_m H_s.
            apply from_bridge_step_num_to_bridge_step in H0.
            apply seq_comp_nh_tail' with (m' :=  m1_end); auto.
          }
          
          {
            apply seq_comp_nh_tail' with (m' :=  s1_end); auto.
          }
          
        }
        
      }
      
      
    }
    
    Focus 2.
    Case "T_While".
    {
      (* clear unneccessary hypotheses *)
      clear IHH_wt.
      apply while_step_count_decreases in H_m; 
        apply while_step_count_decreases_weakened in H_s; 
        destruct_exists_conj.
      assert ( { Γ, pc ⊢ IFB e THEN c;; WHILE e DO c END ELSE SKIP FI } )  as H_wt'.
      {
        apply T_If with (ℓ := ℓ) (pc' := pc'); auto.
        apply T_Seq; auto.
        apply T_While with (ℓ := ℓ) (pc' := pc'); auto.
        apply flowsto_sym.
        apply T_Skip.
      }
      
      assert (n <= n) as H_n_leq_n by omega.
      specialize (H n H_n_leq_n Γ pc (IFB e THEN c;; WHILE e DO c END ELSE SKIP FI)
                    H_wt' m s o1 o2 c_end d_end m_end s_end leq H_m H_s).
      destruct_conj; repeat (split; auto).
      intros.
      specialize_gen.
      match goal with
              | [ H : exists _, _ |-_ ] => 
                destruct H as [cmd_low];
                  repeat destruct_exists; destruct_conj; subst
      end.
      match goal with 
        |  [_ : 〈_, m 〉 ⇒*/(NH, Γ) 〈?cmd_low, ?m_last 〉,
                _ : 〈_, s 〉 ⇒*/(NH, Γ) 〈?cmd_low, ?s_last 〉 |- _ ]
           =>           (exists cmd_low m_last s_last)
      end.     
      repeat (split; auto); try tt_SSn_ne_1;

      match goal with 
            | [ H :  〈?C, ?M 〉 ⇒*/(NH, Γ) 〈_, _ 〉 |-  context [ 〈 ?CMD, ?M〉] ] 
              =>
              assert ( 〈 CMD, M 〉⇒/(NH, Γ)〈C, M〉)
                by (
                    apply nonstophigh_or_empty_event_empty;
                    repeat constructor;
                    try (apply wt_programs_are_not_stop with Γ pc; auto)
                  );
                apply multi_step with 〈 C, M 〉; auto
      end.      
    }
    Unfocus.
    
    
    Case "T_if".
    {

      
      (* destruct pc' .
         - if it is low then proceed by either outer induction hypothesis. 
           cannot use the inner one because the number of low steps 
           is going to be one fewer.

         - if it is high then we need a separate lemma about memory 
           equivalence in high contexts.

       *)
      
      (* we clear the inner IH because we cannot use them. *)
      clear IHH_wt1 IHH_wt2.
      level_cases (destruct pc') SCase.
      SCase "Low".
      {
        repeat match goal with 
          | [ H : pc ⊑ Low |- _ ] =>
            assert (pc = Low) by (inversion H; auto);
              subst; auto
          | [ H : ℓ ⊑ Low |- _ ] =>
            assert (ℓ = Low) by (inversion H; auto);
              subst; auto
          | [ H : Low ⊑ Low |- _ ] => clear H
        end.
        


        apply if_step_count_decreases in H_m;
          destruct_exists_conj.

        apply if_step_count_decreases_weakened  in H_s;
          destruct_exists_conj.
        
        
        (* next we want to show that evaluations of e in 
           both m and s yield the same value 
         *)




        match goal 
        with | [ _ : eval e m ?U, _ : eval e s ?V|- _ ] => 
               rename U into u; rename V into v
        end;
              
        repeat match goal with | [ H :  _ \/ _ |- _ ] => destruct H end;
        assert (u = v) by
            (
              assert (val_low_eq Low u v) as LE by        
                  ( apply ni_exp with ( Γ := Γ) ( m1 := m) (m2 := s) (e:=e);
                    auto);
              inversion LE; auto
            ); subst;
        repeat match goal with 
            | [ _ : 1 = 0 |- _ ] => crush
            | [ _ : 0 = 1 |- _ ] => crush
            | [ H : 0 = 1 -> _ |- _ ] => clear H
            | [ H : 1 = 0 -> _ |- _ ] => clear H
            | [ H : ?X = ?X -> _ , H' : ?X = ?X |- _ ] => specialize (H H')
            (* further cleanup *)


            | [ H:  {{Γ ⊢ e : Low}} |- _ ] => clear H
        end; clear_trivial; remove_duplicate_hypothesis;

        (* both runs take the same branch *)
        

        (* TODO : 2015-04-03; this is ugly  only because
           I don't know how to return tuples in ltac.  *)
        
        let c_i:=
            match goal with 
                | [ _ : eval e m 0 |- _ ] => c2
                | [ _ : eval e m 1 |- _ ] => c1
            end
        in
        let H_wt_i:=
            match goal with 
              | [ _ : eval e m 0 |- _ ] => H_wt2
              | [ _ : eval e m 1 |- _ ] => H_wt1
            end
        in
        
          match goal with 
              | [ H : _ ⇨+/(SL, Γ, _, S n) _  ,
                  H': _ ⇒+/(SL, Γ, _) _ |- _  ] =>
                rename H into H_num;
                rename H' into H_bridge
          end;
            
          (* this should be only about applying the induction hypothesis *)
          assert (n <= n) as H_n_leq_n by omega;
          specialize (H n H_n_leq_n Γ Low c_i H_wt_i m s 
                        o1 o2 c_end d_end m_end s_end
                        leq H_num H_bridge
                     );

          destruct_conj; repeat (split; auto);
          intros; specialize_gen;
          match goal with
              | [ H : exists _, _ |-_ ] => 
                destruct H as [cmd_low];
                  repeat destruct_exists; destruct_conj; subst
          end;

          match goal with 
           |  [_ : 〈_, m 〉 ⇒*/(NH, Γ) 〈?cmd_low, ?m_last 〉,
               _ : 〈_, s 〉 ⇒*/(NH, Γ) 〈?cmd_low, ?s_last 〉 |- _ ]
              =>           exists cmd_low m_last s_last
          end;          



          repeat (split; auto); try tt_SSn_ne_1;
          
          match goal with 
            | [ H :  〈?C, ?M 〉 ⇒*/(NH, Γ) 〈_, _ 〉 |-  context [?M] ] 
                =>
                assert (〈IFB e THEN c1 ELSE c2 FI, M 〉⇒/(NH, Γ)〈C, M〉) by
                    (
                      apply nonstophigh_or_empty_event_empty;
                      apply event_empty_branch;
                      try (apply wt_programs_are_not_stop with Γ Low; auto);
                      constructor; auto
                    );
                  apply multi_step with 〈C, M 〉; auto
          end.
      }

      SCase "High".
      {
        assert ({Γ, High ⊢ IFB e THEN c1 ELSE c2 FI}).
        {
          apply T_If with (ℓ:= ℓ) (pc' := High); auto with Sec.
        }
        assert (wf_mem m Γ) by (inversion leq; crush).
        assert (wf_mem s Γ) by (inversion leq; crush).
        
        apply high_pc_does_not_update_low_state in H_m; auto.
        apply from_bridge_step_to_bridge_step_num in H_s; auto; destruct_exists; destruct_conj.


        

        match goal with 
          | [ H: _  ⇨+/(SL, Γ, o2, ?Z) _ |- _ ] =>
            assert (exists x', S x' = Z) as Sxx by
                  (
                    induction Z;
                    assert ( 0 >=1 -> False) by omega; crush;
                    exists Z;crush
                  );
              destruct Sxx; subst;
          
              apply high_pc_does_not_update_low_state in H; auto
        end.
        destruct_conj. 
        subst.
        split; auto.
        {
          match goal with
              [ H : state_low_eq _ m m_end |- _ ] =>
              rename H into H_working
          end.
          apply state_low_eq_sym in H_working; auto.
          eapply state_low_eq_trans.
          apply H_working.
          eapply state_low_eq_trans.
          apply leq.
          auto.
        }
        repeat (split; auto).
        {
          apply non_low_effects_are_related;auto.
        }
        {
          intros.
          contradiction.
        }
      }
      
    }
  }
Qed.
