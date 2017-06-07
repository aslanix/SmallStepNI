

Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.
Require Import Omega.



Set Implicit Arguments.

Require Import Identifier Environment Imperative Types Augmented Bridge.
Require Import WellFormedness LowEq NIexp.
Require Import InductionPrinciple.
Require Import UtilTactics.
Require Import BridgeTactics.
Require Import BridgeProperties.
Require Import HighPCSteps.



Definition NI_idx (n: nat): Prop :=
  forall Γ pc c,
    -{ Γ, pc ⊢ c }- ->
    forall m s ev1 ev2 c2 d2 m2 s2 n',
      state_low_eq Γ m s -> 
      〈c, m〉 ↷ ( Γ, ev1, n ) 〈c2, m2〉->
      〈c, s〉 ↷ ( Γ, ev2, n') 〈d2, s2〉->
      state_low_eq Γ m2 s2 /\ c2 = d2 /\
      (low_event Γ Low ev1 <-> low_event Γ Low ev2)
      /\  (low_event Γ Low ev1 -> ev1 = ev2).




Theorem ni_bridge_num:
  forall n, NI_idx (n).
Proof.
  apply strongind.
  (* Base case *)
  {
    unfold NI_idx.
    intros Γ pc c  H; subst.
    cmd_has_type_cases (induction H) Case;
      intros m s ev1 ev2 c_end d_end m_end s_end n' leq H_m H'_s.

    Case "T_Skip".
    {
      forwards H_a: skip_bridge_properties H_m.
      forwards H_b: skip_bridge_properties H'_s.
      destructs H_a.
      destructs H_b.
      subst.
      splits *.
    }
    Case "T_Assign".
    {
      (* clean up; gathering what we know about assignments *)

      repeat
        (match goal with
             | [ H: context [bridge_step_num] |- _ ] =>
               (apply assign_bridge_properties in H; repeat (super_destruct; subst))
             |  [ H: Γ x = Some ?U, H' : Γ x = Some ?V |- _ ] =>
                (assert (U = V) by congruence; subst; clear H)
         end).

      (* use NI for expressions *)
      forwards* low_eq: ni_exp.
      match goal with
          [ _ : Γ x = Some ?ℓ' |- _ ] =>
          (forwards* LE : low_eq_flowsto __ ℓ' low_eq;
           clear low_eq;
           rename ℓ' into ℓ_x)
      end.
      forwards* st_eq: leq_updates.

      splits *.
      (* the main goal is in the hypothesis by now *)
      
      (* these take care of the last two technical goals *)
      - 
        clear st_eq;
        assert (Low ⊑ Low) by auto;
        assert ( ~ High ⊑ Low) by  (unfold not; intros H''; inversion H'').
        destruct ℓ_x; subst.
        + inverts~ LE.
          splits;
          intros;
          repeat specialize_gen; subst;
          eauto.
        + inverts~ LE.
          splits;
          intros;
            repeat specialize_gen; subst;
            unfolds high_event;
            contradiction.
      - intros.
        destruct ℓ_x; subst;
        inverts~ LE;
        assert (Low ⊑ Low) by auto;
        assert ( ~ High ⊑ Low) by  (unfold not; intros H''; inversion H'');
        repeat specialize_gen; subst; eauto;
        unfolds high_event; contradiction.

    }
    Case "T_Seq".
    {
      (* auxiliary Ltac to apply the IH *)
      Ltac apply_seq_comp_base_IH c1 m s IH leq:=
          match goal with
            | [ H : 〈c1, m 〉 ⇨+/(SL, ?Γ , ?ev1, _) 〈?C1, ?M 〉,
                    H_alt : 〈c1, s 〉 ⇨+/(SL, _ , ?ev2, ?n') 〈?C2, ?S 〉 |- _ ]
              => specialize (IH m s ev1 ev2 C1 C2 M S n' leq H H_alt)
          end.


      apply seq_comp_bridge_property in H_m.
      apply seq_comp_bridge_property in H'_s.

      super_destruct; try (solve [omega]).
      (* the above destruct gives us four cases; two are discharged by
         omega; of the remaining two only one is possible *)

      - (* this is the only possible case, we get it from the IH *)

        apply_seq_comp_base_IH c1 m s IHcmd_has_type1 leq.
        super_destruct;
          (splits ~) ;
          compare x STOP;intros;
          repeat (specialize_gens).

      - (* impossible after applying the IH because ev1 is low?  *)
        apply_seq_comp_base_IH c1 m s IHcmd_has_type1 leq.
        super_destruct.
        specialize_gens.
        
        invert_low_event.
        exfalso.
        eauto.
      }


    (* neither if or while are possible in base case
       we use the following auxiliary ltac to discharge the goals *)

    Ltac discharge_if_while_base H :=
      (inverts H);
      repeat match goal with
        | [ H : context [low_event_step] |- _ ] => invert_low_steps
        | [ H : context [high_event_step] |- _] => (invert_high_steps; subst)
        | [ H: context [is_stop] |-  _ ] => (do 2 unfolds in H; inverts * H)
        | [ H : 〈 _, _  〉 = 〈STOP, _ 〉 |- _] => (inversion H ; contradiction)
        | [ H : 0 >= 1 |- _ ] => omega
      end.

    Case "T_if".
    {
      (* impossible *)
      discharge_if_while_base H_m; crush.
    }
    Case "T_While".
    {
      (* impossible *)
      discharge_if_while_base H_m; crush.
    }
  }
  (* inductive case *)
  {
    intros.
    unfold NI_idx in *.
    intros Γ pc c H_wt.
    (* we proceed by induction on the typing derivation *)
    cmd_has_type_cases (induction H_wt) Case;
      intros m s ev1 ev2 c_end d_end m_end s_end n' leq H_m H_s.
    Case "T_Skip".
    {
      (* impossible *)
      inversion H_m.
      invert_high_steps.
      intros.
      stop_contradiction_alt.
    }
    Case "T_Assign".
    {
      (* impossible *)
      inversion H_m.
      invert_high_steps.
      stop_contradiction_alt.
    }
    Case "T_Seq".
    {

      apply seq_comp_bridge_property in H_m.
      apply seq_comp_bridge_property in H_s.

      super_destruct.
      (* we have four cases based on the side of the chosen existential after destruct:
        LL, RL, LR, RR
        - LL is proven via inner HH;
        - RR is proven via outer HH;
        - RL and LR are impossible
       *)
      {
        (* LL *)
        apply_seq_comp_base_IH c1  m s IHH_wt1 leq.
        super_destruct;
          repeat (split~).
        compare x STOP; intros;
        repeat (specialize_gens).
        (* TODO: this boilerplate is similar to the LL case in the base case of the proof; consider
           generalizing; 2016-07-25; aa *)
      }

Ltac apply_seq_comp_ind_IH H c1 H_leq:=
   do 2 match goal with

          | [ H: context [?X < S ?n] |- _ ]=>
            assert (X <= n) by omega; clear H
          | [ H_m : 〈c1, ?m 〉 ⇨+/(SL, ?Γ , ?ev1, ?X) 〈?C1, ?M 〉,
                    H_s: 〈c1, ?s 〉 ⇨+/(SL, _ , ?ev2, ?n') 〈?C2, ?S 〉,
                         H_wt1 : -{ ?Γ, ?pc ⊢ c1 }-,
                         XX : context [ ?X <= _ ] |- _  ]
            =>
            specialize (H X XX Γ pc c1 H_wt1 m s ev1 ev2  C1 C2 M S n' H_leq H_m H_s)
        end.


      {
        (* RL *)
        (* impossible - show via applying the outer IH *)
        apply_seq_comp_ind_IH H c1 leq.
        super_destruct.
        match goal with [ H: context [ _ <-> _ ] |- _ ] => destruct H end.
        specialize_gen.
        invert_low_event.
        exfalso.
        eauto.
      }
      {
        (* LR *)
        (* impossible - show via applying the inner IH *)
        apply_seq_comp_base_IH c1 m s IHH_wt1 leq.
        super_destruct.
        exfalso.

        match goal with [ H: low_event _ _ _ <-> low_event _ _ _ |- _ ] => destruct H end.
        
        
        match goal with [H  : low_event _ _ ev1 -> low_event _ _ _,
                              H' : low_event _ _ ev1 |- _ ] => apply H in H'; inversion H'  end.
        eauto.
      }
      {
        clear IHH_wt1 IHH_wt2.
        (* RR *)
        (* save the outer hypothesis, because it is used twice *)
        assert (IH_outer := H).
        apply_seq_comp_ind_IH H c1 leq.
        destruct H.
        
        (* applying the induction hypothesis again, this time to c2 *)

        (* transform the indices so they match the patterns *)


        match goal with
          | [ H : context [ S n - ?X - 1] |- _ ] =>
            (assert (n - X <= n) by omega;
             replace (S n - X - 1) with ((n-X))  in * by omega
            )        
        end.




        (* apply the IH *)

        match goal with

          | [ H_m : 〈c2, ?m 〉 ⇨+/(SL, ?Γ , ev1, ?X) 〈?C1, ?M 〉,
                    H_s: 〈c2, ?s 〉 ⇨+/(SL, _ , ev2, ?n') 〈?C2, ?S 〉,
                         H_wt : -{ ?Γ, ?pc ⊢ c2 }- ,
                         XX : context [ ?X <= _ ] |- _  ]
            =>specialize (IH_outer X XX Γ pc c2 H_wt m s ev1 ev2 C1 C2 M S n' H H_m H_s) 
        end.
        eauto.

        (* TODO: 2016-07-26; the above may be too boilerplate;
           maybe clean up the code for IH application *)
      }
    }

    Case "T_if".
    {
      clear IHH_wt1 IHH_wt2;

      apply if_bridge_properties in H_m;
      apply if_bridge_properties in H_s.

      level_cases (destruct pc') SCase.

      - (* pc' = Low *)
        (* let's destruct and show that both branches evaluate to the same *)
        (* establish ℓ-equivalence of the guard *)

        assert (forall v1 v2,
                  eval e m v1 ->
                  eval  e s v2 ->
                  v1 = v2) as ?g_leq
            by ( intros;
                 assert (val_low_eq ℓ v1 v2) as X by applys* ni_exp;
                 inverts~ X;
                 impossible_flows
               ).

        super_destruct;
          (* 4 sub-goals after destruct; we appeal to low-equivalence of the guard
             to discharge the goals where both branches take separate branches *)
          specializes* g_leq; subst; try omega;
          (* 2 sub-goals remaining that correspond to both runs
             taking the same run; we handle both cases similarly by
             applying the induction hypothesis *)


        match goal with
            |  [ H' : 〈?c_i, s 〉 ⇨+/(SL, _ , ev2, ?X) _   |- _ ]
               =>   forwards* : H (S n - 1) c_i; omega
        end.
        
      - (* pc' = High *)
        clear H. (* no need for the IH *)
        subst.

        (* rather than dealing with four subcases of which branch is
          taken we extract the useful information about high ifs,
          namely that they take the bridge steps and are high
          themselves, and the rest of the case deals with these
          'abstract' programs c_i, c_j, where c_i that is taken from
          the m-run, and c_j that is taken from the s-run *)

        replace (S n - 1) with n in * by omega.

        assert (exists c_i, 〈c_i, m 〉 ⇨+/(SL, Γ, ev1, n) 〈c_end, m_end 〉
                            /\ ( c_i = c1 \/ c_i = c2  ) /\ -{ Γ, High ⊢ c_i }-) as H_i
            by (super_destruct;
                solve [exists c1; splits~ |  exists c2; split~ ]).
        
        assert (exists c_j ,〈c_j, s 〉 ⇨+/(SL, Γ, ev2,  (n' - 1) ) 〈d_end, s_end 〉
                            /\ ( c_j = c1 \/ c_j = c2  ) /\ -{ Γ, High ⊢ c_j }- ) as H_j
            by ( 
                super_destruct;
(*                match goal with  | [ H:〈_, s 〉 ⇨+/(SL, Γ, ev2, n') 〈d_end, s_end 〉|- _ ] =>
                                   replace n' with (S (n' - 1)) in H by omega
                end. *)
                solve[ exists c1; splits~ | exists c2; splits~]
              ).

        clear H_m H_s. (* we don't need these anymore *)
        destruct H_i as [c_i].
        destruct H_j as [c_j].

        super_destruct.

        assert (state_low_eq Γ m m_end /\ c_end = STOP /\ high_event Γ Low ev1)
          by (applys* high_pc_bridge c_i m ev1; inverts~ leq).

        assert (state_low_eq Γ s s_end /\ d_end = STOP /\ high_event Γ Low ev2)
          by (applys* high_pc_bridge c_j s ev2; inverts~ leq).

        super_destruct; subst.
        splits~.
        + apply state_low_eq_trans_square with m s; assumption.
        + split; intros; contradiction.
        + contradiction.
    }

    Case "T_While".
    {
      clear IHH_wt. (* clear unnecessary hyps *)

      apply while_bridge_properties in H_m.
      apply while_bridge_properties in H_s.
      super_destruct.
      
      replace (S n - 1) with n in * by omega.


      assert ( -{ Γ, pc ⊢ IFB e THEN c;; WHILE e DO c END ELSE SKIP FI }- ).
      {
        apply  T_If with ℓ pc'; auto.
        applys* T_Seq.
        apply T_While with ℓ pc'; auto.
        apply* T_Skip.
      }

      applys* H (IFB e THEN c;; WHILE e DO c END ELSE SKIP FI).
    } (* unfocus T_While *)
  } (* unfocus induction case *)
Qed.
