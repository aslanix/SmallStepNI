(* Top-level noninterference 
   Author: Aslan Askarov
   Created: 2016-07-28
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
Require Import BridgeProperties.
Require Import HighPCSteps.
Require Import Adequacy.
Require Import NIBridge.


Definition TINI_idx (n: nat): Prop :=  
  forall Γ c m m_end s s_end pc k,
    〈c, m 〉 ⇒/+ n +/ 〈STOP, m_end 〉 ->
    -{ Γ, pc ⊢ c }- ->
    state_low_eq Γ m s ->
    〈c, s 〉 ⇒/+ k +/ 〈STOP, s_end 〉 ->
    state_low_eq Γ m_end s_end.

Lemma tini_idx: forall n, TINI_idx (n).

Proof.
  apply strongind.
  (* base case *)
  { unfolds.
    intros.
    inverts H.
    inverts H0.
  }
  (* inductive case *)
  {
    
    unfold TINI_idx.
    intros n IH Γ c m m_end s s_end pc k H_m H_wt H_leq H_s. 

    forwards* H_bridge_m: bridge_adequacy H_m.
    {
      inverts~ H_leq.
    }

    forwards* H_bridge_s: bridge_adequacy H_s.
    {
      inverts~ H_leq.
    }

    (* TODO: 2016-07-29 : complete the case by applying ni_bridge_num *) 
    
    destruct H_bridge_m as [? | ?H_bridge_m];
      subst ;
      try  (solve [inverts H_wt]).
    destruct H_bridge_s as [? | ?H_bridge_s];
      subst;
      try  (solve [inverts H_wt]).
    

    
    lets  (?ev1 & ?n1 &  ?cfg1 & ?k1 & ?H_bridge_IH1 & H_multi_IH1 & ?): H_bridge_m.
    lets  (?ev2 & ?n2 &  ?cfg2 & ?k2 & ?H_bridge_IH2 & H_multi_IH2 & ?): H_bridge_s.

    (* TODO apply the same to H_bridge_m *)
    (* TODO: earlier : add stop non-typability into hints *)
    
    clear H_bridge_m H_bridge_s.

    destruct cfg1 as [c1 m'].
    destruct cfg2 as [c2 s'].
      
      
    assert (k1 <= n) as H_k1 by omega.

    replace n1 with (S (n1 - 1)) in * by (inverts* H_bridge_IH1; omega ).
    replace n2 with (S (n2 - 1)) in * by (inverts* H_bridge_IH2; omega ).

    lets NI_bridge: ni_bridge_num (n1 -1); unfold NI_idx in NI_bridge.


        
    specializes~ NI_bridge (>>Γ c m s ev1  c1  m' s' (n2 - 1) ___).


    forwards* (? & ?H_wt'): preservation_bridge.
    {
      inversion H_leq; auto.
    }
    lets (H_leq' & cmd_eq & ? ) : NI_bridge.
    clear NI_bridge.
    subst.
    
    compare c2 STOP; intros; subst.
    - assert (m' = m_end) by eauto.
      assert (s' = s_end) by eauto.
      subst*.
    - specializes* H_wt'.
  }
Qed.

    
(* Standard termination-insensitive noninterference *)

Theorem TINI:
  forall Γ c m s m_end s_end pc,
    -{ Γ, pc ⊢ c }- ->
    state_low_eq Γ m s ->
    〈c, m 〉 ⇒* 〈STOP, m_end 〉 ->
    〈c, s 〉 ⇒* 〈STOP, s_end 〉 ->
    state_low_eq Γ m_end s_end.
Proof.    
  intros Γ c m s m_end s_end pc H_wt H_leq H_m H_s.
  forwards (?n & ?H'_m) : from_multi_to_multi_idx H_m; clear H_m.
  forwards (?k & ?H'_s) : from_multi_to_multi_idx H_s; clear H_s.

  applys tini_idx H'_m H_wt H_leq H'_s.
Qed.

     