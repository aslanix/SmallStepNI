Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Require Import Identifier Environment Imperative WellFormedness UtilTactics Types.



(* Low-equivalences  *)


(* Value low-equivalence *)

Inductive val_low_eq : level -> nat -> nat -> Prop :=
  | VLEqH : forall u v, val_low_eq High u v
  | VLEqL : forall u v, 
        u = v ->
        val_low_eq Low u v.

Lemma low_eq_flowsto : forall ℓ ℓ' u v,
                         ℓ  ⊑ ℓ' ->
                         val_low_eq ℓ u v ->
                         val_low_eq ℓ' u v.
Proof.
  intros; inversion H; crush; constructor.
Qed.
  

Lemma val_low_eq_sym: 
   forall ℓ u v, 
     val_low_eq ℓ u v ->
     val_low_eq ℓ v u.
Proof.
   intros.
   inversion H; crush.
   apply VLEqH.
Qed.
 
Lemma val_low_eq_sym_trans:
  forall ℓ u v w, 
    val_low_eq ℓ u v ->
    val_low_eq ℓ v w ->
    val_low_eq ℓ u w.
Proof.
  intros.
  destruct ℓ.
  {
    inversion H;   
    inversion H0;
    crush.
  }
  {
    constructor.
  }
Qed.  

Lemma val_low_eq_refl:
  forall ℓ u,
    val_low_eq ℓ u u.
Proof.
  destruct ℓ; constructor ;crush.
Qed.





(* Variable low-equivalence *)

Inductive var_low_eq : typenv -> state -> state -> id -> Prop :=
|  var_low_eq_: forall  Γ ℓ u v m1 m2 x, 
      Γ x =  Some ℓ ->
      m1 x = Some u ->
      m2 x = Some v ->
      val_low_eq ℓ u v ->
      var_low_eq Γ m1 m2 x.



Lemma var_low_eq_wf_refl:
  forall Γ m x ℓ,
    wf_mem m Γ ->
    Γ x = Some ℓ ->
    var_low_eq Γ m m x.
Proof.
  intros.
  unfold wf_mem in H.
  destruct_conj.
  repeat specialize_gen.
  destruct H1.
  apply var_low_eq_ with (ℓ := ℓ)  (u := x0) (v := x0); auto.
  apply val_low_eq_refl.
Qed.



Lemma var_low_eq_sym:
  forall Γ m s x, 
    var_low_eq Γ m s x ->
    var_low_eq Γ s m x.
Proof.
  intros.
  inversion H;
    crush.
  
  apply var_low_eq_ with (ℓ := ℓ) (u := v) (v := u); auto.
  apply val_low_eq_sym; auto.

Qed.


Lemma var_low_eq_wf_trans:
  forall Γ m x ℓ,
    wf_mem m Γ ->
    Γ x = Some ℓ ->
    var_low_eq Γ m m x.
Proof.
  intros.
  unfold wf_mem in *.
  destruct H.
  specialize (H1 x ℓ H0).
  destruct H1 as [u'].
  apply var_low_eq_ with (ℓ := ℓ) (u := u') ( v:= u'); crush.
  apply val_low_eq_refl.
Qed.




(* State low-equivalence *)

Inductive state_low_eq : typenv -> state -> state -> Prop:=
|  state_low_eq_ : forall Γ m1 m2,
       wf_mem m1 Γ ->
       wf_mem m2 Γ ->
       (forall x ℓ, Γ x = Some ℓ -> var_low_eq Γ m1 m2 x) ->
       state_low_eq Γ m1 m2.


Lemma state_low_eq_sym: 
  forall Γ m s, 
    state_low_eq Γ m s->
    state_low_eq Γ s m.
Proof.
  intros.
  inversion H.  
  subst.
  apply state_low_eq_; auto.
  intros.
  specialize (H2 x ℓ H3).
  apply var_low_eq_sym.
  auto.
Qed.




  
Lemma state_low_eq_trans:
  forall Γ m r s, 
    state_low_eq Γ m r ->
    state_low_eq Γ r s ->
    state_low_eq Γ m s.
Proof.
  intros.
  inversion H; inversion  H0; subst;
  remove_duplicate_hypothesis.
  
  apply state_low_eq_; auto.
  intros.
  repeat specialize_gen.
  inversion H3; inversion H9; subst.
  
  match goal with 
      | [ H: ?M ?x = Some ?U, H' : ?M ?x = Some ?V |- _ ]
          => assert (U = V) by (rewrite -> H in H'; crush); subst
  end.
  

  match goal with 
      | [ H: Γ ?x = Some ?U, H' : Γ ?x = Some ?V |- _ ]
          => assert (U = V) by (rewrite -> H in H'; crush); subst
  end.
  remove_duplicate_hypothesis.
  apply var_low_eq_ with (ℓ := ℓ1) (u:=u) (v := v0); auto.
  apply val_low_eq_sym_trans with (v := u0); auto.
Qed.  



  


Lemma state_low_eq_wf_refl:
  forall Γ m, 
    wf_mem m Γ
    -> state_low_eq Γ m m.

Proof.
  intros.
  apply state_low_eq_;auto.
  intros.
  apply var_low_eq_wf_refl with (ℓ := ℓ); auto.
Qed.





(* Relation between state and value low-equivalence *)

Lemma vars_low_eq: forall Γ m1 m2 x u v ℓ, 
  Γ x = Some ℓ ->
  state_low_eq Γ m1 m2 ->
  m1 x = Some u ->
  m2 x = Some v ->
  val_low_eq ℓ u v.
Proof.
  intros.
  inversion H0; subst.
  specialize (H5 x ℓ H).
  inversion H5; crush.

Qed.


(* Updating low-eq memories in a low-eq manner preserves low-equivalence *)

Lemma leq_updates: 
  forall Γ ℓ x m s u v,
    state_low_eq Γ m s ->
    Γ x = Some ℓ ->
    val_low_eq ℓ u v ->
    state_low_eq Γ (update_st m x u) (update_st s x v).
Proof.
  intros.

  inversion H.
  apply state_low_eq_; auto.
  
  Focus 3.

  {
    intros.
    Hint Resolve eq_nat_dec: SComp.
    rename x0 into y.
                               
    compare x y; auto with SComp.
    {
      intros; subst.
      apply var_low_eq_ with (ℓ:=ℓ) (u :=u) (v := v); auto;
      unfold update_st; unfold update_env; destruct eq_id_dec; crush.

    }
    {
      intros; subst.
      specialize (H4 y ℓ0 H8).
      unfold wf_mem in *.
      destruct_conj.
      specialize (H6 y ℓ0 H8); destruct H6.
      specialize (H5 y ℓ0 H8); destruct H5.

      unfold update_st in *; unfold update_env in *.
      apply var_low_eq_ with (ℓ := ℓ0) (u := x0) (v := x1); auto.
      destruct eq_id_dec; tryfalse; auto.
      destruct eq_id_dec; tryfalse; auto.
      inversion H4.
      subst.
      crush.
    }
    
  }

  Unfocus.
  {
    subst.
    unfold wf_mem in *.
    split; intros.
    {
      compare x0 x; auto with SComp; intros; subst.
      {
        exists ℓ;
        auto.
      }
      {
        destruct_conj.
        unfold update_st in *; unfold update_env in *; destruct eq_id_dec; tryfalse; auto.
        repeat specialize_gen; auto.
      }
    }
    {
     destruct_conj.

      compare x0 x; auto with SComp; intros; subst.
      {
        unfold update_st in *; unfold update_env in *; destruct eq_id_dec; tryfalse; auto.
        exists u; auto.
      }
      {
        unfold update_st in *; unfold update_env in *; destruct eq_id_dec; tryfalse; auto.
        repeat specialize_gen; auto.
      }
    }
  }
  
  {
    subst.
    unfold wf_mem in *.
    split; intros.
    {
      compare x0 x; auto with SComp; intros; subst.
      {
        exists ℓ;
        auto.
      }
      {
        destruct_conj.
        unfold update_st in *; unfold update_env in *; destruct eq_id_dec; tryfalse; auto.
        repeat specialize_gen; auto.
      }
    }
    {
     destruct_conj.

      compare x0 x; auto with SComp; intros; subst.
      {
        unfold update_st in *; unfold update_env in *; destruct eq_id_dec; tryfalse; auto.
        exists v; auto.
      }
      {
        unfold update_st in *; unfold update_env in *; destruct eq_id_dec; tryfalse; auto.
        repeat specialize_gen; auto.
      }
    }
    
  }
Qed.

(* TODO: beautify the above prove! :(  2015-04-03 *)



Lemma state_low_eq_trans_square:
                forall Γ m s m' s',
                  state_low_eq Γ m s ->
                  state_low_eq Γ m m' ->
                  state_low_eq Γ s s' ->
                  state_low_eq Γ m' s'.
Proof.
                intros.
                assert (state_low_eq Γ m s') by  apply (state_low_eq_trans H H1).
                assert (state_low_eq Γ m' m) by  (eapply state_low_eq_sym; assumption).
                apply (state_low_eq_trans H3 H2).
Qed.
