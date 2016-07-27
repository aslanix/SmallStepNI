Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.


Set Implicit Arguments.


Require Import Identifier Environment.
Require Import Imperative.


                                     

(* Type system *)

Inductive level :=
  | Low : level
  | High : level.



Lemma eq_level_dec: forall l1 l2: level, {l1 = l2} + { l1<>l2 }.
Proof.


  decide equality.
Qed.  
Hint Resolve eq_level_dec.  



Hint Resolve eq_exp_dec. 
Hint Resolve eq_id_dec.
  

Tactic Notation "level_cases" tactic (first) ident (c):=
  first;
  [Case_aux c "Low" | Case_aux c "High" ].



Inductive flowsto: level -> level -> Prop := 
  | flowsto_sym: forall ℓ, flowsto ℓ ℓ
  | flowsto_ord: flowsto Low High.

Notation "ℓ '⊑' ℓ'" := (flowsto ℓ ℓ') (at level 35).


  
  
Definition typenv := @Env level.

Reserved Notation "'{{' Γ '⊢' e ':' ℓ '}}'" (at level 0, Γ at level 50, e at level 99).
Inductive exp_has_level : typenv -> exp -> level -> Prop :=
  | T_Const : forall Γ n ℓ, 
      {{ Γ ⊢ ENum n : ℓ }}
  | T_Id : forall Γ x ℓ, 
      (Γ x) = Some ℓ -> 
      {{ Γ ⊢ EId x : ℓ  }}
  | T_Plus : forall Γ e1 e2 ℓ, 
      {{ Γ ⊢ e1 : ℓ }} -> 
      {{ Γ ⊢ e2 : ℓ }} -> 
      {{ Γ ⊢ (EPlus e1 e2) : ℓ }}
  | T_Sub  : forall Γ e ℓ ℓ',
      {{ Γ ⊢ e : ℓ }} ->
      ℓ ⊑ ℓ'  ->
      {{ Γ ⊢ e : ℓ' }}
where "'{{' Γ '⊢' e ':' ℓ '}}' " := (exp_has_level Γ e ℓ).


Tactic Notation "exp_has_level_cases" tactic (first) ident (c) :=
 first; 
 [Case_aux c "T_Const" | Case_aux c "T_Id" | Case_aux c "T_Plus"  | Case_aux c "T_Sub" ].







(* Volpano-Smith simple typing *)
Reserved Notation  "'-{' Γ ',' pc '⊢' c '}-'" (at level 0, Γ at level 55, pc at level 35).
Inductive cmd_has_type : typenv -> level -> cmd -> Prop :=
 | T_Skip : forall Γ pc,
     -{ Γ, pc ⊢ SKIP }-
 | T_Assign: forall Γ pc x e ℓ ℓ',
     {{ Γ ⊢ e : ℓ }} ->
     Γ x = Some ℓ' ->
     ℓ ⊑ ℓ' ->
     pc ⊑ ℓ' ->
     -{ Γ , pc ⊢ (x::=e) }-
 | T_Seq : forall Γ pc c1 c2,
     -{ Γ, pc ⊢ c1 }- ->
     -{ Γ, pc ⊢ c2 }- ->
     -{ Γ, pc ⊢ c1;;c2 }-
 | T_If : forall Γ pc e ℓ pc' c1 c2,
     {{ Γ ⊢ e : ℓ }} ->
     ℓ ⊑ pc' ->
     pc ⊑ pc' ->
     -{ Γ, pc' ⊢ c1 }- ->
     -{ Γ, pc' ⊢ c2 }- ->
     -{ Γ, pc  ⊢ IFB e THEN c1 ELSE c2 FI }-
 | T_While : forall Γ pc e ℓ pc' c, 
     {{ Γ ⊢ e : ℓ }} ->
     ℓ ⊑ pc' ->
     pc ⊑ pc' ->
     -{ Γ, pc' ⊢ c }- ->
     -{ Γ, pc ⊢ WHILE e DO c END }-
     
where "'-{' Γ ',' pc '⊢' c '}-'" := (cmd_has_type Γ pc c).

Tactic Notation "cmd_has_type_cases" tactic (first) ident (c) :=
 first; 
 [
   (* Case_aux c "T_Stop" |  *)
   Case_aux c "T_Skip" | Case_aux c "T_Assign"  | Case_aux c "T_Seq"
 | Case_aux c "T_if" | Case_aux c "T_While" ].


Lemma high_does_not_flow_to_low: ~ High ⊑ Low.
Proof.
  crush; inversion H.
Qed.




(* TODO: move this to Types; 2016-07-26 *)
Lemma wt_programs_are_not_stop: 
  forall Γ pc c,
     -{ Γ, pc ⊢ c }- ->
     c <> STOP.
Proof.
  intros.
  induction H;
    congruence.
Qed.


Ltac tt_wt_cmd_is_not_stop_save_name c H_new :=
  match goal with 
      [H : -{ _, _ ⊢ c }- |- _ ]
            
      =>
      assert (H_new := H);
        apply wt_programs_are_not_stop in H; auto
  end.
      