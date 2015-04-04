Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.


Set Implicit Arguments.


Require Import Identifier Environment.


Definition state := @Env nat.
Definition update_st := @update_env nat.
Definition empty_state := @empty_env nat.

Inductive exp: Type :=
| ENum : nat -> exp
| EId  : id  -> exp
| EPlus: exp -> exp -> exp.
Lemma eq_exp_dec: forall e1 e2: exp, {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
  apply eq_nat_dec.
  apply eq_id_dec.
Qed.

Local Hint Resolve eq_exp_dec. 
Local Hint Resolve eq_id_dec.
  
Tactic Notation "exp_cases" tactic (first) ident (c) :=
 first; 
 [Case_aux c "ENum" | Case_aux c "EId" | Case_aux c "EPlus" ].


Inductive eval : exp -> state -> nat -> Prop:=
   | eval_const : forall n st, eval (ENum n) st n
   | eval_var: forall x st u, 
        st x = Some u ->
        eval (EId x) st u
   | eval_plus  : forall e1 e2 st u v z,
        eval e1 st u ->
        eval e2 st v ->
        z = u + v ->
        eval (EPlus e1 e2) st z.
Tactic Notation "eval_cases" tactic (first) ident (c) :=
 first; 
 [Case_aux c "eval_const" | Case_aux c "eval_var" | Case_aux c "eval_plus" ].


Lemma eval_const_aux : forall st n u, 
  eval (ENum n) st u -> u = n.
Proof.
  intros.
  inversion H.
  crush.
Qed.  

Lemma eval_var_aux : forall st x u,
  eval (EId x) st u -> st x = Some u.                      
Proof.
  intros. inversion H. assumption.
Qed.

(* Eval is deterministic *) 
Theorem eval_is_det: forall e st u v,
  eval e st u ->
  eval e st v ->
  u = v.
Proof.
  intros.
  generalize dependent v.

  eval_cases (induction H) Case.
     intros; inversion H0; crush.     
     intros; inversion H0; crush.
     intros. inversion H2. crush.
Qed.


Inductive cmd : Type :=
  | CStop : cmd 
  | CSkip : cmd 
  | CAss  : id  -> exp -> cmd
  | CSeq  : cmd -> cmd -> cmd
  | CIf   : exp -> cmd -> cmd -> cmd
  | CWhile: exp -> cmd -> cmd.

Tactic Notation "cmd_cases" tactic(first) ident(c) :=
  first; 
  [ Case_aux c "STOP" | Case_aux c "SKIP" 
  | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'STOP'" := CStop.
Notation "'SKIP'" := CSkip.
Notation "x '::=' a" :=(CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Inductive config : Type :=
   | Config 
       ( c : cmd) 
       ( st: state).
Notation "'〈' c ',' st '〉'" := (Config c st) (at level 0).

Reserved Notation "cfg '⇒' cfg'" (at level 40).

Inductive step : config -> config -> Prop :=
  | step_skip : forall st, 
      〈 SKIP, st 〉 ⇒ 〈 STOP, st 〉
  | step_assign: forall x e v st st',
       eval e st v -> 
       st' = update_st st x v ->
      〈 x ::= e, st 〉 ⇒  〈 STOP, st'〉
  | step_seq1 : forall c1 c1' c2 st st',
      〈 c1, st 〉⇒ 〈 c1', st' 〉-> 
      c1' <> STOP ->
      〈 c1 ;; c2, st 〉⇒ 〈 c1' ;; c2, st' 〉
  | step_seq2 : forall c1 c2 st st',
      〈 c1, st 〉⇒ 〈 STOP, st' 〉-> 
      〈 c1 ;; c2, st 〉⇒ 〈 c2, st' 〉
  | step_if1 : forall e c1 c2 st, 
       eval e st 1 ->
      〈 IFB e THEN c1 ELSE c2 FI, st 〉⇒〈 c1, st 〉
  | step_if2 : forall e c1 c2 st, 
       eval e st 0 ->
      〈 IFB e THEN c1 ELSE c2 FI, st 〉⇒〈 c2, st 〉
  | step_while : forall e c st,
      〈 WHILE e DO c END, st 〉⇒ 
          〈 IFB e THEN c;; WHILE e DO c END ELSE SKIP FI, st 〉
where "cfg '⇒' cfg' " := (step cfg cfg').


Lemma eq_cmd_dec: forall c1 c2: cmd, {c1 = c2} + { c1<>c2 }.
Proof.
  decide equality.
Qed.  
Local Hint Resolve eq_cmd_dec.  




                                     

(* Type system *)

Inductive level :=
  | Low : level
  | High : level.



Lemma eq_level_dec: forall l1 l2: level, {l1 = l2} + { l1<>l2 }.
Proof.

  decide equality.
Qed.  
Local Hint Resolve eq_level_dec.  


Inductive event := 
  | EmptyEvent : event 
  | StopEvent  : event
  | AssignmentEvent : level -> id -> nat -> event.

 

Lemma eq_event_dec: forall ev1 ev2: event, {ev1 = ev2} + { ev1<>ev2 }.
Proof.
  decide equality.
  apply eq_nat_dec.
Qed.  
Local Hint Resolve eq_event_dec.  



Inductive obs :Type :=
  | Halt : obs
  | Effect : level -> id -> nat-> obs.

Lemma eq_obs_dec: forall ev1 ev2: obs, {ev1 = ev2} + { ev1<>ev2 }.
Proof.
  decide equality.
  apply eq_nat_dec.
Qed.  
Local Hint Resolve eq_obs_dec.  

Inductive is_effect : obs -> Prop :=
  | is_effect_: forall ℓ i n, is_effect (Effect ℓ i n).

Tactic Notation "level_cases" tactic (first) ident (c):=
  first;
  [Case_aux c "Low" | Case_aux c "High" ].
Inductive flowsto: level -> level -> Prop := 
  | flowsto_sym: forall ℓ, flowsto ℓ ℓ
  | flowsto_ord: flowsto Low High.

Notation "ℓ '⊑' ℓ'" := (flowsto ℓ ℓ') (at level 35).



Inductive is_low_effect : obs -> Prop :=
  | is_low_effect_: forall i n, is_low_effect (Effect Low i n).

Lemma low_effects_are_effects: 
  forall o, 
    is_low_effect o -> is_effect o.
Proof.
  intros.
  inversion H.
  constructor.
Qed.
Hint Resolve low_effects_are_effects : Sec.


Lemma high_does_not_flow_to_low: ~ High ⊑ Low.
Proof.
  crush; inversion H.
Qed.


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
Reserved Notation  "'{' Γ ',' pc '⊢' c '}'" (at level 0, Γ at level 55, pc at level 35).
Inductive cmd_has_type : typenv -> level -> cmd -> Prop :=
(*  | T_Stop : forall Γ pc, 
     { Γ, pc ⊢ STOP }
*)
 | T_Skip : forall Γ pc,
     { Γ, pc ⊢ SKIP }
 | T_Assign: forall Γ pc x e ℓ ℓ',
     {{ Γ ⊢ e : ℓ }} ->
     Γ x = Some ℓ' ->
     ℓ ⊑ ℓ' ->
     pc ⊑ ℓ' ->
     { Γ , pc ⊢ (x::=e) }
 | T_Seq : forall Γ pc c1 c2,
     { Γ, pc ⊢ c1 } ->
     { Γ, pc ⊢ c2 } ->
     { Γ, pc ⊢ c1;;c2 }
 | T_If : forall Γ pc e ℓ pc' c1 c2,
     {{ Γ ⊢ e : ℓ }} ->
     ℓ ⊑ pc' ->
     pc ⊑ pc' ->
     { Γ, pc' ⊢ c1 } ->
     { Γ, pc' ⊢ c2 } ->
     { Γ, pc  ⊢ IFB e THEN c1 ELSE c2 FI }
 | T_While : forall Γ pc e ℓ pc' c, 
     {{ Γ ⊢ e : ℓ }} ->
     ℓ ⊑ pc' ->
     pc ⊑ pc' ->
     { Γ, pc' ⊢ c } ->
     { Γ, pc ⊢ WHILE e DO c END }
where "'{' Γ ',' pc '⊢' c '}'" := (cmd_has_type Γ pc c).

Tactic Notation "cmd_has_type_cases" tactic (first) ident (c) :=
 first; 
 [
   (* Case_aux c "T_Stop" |  *)
   Case_aux c "T_Skip" | Case_aux c "T_Assign"  | Case_aux c "T_Seq"
 | Case_aux c "T_if" | Case_aux c "T_While" ].






Inductive is_not_stop_config : config -> Prop :=
  | config_is_not_stop_config : forall c st, 
       c <> STOP ->
       is_not_stop_config 〈c, st 〉.




Lemma is_not_stop_config_neg: forall st,
    is_not_stop_config 〈STOP, st 〉 -> False.
Proof.
  intros.
  inversion H.
  apply H1.
  auto.
Qed. 


Inductive is_stop_config : config -> Prop:=
| config_is_stop_config : 
    forall st, 
      is_stop_config 〈 STOP, st 〉.


(* Instrumented semantics. We decorate the semantic transition with
   events. Events may correspond to either assignments, program
   termination (stop) or transitionary (empty) events.  *)


(* IOW, this is auxiliary semantics *)

Inductive event_step : typenv -> event -> config ->  config -> Prop :=
  | event_step_assign: 
      forall Γ ℓ x e v st st', 
        〈 x ::= e,  st〉 ⇒ 〈STOP, st' 〉->
        Γ (x) = Some ℓ ->
        eval e st v ->
        event_step Γ (AssignmentEvent ℓ x v)〈 x ::= e,  st〉 〈STOP, st' 〉

 | event_skip: forall Γ st,
      〈SKIP, st 〉 ⇒ 〈 STOP, st 〉 ->
       event_step Γ StopEvent 〈 SKIP, st 〉〈  STOP, st 〉

  | event_empty_branch: forall Γ e c1 c2 c' st, 
     〈IFB e THEN c1 ELSE c2 FI, st 〉 ⇒ 〈  c', st 〉 ->
     c' <> STOP ->
     event_step Γ EmptyEvent 〈IFB e THEN c1 ELSE c2 FI, st 〉〈  c', st 〉


  | event_empty_loop1 : forall Γ e c c' st,
      〈WHILE e DO c END, st 〉 ⇒ 〈c', st 〉 ->
      c' <> STOP ->
      event_step Γ EmptyEvent〈WHILE e DO c END, st 〉 〈c', st 〉

  | event_step_seq1 : forall Γ ev c1 c1' c2 st st',
      event_step Γ ev 〈c1, st  〉  〈 c1', st' 〉  ->
      ev <> StopEvent -> 
      c1' <> STOP ->
      event_step Γ ev 〈c1;;c2, st 〉  〈 c1';;c2, st' 〉 

  | event_step_seq2 : forall Γ  c1 ℓ x u c2 st st', 
                        c2 <> STOP ->
      event_step Γ (AssignmentEvent ℓ x u) 〈c1, st  〉 〈 STOP, st' 〉  -> 
      event_step Γ (AssignmentEvent ℓ x u) 〈c1;;c2, st 〉 〈c2, st' 〉 

  | event_step_seq3 : forall Γ c1 c2 st,
      event_step Γ StopEvent 〈c1, st  〉 〈 STOP, st 〉 -> 
      c2 <> STOP ->
      event_step Γ EmptyEvent 〈c1;;c2, st 〉  〈 c2, st 〉 .
 
      
Tactic Notation "event_step_cases" tactic (first) ident (c) := 
 first;
 [ Case_aux c "event_step_assign" |
   Case_aux c "event_skip"        |
   Case_aux c "event_empty_branch"|
   (* Case_aux c "event_stop_branch" | *)
   Case_aux c "event_empty_loop1" |
   Case_aux c "event_step_seq1"   |
   Case_aux c "event_step_seq2"   |
   Case_aux c "event_step_seq3"   ].





(* ℓ / stop transition *)



Inductive low_or_stop_event: 
  typenv -> level -> config -> config -> obs -> Prop :=
  | low_or_stop_event_stop: forall Γ ℓ ev cfg cfg',
      event_step Γ ev cfg cfg' -> 
      is_stop_config cfg' ->
      (ev = EmptyEvent \/ ev = StopEvent ) ->
      low_or_stop_event Γ ℓ cfg cfg' Halt

  | low_or_stop_event_high_assign: forall Γ ℓ  ℓ' x u cfg cfg',
      event_step Γ (AssignmentEvent ℓ' x u) cfg cfg' -> 
      is_stop_config cfg' ->
       ~ (ℓ' ⊑ ℓ ) ->
      low_or_stop_event Γ ℓ cfg cfg' Halt


  | low_or_stop_event_low_assign: forall Γ ℓ ℓ' x u cfg cfg',
      event_step Γ (AssignmentEvent ℓ' x u) cfg cfg' ->
      ℓ' ⊑ ℓ ->
      low_or_stop_event Γ ℓ cfg cfg' (Effect ℓ' x u).


Tactic Notation "low_or_stop_event_cases" tactic (first) ident (c) := 
 first;
 [ Case_aux c "low_or_stop_event_stop" |
   Case_aux c "low_or_stop_event_high_assign"  |
   Case_aux c "low_or_stop_event_low_assign" ].




(* non-ℓ transition *)

Inductive nonstophigh_or_empty_event : 
  typenv -> level -> config -> config -> Prop :=
   | nonstophigh_or_empty_event_empty : forall Γ ℓ cfg cfg', 
     event_step Γ EmptyEvent cfg cfg' ->
         nonstophigh_or_empty_event Γ ℓ cfg cfg'
   | nonstophigh_or_empty_event_assign : forall Γ ℓ ℓ' x u cfg cfg',
     event_step Γ (AssignmentEvent ℓ'  x u ) cfg cfg' ->
     ~ ( ℓ' ⊑ ℓ) ->
     is_not_stop_config cfg' -> 
         nonstophigh_or_empty_event Γ ℓ cfg cfg'.

Tactic Notation "nonstophigh_or_empty_event_cases" tactic (first) ident (c) :=
  first;
  [Case_aux c "nonstophigh_or_empty_event_empty" | 
   Case_aux c "nonstophigh_or_empty_event_assign" ].


Inductive high_event : typenv -> level -> config -> config -> Prop :=
   | high_term_event_other : 
       forall Γ ℓ ev cfg cfg', 
         event_step Γ ev cfg cfg' ->
         ev = EmptyEvent \/ ev = StopEvent ->
         high_event Γ ℓ cfg cfg'
   | high_event_assign :
       forall Γ ℓ ℓ' x u cfg cfg',
         event_step Γ (AssignmentEvent ℓ' x u) cfg cfg' ->
         ~ ( ℓ' ⊑ ℓ) ->
         high_event Γ ℓ cfg cfg'.




Tactic Notation "high_event_cases" tactic (first) ident (c) := 
 first;
 [ Case_aux c "high_term_event_other" |
   Case_aux c "high_event_assign"  ].



                
                


(* Multi-step reduction *)

Inductive multi {X:Type} (R: relation X): relation X :=
   | multi_refl : forall (x : X), multi R x x
   | multi_step : forall (x y z : X),
         R x y ->
         multi R y z ->
         multi R x z.
Local Hint Resolve multi_refl.


Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].


Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl. Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
   intros. 
   multi_cases (induction H) Case.
   Case "multi_refl".
      assumption.
  Case "multi_step".
      apply multi_step with y; try apply IHmulti; assumption.

Qed. 






(* Multi-step transitions *)
Definition multistep := multi step.
Notation " t '⇒*' t' " := (multistep t t') (at level 40).



(* 2015-03-25; transitioning the proof script to move all the bridge
step definitions and lemmas to the end *)





Inductive high_converges: typenv -> level -> config -> state -> Prop :=
| stop_converges: 
    forall Γ ℓ st, 
      high_converges Γ ℓ 〈 STOP, st 〉st
| high_step_converges : 
    forall Γ ℓ cfg s cfg',
      multi (nonstophigh_or_empty_event Γ ℓ) cfg cfg' ->
      high_event Γ ℓ cfg' 〈 STOP, s 〉->
      high_converges Γ ℓ cfg s.






Tactic Notation "high_converges_cases" tactic (first)  ident (c ) :=
  first;
  [ Case_aux c "high_converges_"].

Notation " t '⇒/(NH,' Γ ')'  t' " := 
      (nonstophigh_or_empty_event Γ Low t t') (at level 40).

Notation " t '⇒/(H,' Γ ')'  t' " := 
      (high_event Γ Low t t') (at level 40).

Notation " t '⇒*/(NH,' Γ ')'  t' " := 
      (multi (nonstophigh_or_empty_event Γ Low) t t') (at level 40).

Notation " t '⇒/(SL,' Γ ',' obs ')'  t' " :=
      (low_or_stop_event Γ Low t t' obs) (at level 40).

Notation " t '⇓/(H,' Γ ')'  m ":=
      (high_converges Γ Low t m) (at level 40).











Definition is_not_assign (c:cmd) := 
  ~ (exists x e, c = x ::= e).

Example stop_is_not_assign:
  is_not_assign (STOP).
Proof.
  unfold is_not_assign.
  unfold not.    
  intros.
  destruct H.
  destruct H.
  inversion H.
Qed.
  

Lemma is_not_assign_neg: forall x e, 
    is_not_assign (x ::= e) -> False.
Proof.
  intros. 
  unfold is_not_assign in H.
  assert (exists x0 e0, x ::= e = x0 ::= e0) as Y.
  exists x.
  exists e.
  auto.
  contradiction.
Qed.









Ltac lift_event_step cfg :=
  match goal with 
    | [ H : event_step _ _ cfg _ |- _ ]  =>
      inversion H;
        try match goal with 
          | [ H : cfg ⇒  _ |- _ ] =>
            inversion H
        end
  end.
    

Ltac lift_inversion_high cfg := 
  match goal with          
    | [ H : cfg ⇒/(NH, _) _ |- _ ] => 
      inversion H;
        lift_event_step cfg            
  end.

Ltac lift_inversion_high_multi cfg :=
  match goal with
    | [ H : cfg  ⇒*/(NH, _) _ |- _ ] =>
      multi_cases (inversion H) Case; (try lift_inversion_high cfg)
  end.

Ltac lift_inversion_low cfg :=
  match goal with 
    | [ H : cfg  ⇒/(SL, _, _) _ |- _ ] =>
      inversion H;
        lift_event_step cfg
  end.


Lemma stop_makes_no_steps: forall Γ m c1 m1, 
  〈STOP, m 〉 ⇒*/(NH, Γ) 〈c1, m1 〉->
   c1 = STOP /\ m1 = m.
Proof.
   intros.
   lift_inversion_high_multi 〈STOP, m 〉; crush.
Qed.




Lemma skip_makes_no_high_steps: 
  forall Γ m c1 m1,
   〈SKIP, m 〉 ⇒*/(NH, Γ) 〈c1, m1 〉-> 
    c1 = SKIP /\ m1 = m.
Proof.
  intros. 
  lift_inversion_high_multi 〈SKIP, m 〉; crush.
Qed.

Lemma skip_makes_no_high_steps_cfg:
  forall Γ m cfg,
    〈SKIP, m 〉 ⇒*/(NH, Γ) cfg -> 
    cfg = 〈 SKIP, m 〉.
Proof.           
  intros.
  destruct cfg.
  assert (c = SKIP /\ st = m) ;
    [ apply skip_makes_no_high_steps with Γ |  idtac]; crush.
Qed.  
  

Ltac rewrite_conj X :=
  destruct X as (X1, X2);
  rewrite X1, X2 in *;
  clear  X1 X2.


Lemma env_is_det: 
  forall {X:Type} (env: @Env X) x (u:X) (v:X),
  env x = Some u ->
  env x = Some v -> 
  u = v.
Proof.
  intros.
  crush.
Qed.


(* TODO: 2014-05-18 : this lemma needs strengthening *)



Lemma empty_event_is_a_non_stop_high_event: 
  forall Γ c m c' m', 
    event_step Γ EmptyEvent 〈 c, m 〉 〈 c', m' 〉->
    〈c, m 〉 ⇒/(NH, Γ) 〈c', m' 〉.
Proof.
  intros.
  apply nonstophigh_or_empty_event_empty.
  assumption.
Qed.


Ltac tt_empty_event_is_a_non_stop_high_event c m:=
  match goal with 
    | [ H: event_step ?Γ EmptyEvent 〈 c, m 〉 〈 ?c', ?m' 〉 |- _ ] =>
      apply empty_event_is_a_non_stop_high_event in H
  end.

Ltac tt_empty_event_is_a_seq_of_non_stop_high_events c m:=
  match goal with 
    | [ H: event_step ?Γ EmptyEvent 〈 c, m 〉 〈 ?c', ?m' 〉 |- _ ] =>
      apply empty_event_is_a_non_stop_high_event in H;
        apply multi_step with 〈c', m' 〉
  end.




Ltac inv_event_step :=
  match goal with [ H : event_step _ _ _ _ |- _ ]
                  => inversion H end.

Ltac inv_event_step_no_clear :=
  match goal with [ H : event_step _ _ _ _ |- _ ]
                        => inversion H end.

Ltac inv_event_step_clear :=
  match goal with [ H : event_step _ _ _ _ |- _ ]
                  => inversion H ; clear H
  end.


Ltac inv_nh_multi:=
  match goal with 
      [ H : _  ⇒*/(NH, _) _ |- _ ] => inversion H; clear H
  end.

Ltac inv_nh_step:=
  match goal with 
      [ H : _  ⇒/(NH, _) _ |- _ ] => inversion H; clear H
  end.

Ltac inv_sl_step:=
  match goal with 
      [ H : _  ⇒/(SL, _, _) _ |- _ ] => inversion H; clear H
  end.


Ltac inv_non_stop_config:=
  match goal with
    | [ H : context [is_not_stop_config] |- _ ] => 
      inversion H
  end.


Ltac inv_stop_config:=
  match goal with
    | [ H : context [is_stop_config] |- _ ] => 
      inversion H
  end.


Lemma first_seq_comp_low_step: 
  forall Γ i ca cb m c_end m_end,
    〈ca;; cb, m 〉 ⇒/(SL, Γ, i) 〈c_end, m_end 〉 ->
    exists d,
      (〈ca, m 〉 ⇒/(SL, Γ, i) 〈d, m_end 〉 )
      /\ ( d <> STOP -> c_end = (d;; cb))
      /\ ( d =  STOP -> c_end = cb)
      /\ is_low_effect i.
Proof.
  intros.
  
  low_or_stop_event_cases (inversion H ) Case.
  Case "low_or_stop_event_stop".
  {
    inv_event_step_no_clear; subst;
    inv_stop_config; crush.    
  }

  Case "low_or_stop_event_high_assign" .
  {
    inv_event_step_no_clear; subst;
    inv_stop_config; crush.
  }

  Case "low_or_stop_event_low_assign".
  {
    inv_event_step_clear; subst;
    
    let CC := 
        match goal with 
          | [_ : event_step _ _ _ 〈?C1, m_end 〉, 
             _ : ?C1 <> STOP |- _ ]  => C1
                                               
          | [_ : event_step _ _ _ 〈STOP, m_end 〉 |- _]
            => eval simpl in STOP
    end
    in
      (exists CC); crush;
    try (apply low_or_stop_event_low_assign); try constructor; auto;
    match goal with | [ H: context [Low] |- _  ] =>
                      assert (ℓ' = Low) by ( inversion H; auto); subst
    end;
    constructor.
  }
Qed.



Lemma first_step_comp_high_step: 
  forall Γ ca cb m c_end m_end,
    〈ca;; cb, m 〉 ⇒/(H, Γ) 〈c_end, m_end 〉 ->
    exists d,
      (〈ca, m 〉 ⇒/(H, Γ) 〈d, m_end 〉 )
      /\ ( d <> STOP -> c_end = (d;; cb))
      /\ ( d =  STOP -> c_end = cb).                                   
Proof.
  intros.
  inversion H.
  
  dependent induction H0; crush;

  
  match goal with
    | [ H : event_step Γ ?ev 〈_, _ 〉 〈?c, _ 〉 |- _ ] =>
      (exists c);
        split;                         
        try (apply high_term_event_other with ev); 
        crush  
  end.
    
  match goal with
    | [ H: context [AssignmentEvent] |- _ ] =>


       inversion H
       ; clear H
               
       ; match goal with
           | [H : event_step _ (AssignmentEvent ?ℓ'' ?X ?U ) 〈ca, m 〉 〈?c', m_end 〉|- _] =>
             (exists c')
             ; crush
             ; apply high_event_assign with ℓ'' X U
             ; crush
         end
  end.
Qed.


Lemma first_step_comp_high_step' : 
  forall Γ d ca cb m m_end,
    (〈ca, m 〉 ⇒/(H, Γ) 〈d, m_end 〉 ) ->
    cb <> STOP ->
    exists c_end,
      〈ca;; cb, m 〉 ⇒/(H, Γ) 〈c_end, m_end 〉 
      /\ ( d <> STOP -> c_end = (d;; cb))
      /\ ( d =  STOP -> c_end = cb). 
Proof.
  intros.
  high_event_cases (inversion H) Case.
 
  match goal with 
    | [ H: context [event_step] |- _] => 
      event_step_cases (inversion H) SCase  
  end; crush;
  match goal with 
    | [ H : context[StopEvent] |- _ ] =>
      (exists cb)
      ; crush
      ; apply high_term_event_other with EmptyEvent
      ; try (apply event_step_seq3); auto
    
    | [ H : event_step _ EmptyEvent _ 〈 ?d, _ 〉 |- _ ] => 
      (exists (d;;cb))
       ; crush
       ; try (  apply high_term_event_other with EmptyEvent;
                try (apply event_step_seq1); crush )


  end.

  match goal with [ H: context [event_step] |- _] => 
                  (inversion H)   end.

  match goal with 
      | [ H: 〈_, _ 〉 ⇒ 〈STOP, _ 〉 |- _] =>
        (exists cb);
          crush;
          apply high_event_assign with ℓ' x u;
          try (apply event_step_seq2); 
          crush 
  end.
  subst.


  exists ((c1';;c2);;cb).
  crush.
  apply high_event_assign with ℓ' x  u;
  try (apply event_step_seq1);
    crush.

  
  subst.
  exists (d;; cb).
  crush.
  apply high_event_assign with ℓ' x u;
  try (apply event_step_seq1);
  crush.
Qed.

  


Lemma nonstop_high_event_is_a_high_event: 
  forall Γ ca m c_end m_end,
    〈ca, m 〉 ⇒/(NH, Γ) 〈c_end, m_end 〉 ->
    〈ca, m 〉 ⇒/(H, Γ) 〈c_end, m_end 〉.
Proof.
  intros. 
  nonstophigh_or_empty_event_cases (inversion H) Case;
  [ apply high_term_event_other with EmptyEvent |
    apply high_event_assign with ℓ' x u];
    auto.
Qed.




  

Lemma stop_events_end_in_stop: 
  forall Γ cfg c_end m_end,
    event_step Γ StopEvent cfg 〈 c_end, m_end 〉->
    c_end = STOP.
Proof.
  intros.
  inversion H; crush.
Qed.



  
Lemma high_event_to_nonstop_high_event: 
  forall Γ ca m c_end m_end,
    〈ca, m 〉 ⇒/(H, Γ) 〈c_end, m_end 〉 ->
    c_end <> STOP ->
    〈ca, m 〉 ⇒/(NH, Γ) 〈c_end, m_end 〉.
Proof.
  intros.
  high_event_cases (inversion H) Case; crush.
  apply nonstophigh_or_empty_event_empty; auto.
  apply stop_events_end_in_stop in H1; crush.
  apply nonstophigh_or_empty_event_assign with ℓ' x u; crush.
  apply config_is_not_stop_config; auto.
Qed.  

Lemma first_step_comp_nonstop_high_step: 
  forall Γ ca cb m c_end m_end,
    〈ca;; cb, m 〉 ⇒/(NH, Γ) 〈c_end, m_end 〉 ->
    exists d,
      (〈ca, m 〉 ⇒/(H, Γ) 〈d, m_end 〉 )
      /\ ( d <> STOP -> c_end = (d;; cb))
      /\ ( d =  STOP -> c_end = cb).
Proof.
  intros. 
  apply nonstop_high_event_is_a_high_event in H.
  apply first_step_comp_high_step.
  assumption.
Qed.



Lemma nonstopcommands_do_not_end_in_stop:
  forall Γ c m m',
    〈c, m 〉 ⇒/(NH, Γ) 〈STOP, m' 〉 -> False.
Proof.
  intros.
  inversion H; subst.
  inversion H0; crush.
  inversion H0; crush.
  inversion H2.
  auto.
Qed.

Lemma nonstopcommands_do_not_end_in_stop':
  forall Γ c c' m m',
    〈c, m 〉 ⇒/(NH, Γ) 〈c', m' 〉 -> c' <> STOP.
Proof.
  intros.
  inversion H; subst.
  inversion H0; crush.
  inversion H0; crush.
  inversion H2.
  auto.
Qed.


Lemma nonstopcommands_multi_do_not_end_in_stop:
  forall Γ c c' m m',
      c <> STOP ->
      〈c, m 〉 ⇒*/(NH, Γ) 〈c', m' 〉
              -> (c' <> STOP).
  Proof.
    intros.
    
    dependent induction H0.
    auto.
    destruct y.

    apply nonstopcommands_do_not_end_in_stop' in H1.

    specialize IHmulti with m' st c' c0.
    crush.
Qed.


Lemma nonstop_high_event_is_a_high_event_and_does_not_end_in_stop: 
          forall Γ ca m c_end m_end,
            〈ca, m 〉 ⇒/(NH, Γ) 〈c_end, m_end 〉 ->
            〈ca, m 〉 ⇒/(H, Γ) 〈c_end, m_end 〉
            /\ c_end <> STOP.
Proof.
  intros.
  split; 
    [ apply nonstop_high_event_is_a_high_event 
    | destruct c_end;crush;
      apply nonstopcommands_do_not_end_in_stop with Γ (ca) m m_end
    ];
  auto.
Qed.

Lemma high_step_converges_alt:
  forall Γ c m c' m' m_end, 
    〈c, m 〉 ⇒/(NH, Γ) 〈c', m' 〉 ->
    〈c', m' 〉 ⇓/(H, Γ) m_end ->  
    〈c, m 〉 ⇓/(H, Γ) m_end. 
Proof.
  intros. 
  dependent induction H0.
  apply nonstopcommands_do_not_end_in_stop in H. elim H.   
  apply high_step_converges with cfg'; auto.
  apply multi_step with 〈c', m' 〉; auto.
Qed.
 


    



Lemma stop_makes_no_steps_gen: 
  forall Γ m cfg,
    〈STOP, m 〉 ⇒*/(NH, Γ) cfg ->
    cfg = 〈STOP, m 〉.
Proof.
  intros.
  destruct cfg.
  assert (c = STOP /\ st = m).
  apply stop_makes_no_steps with Γ.
  crush. crush.
Qed.




Lemma seq_comp_decomp_high: 
  forall Γ ca cb c m m', 
    〈 ca;; cb, m 〉⇒*/(NH, Γ) 〈c, m'〉 ->
    cb <> STOP -> 
    ( exists ca',
        (c = (ca';;cb) /\ 〈 ca, m 〉⇒*/(NH, Γ) 〈ca', m'〉)) \/
    ( exists m_b, 
        (〈 ca, m 〉⇓/(H, Γ) m_b /\ 〈 cb, m_b 〉⇒*/(NH, Γ) 〈c, m'〉 )) .
Proof.                  
  intros.
  multi_cases (dependent induction H) Case.

  {
    Case "multi_refl".
    left.
    exists ca.
    crush.
  }
  {
    Case "multi_step".
    destruct y.    
    eapply first_step_comp_nonstop_high_step in H. crush.
    rename x into ca'.
    compare ca' STOP; crush.
    {
      right.
      exists st.
      split; try (apply high_step_converges with 〈ca, m 〉); auto.
    }
    {
      specialize IHmulti with ca' cb  c  st  m'.
      destruct IHmulti; auto.      
      {
        match goal with 
          | [ H: context [exists _, _ ]|- _ ] => destruct H as [d]; 
              destruct H;
              SCase "exists d"; subst
        end.
        left.
        exists d; crush.
        apply multi_step with 〈ca', st 〉; 
          [apply high_event_to_nonstop_high_event | idtac]; auto.        
      }
      {
        match goal with 
          | [ H : context [exists _, _] |- _] => destruct H as [m_b];
              destruct H;
              SCase "exists m_b"; subst
        end.
        right.
        exists m_b.
        split; auto.
        apply high_step_converges_alt with ca' st; auto.
        apply high_event_to_nonstop_high_event; auto.
      }      
    }
  }
Qed.




Lemma wt_programs_are_not_stop: 
  forall Γ pc c,
     { Γ, pc ⊢ c } ->
     c <> STOP.
Proof.
  intros.
  induction H; crush.
Qed.





Ltac tt_eval_is_det:=      
  match goal with 
    | [ H:  eval ?E ?M ?u, H' : eval ?E ?M ?v |- _ ] 
      => apply eval_is_det with (e:=E) (st:=M); auto
  end.

Local Hint Resolve flowsto_sym.
Local Hint Resolve high_does_not_flow_to_low.




Local Hint Resolve config_is_stop_config.

Lemma from_high_stop_event_to_low_stop_event:
  forall Γ cfg s,
    cfg ⇒/(H, Γ) 〈STOP, s 〉->
    cfg ⇒/(SL, Γ, Halt) 〈STOP, s 〉.
Proof.
  intros.
  inversion H.
  inv_event_step; crush.
  {
    apply low_or_stop_event_stop with  (ev := StopEvent); crush.
  }

   
  
  {
    apply low_or_stop_event_high_assign with  ℓ' x u; crush.

  }

Qed.




Lemma seq_com_aux_nonstopmany: 
  forall Γ ca m cb ca' st,
    cb <> STOP ->
    〈ca, m 〉 ⇒*/(NH, Γ) 〈ca', st 〉 ->
    〈ca;; cb, m 〉 ⇒*/(NH, Γ) 〈ca';;cb , st 〉.

Proof.
  intros.
  multi_cases (dependent induction H0) Case; auto.
  destruct y.
  specialize IHmulti with c st0 ca' st.       
  crush.
  
  assert ( 〈  ca;; cb, m 〉 ⇒/(NH, Γ) 〈c;; cb, st0 〉 ) as X. 
  
  apply high_event_to_nonstop_high_event; crush.
  apply nonstop_high_event_is_a_high_event_and_does_not_end_in_stop
    in H1.
  destruct H1.
  apply first_step_comp_high_step' 
  with Γ c ca cb m st0 in H1; crush.
  apply multi_step with 〈c;; cb, st0 〉; crush.
Qed.


