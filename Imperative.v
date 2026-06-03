From Stdlib Require Import Bool Arith List.
Require Import CpdtTactics SfLib LibTactics.
From Stdlib Require Import Program.Equality.


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

#[local] Hint Resolve eq_exp_dec : core.
#[local] Hint Resolve eq_id_dec : core.

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
#[export] Hint Rewrite eval_is_det : core.


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

Definition cmd_of cfg :=
  match cfg with
    | Config c _ => c
  end.
#[export] Hint Unfold cmd_of : core.

Definition state_of cfg :=
  match cfg with
    | Config _ m => m
  end.
#[export] Hint Unfold state_of : core.

(* lifiting reasoning about STOP to configurations *)

Definition is_stop cfg := cmd_of cfg = STOP.
#[export] Hint Unfold is_stop : core.
Definition is_not_stop cfg := cmd_of cfg <> STOP.
#[export] Hint Unfold is_not_stop : core.




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
  | step_if1 : forall e u c1 c2 st,
       eval e st u -> u <> 0 ->
      〈 IFB e THEN c1 ELSE c2 FI, st 〉⇒〈 c1, st 〉
  | step_if2 : forall e c1 c2 st,
       eval e st 0 ->
      〈 IFB e THEN c1 ELSE c2 FI, st 〉⇒〈 c2, st 〉
  | step_while : forall e c st,
      〈 WHILE e DO c END, st 〉⇒
          〈 IFB e THEN c;; WHILE e DO c END ELSE SKIP FI, st 〉
where "cfg '⇒' cfg' " := (step cfg cfg').

(* The [sem] hint database collects the constructors of the semantic, typing
   and low-equivalence relations. It is deliberately kept separate from [core]
   so that the existing [crush]/[auto]/[eauto]/[*]/[~] automation is unaffected
   (the development stays stable), while new or refactored proofs can opt in to
   the extra automation with [eauto with sem]. *)
Create HintDb sem.
#[export] Hint Constructors eval step : sem.

(* [crush_sem] is a strictly stronger finisher than [crush] for this
   development: it runs [crush] for simplification and then discharges any
   remaining constructor-shaped goals (typing / semantics / low-equivalence)
   with the [sem] database. It is provided as an opt-in tactic rather than by
   redefining [crush], which -- like adding these hints to [core] -- would
   disturb the existing auto-star-based proofs. *)
Ltac crush_sem := crush; eauto with sem.


Lemma eq_cmd_dec: forall c1 c2: cmd, {c1 = c2} + { c1<>c2 }.
Proof.
  decide equality.
Qed.
#[local] Hint Resolve eq_cmd_dec : core.
