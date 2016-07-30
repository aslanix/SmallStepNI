Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.


Set Implicit Arguments.


Require Import Identifier Environment.
Require Import Imperative Types.



Inductive event :=
  | EmptyEvent : event
  | AssignmentEvent : level -> id -> nat -> event.


Lemma eq_event_dec: forall ev1 ev2: event, {ev1 = ev2} + { ev1<>ev2 }.
Proof.
  decide equality.
  apply eq_nat_dec.
Qed.
Hint Resolve eq_event_dec.



(* Instrumented semantics. We decorate the semantic transition with
   events. Events may correspond to either assignments, program
   termination (stop) or transitionary (empty) events.  *)



Inductive event_step : typenv -> event -> config ->  config -> Prop :=
  | event_step_assign:
      forall Γ ℓ x e v st st',
        〈 x ::= e,  st〉 ⇒ 〈STOP, st' 〉->
        Γ (x) = Some ℓ ->
        eval e st v ->
        event_step Γ (AssignmentEvent ℓ x v)〈 x ::= e,  st〉 〈STOP, st' 〉

 | event_skip: forall Γ st,
      〈SKIP, st 〉 ⇒ 〈 STOP, st 〉 ->
       event_step Γ EmptyEvent 〈 SKIP, st 〉〈  STOP, st 〉

  | event_empty_branch: forall Γ e c1 c2 c' st,
     〈IFB e THEN c1 ELSE c2 FI, st 〉 ⇒ 〈  c', st 〉 ->
     c' <> STOP ->
     event_step Γ EmptyEvent 〈IFB e THEN c1 ELSE c2 FI, st 〉〈  c', st 〉


  | event_empty_loop1 : forall Γ e c c' st,
      〈WHILE e DO c END, st 〉 ⇒ 〈c', st 〉 ->
      c' <> STOP ->
      event_step Γ EmptyEvent〈WHILE e DO c END, st 〉 〈c', st 〉

  | event_step_seq1 : forall Γ ev c1 c1' c2 st st',
      event_step Γ ev 〈c1, st〉  〈 c1', st'〉  ->
      c1' <> STOP ->
      event_step Γ ev 〈c1;;c2, st〉  〈c1';;c2, st'〉

  | event_step_seq2 : forall Γ ev c1 c2 st st',
                        c2 <> STOP ->
      event_step Γ ev 〈c1, st  〉 〈 STOP, st' 〉  ->
      event_step Γ ev 〈c1;;c2, st 〉 〈c2, st' 〉 .


Tactic Notation "event_step_cases" tactic (first) ident (c) :=
 first;
 [ Case_aux c "event_step_assign" |
   Case_aux c "event_skip"        |
   Case_aux c "event_empty_branch"|
   (* Case_aux c "event_stop_branch" | *)
   Case_aux c "event_empty_loop1" |
   Case_aux c "event_step_seq1"   |
   Case_aux c "event_step_seq2"   ].


(*
Lemma is_not_stop_config_neg: forall st,
    is_not_stop_config 〈STOP, st 〉 -> False.
Proof.
  intros.
  inversion H.
  apply H1.
  auto.
Qed.
*)
