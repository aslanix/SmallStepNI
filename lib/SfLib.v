(** * SfLib: Software Foundations Library *)

(* $Date: 2012-04-05 12:16:07 -0400 (Thu, 05 Apr 2012) $ *)

(** Originally this file collected a large number of definitions and
    exercises from the early Software Foundations chapters (Basics.v, List.v,
    Poly.v, Ind.v, Logic.v, ...). This development only relies on a small part
    of it, so the unused Software-Foundations exercise material (the toy
    inductives [ev]/[appears_in]/[next_nat]/..., the [beq_nat]/[ble_nat]
    lemmas, the [id]/[beq_id]/[partial_map]/[extend] maps, and SfLib's own
    [multi]) has been removed. What remains is the [Case]/[SCase] case-marker
    tactics, the [solve by inversion] tactic, and the [relation],
    [deterministic] and [ex_falso_quodlibet] definitions, which are the items
    actually used elsewhere. *)

(** * From the Coq Standard Library *)

From Stdlib Require Export Bool.
From Stdlib Require Export List.
From Stdlib Require Export Arith.

From Stdlib Require Export String. Global Open Scope string_scope.

(** * Case-analysis markers (from Basics.v) *)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(** * From Logic.v *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

(** * From Later Files *)

Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(** * Some useful tactics *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

(* NB: The original SfLib also defined numbered variants
   [solve by inversion 1 | 2 | 3]. In recent Rocq, using the bare numeric
   literals "1", "2", "3" as Tactic Notation tokens reserves them as keywords,
   which then prevents 1/2/3 from being parsed as numeric term literals
   everywhere else. We therefore keep only the (unnumbered) [solve by inversion]
   form, which performs a single inversion step. *)
Tactic Notation "solve" "by" "inversion" :=
  solve_by_inversion_step idtac.
