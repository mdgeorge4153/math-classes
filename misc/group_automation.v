Require Import
  Coq.Classes.Morphisms
  Coq.Lists.List
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.orders
  MathClasses.theory.groups
  MathClasses.implementations.peano_naturals.

Import ListNotations.

Section GroupAutomation.

Context `{Group A}.

Inductive gexp : Type :=
  | Atomic   : A -> gexp
  | Identity : gexp
  | GroupOp  : gexp -> gexp -> gexp
  | Inverse  : gexp -> gexp
  .

Fixpoint height a : nat := match a with
  | Atomic _    => 0
  | Identity    => 0
  | GroupOp a b => 1 + height a + height b
  | Inverse a   => 1 + height a
  end.

(*
Lemma height_right : ∀ a b, height a < height (GroupOp a b).
Proof. intros; simpl; repeat red.
apply order_preserving. apply _.
*)

Program Fixpoint flatten (e : gexp) {measure (height e)} : list gexp :=
  match e with
  | GroupOp a b           => flatten a ++ flatten b
  | Inverse (GroupOp a b) => flatten (Inverse b) ++ flatten (Inverse a)
  | Inverse Identity      => []
  | Inverse (Inverse a)   => flatten a
  | Inverse (Atomic a)    => [Inverse (Atomic a)]
  | Identity              => []
  | Atomic a              => [Atomic a]
end.
Solve All Obligations with program_simpl; simpl; red; repeat match goal with
  | [ |- (?x <= ?y)%nat ]         => setoid_replace ((x <= y)%nat) with (x ≤ y) by reflexivity
  | [ |- context[(?x + ?y)%nat] ] => setoid_replace ((x + y)%nat) with (x + y) by reflexivity
  | [ |- S _ ≤ S _ ]    => apply order_preserving; [apply _ | idtac]
  | [ |- ?x ≤ ?x + ?y ] => setoid_replace x with (x + 0) at 1 by (symmetry; apply right_identity)
                           ; apply order_preserving; [ apply _ | idtac ]
  | [ |- ?x ≤ ?y + ?x ] => setoid_replace (y + x) with (x + y) by apply commutativity
  | [ |- 0 ≤ ?x ]       => apply le_0_n
  | [ |- ?x ≤ ?x ]      => constructor
  | [ |- ?x ≤ S ?x ]    => constructor
end.


