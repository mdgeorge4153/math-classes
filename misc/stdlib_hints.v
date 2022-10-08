Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.RelationClasses.
Require Import Coq.Unicode.Utf8.

#[global]
Hint Unfold Proper respectful.

#[global]
Hint Unfold Reflexive Symmetric Transitive.
#[global]
Hint Constructors PreOrder.

(*
   These tactics automatically solve symmetry and transitivity problems,
   when the hypothesis are in the context. They should be added as hints
   like

     Hint Extern 4 (?x = ?x) => reflexivity.
     Hint Extern 4 (?x = ?y) => auto_symm.
     Hint Extern 4 (?x = ?y) => auto_trans.

   once the appropriate head constants are defined.
*)
Ltac auto_symm := match goal with
                    [ H: ?R ?x ?y |- ?R ?y ?x] => apply (symmetry H)
                  end.
Ltac auto_trans := match goal with
                    [ H: ?R ?x ?y, I: ?R ?y ?z |- ?R ?x ?z] => apply (transitivity H I)
                  end.

(*
   These tactics make handling sig types slightly easier.
*)
Ltac exist_hyp := match goal with [ H : sig ?P |- ?P _  ] => exact (proj2_sig H) end.
#[global]
Hint Extern 0 => exist_hyp: core typeclass_instances.

Ltac exist_proj1 :=
  match goal with
    | [ |- context [proj1_sig ?x] ] => apply (proj2_sig x)
  end.
#[global]
Hint Extern 0 => exist_proj1: core typeclass_instances.
