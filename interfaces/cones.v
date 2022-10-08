(*
This file gives an alternative characterization of ring orderings based on
positive cones.  The typeclasses here are based on a math overflow post by
David Feuer: https://math.stackexchange.com/q/293000

A cone is a subset that is closed under the operations of the algebraic
structure.  Think of it as an axiomatization of the set of positive (or
nonnegative) elements.

We can generalize the relationship between positivity and ordering as follows:
Given a cone C on A, we can derive a relation R on A by x R y if y - x ∈ C.  If
C is the set of nonnegative elements then R is (≤), while if C is the set of
positive elements then R is (<).  Similarly, we can translate an
ordering R into a cone.

The classes of cones here vary on three axes.  The first axis is
the algebraic structure:

* a SemiGroupCone is closed under (&).
  For SemiGroupCones, (&) is order preserving in R.

* a GroupCone interacts appropriately with inverses.
  For GroupCones, R antisymmetric and transitive.

* a RingCone  is closed under (+) and ( * ).

* a FieldCone behaves appropriately with multiplicative inverses

The second axis is the strictness:

* WeakCones contain the unit element.  They generalize nonnegativity, and
  the relation R behaves like (≤).

* StrictCones do not contain the unit.  They generalize positivity, and
  the relation R behaves like (<).

The third axis is totality:

* TotalCones require that every element is either in the cone or its negation.
  The corrseponding relation will be a total order.

These replationships between cone properties and relation properties are proved
in theory.cones.

*)

Require Import
  Coq.Classes.Morphisms
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.orders.

(** Operational typeclasses ***************************************************)
Class IsNonNeg A := is_nonneg : A -> Prop.
Class IsPos    A := is_pos    : A -> Prop.

Section PositivityAndOrders.

Context `{Group A}.

Definition cone_relation (cone_contains : A -> Prop) : relation A :=
  λ x y, cone_contains (y & (- x)).

Definition relation_cone (compare : relation A) : A -> Prop :=
  λ x, compare mon_unit x.

Definition flipped_cone (cone_contains : A -> Prop) : A -> Prop :=
  λ x, ¬ cone_contains (-x).

Instance cone_rel_is_le   `{IsNonNeg A} : Le A := cone_relation is_nonneg.
Instance cone_rel_is_lt   `{IsPos    A} : Lt A := cone_relation is_pos.
Instance pos_from_nonneg  `{IsNonNeg A} : IsPos A := flipped_cone is_nonneg.
Instance nonneg_from_pos  `{IsPos    A} : IsNonNeg A := flipped_cone is_pos.
Instance rel_cone_is_nneg `{Le A} : IsNonNeg A := relation_cone le.
Instance rel_cone_is_pos  `{Lt A} : IsPos A    := relation_cone lt.

End PositivityAndOrders.

Instance: Params (@cone_relation) 3 := {}.
Instance: Params (@relation_cone) 2 := {}.

(** Cones for group-like objects **********************************************)
Section GroupCones.

Context `{Equiv A} `{SgOp A}.

Class SemiGroupCone (cone_contains : A -> Prop) :=
  { sgcone_sg     :  SemiGroup A
  ; sgcone_proper :> Proper ((=) ==> iff) cone_contains
  ; sgcone_sgop   :  ∀ x y : A, cone_contains x -> cone_contains y -> cone_contains (x & y)
  }.

Context  `{MonUnit A} `{Negate A}.

Class GroupCone (cone_contains : A -> Prop) :=
  { gcone_group  :  Group A
  ; gcone_sgcone :> SemiGroupCone cone_contains
  ; gcone_both   :  ∀ x : A, cone_contains x -> cone_contains (-x) -> x = mon_unit
  }.

End GroupCones.

(** Cones for ring-like objects ***********************************************)
Section RingCones.

Context `{Aeq: Equiv A} `{Plus A} `{Mult A} `{Zero A} `{One A}.

Class SemiRingCone (cone_contains : A -> Prop) :=
  { srcone_sr        :  SemiRing A
  ; srcone_plus_cone :> @SemiGroupCone A Aeq plus_is_sg_op cone_contains
  ; srcone_mult_cone :> @SemiGroupCone A Aeq mult_is_sg_op cone_contains
  }.

Context `{Negate A}.

Class RingCone (cone_contains : A -> Prop) :=
  { rcone_srcone :> SemiRingCone cone_contains
  ; rcone_gcone  :> @GroupCone A Aeq plus_is_sg_op zero_is_mon_unit negate cone_contains
  ; rcone_ring   : Ring A
  }.

Context `{DecRecip A}.

Class FieldCone (cone_contains : A -> Prop) :=
  { fcone_rcone :> RingCone cone_contains
  ; fcone_field :  DecField A
  ; fcone_recip :  ∀ x : A, x ≠ 0 -> cone_contains x -> cone_contains (/ x)
  }.

End RingCones.

(** Properties of cones *******************************************************)
Section ConeProperties.

Context `{Group A}.

(* strict cones yield strict partial orders (e.g. <) *)
Class StrictCone (cone_contains : A -> Prop) :=
  { scone_cone   :> GroupCone cone_contains
  ; scone_strict : ¬ cone_contains mon_unit
  }.

(* weak cones yield weak partial orders (e.g. ≤) *)
Class WeakCone (cone_contains : A -> Prop) :=
  { wcone_cone :> GroupCone cone_contains
  ; wcone_weak :  cone_contains mon_unit
  }.

(* total cones yield total orders *)
Class TotalCone (cone_contains : A -> Prop) :=
  { tcone_cone  :> GroupCone cone_contains
  ; tcone_total :  ∀ x : A, cone_contains x \/ cone_contains (- x) \/ x = mon_unit
  }.

End ConeProperties.

