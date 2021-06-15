(*
This file gives an alternative characterization of ring orderings based on positive
cones.
*)

Require Import
  MathClasses.interfaces.abstract_algebra
  MathClasses.theory.groups.


(** Operational typeclasses ***************************************************)
Class IsNonNeg A := is_nonneg : A -> Prop.
Class IsPos    A := is_pos    : A -> Prop.

(** Cones for group-like objects **********************************************)
Section GroupCones.

Context `{Equiv A} `{SgOp A}.

(* As suggested by David Feuer: https://math.stackexchange.com/q/293000 *)
Class SemiGroupCone (cone_contains : A -> Prop) :=
  { sgcone_sg     : SemiGroup A
  ; sgcone_proper :> Proper ((=) ==> iff) cone_contains
  ; sgcone_sgop   : ∀ x y : A, cone_contains x -> cone_contains y -> cone_contains (x & y)
  ; sgcone_flip   : ∀ x y : A, cone_contains (x & y) -> cone_contains (y & x)
  }.

Context  `{MonUnit A} `{Negate A}.

Class GroupCone (cone_contains : A -> Prop) :=
  { gcone_group : Group A
  ; gcone_both  : ∀ x y : A, cone_contains x -> cone_contains (-x) -> x = mon_unit
  }.

End GroupCones.

(** Operations for ring-like objects ******************************************)
Section RingCones.

Context `{Aeq: Equiv A} `{Plus A} `{Mult A} `{Zero A} `{One A}.

Class SemiRingCone (cone_contains : A -> Prop) :=
  { srcone_sr        : SemiRing A
  ; srcone_plus_cone : @SemiGroupCone A Aeq plus_is_sg_op cone_contains
  ; srcone_mult_cone : @SemiGroupCone A Aeq mult_is_sg_op cone_contains
  }.

Context `{Negate A}.

Class RingCone (cone_contains : A -> Prop) :=
  { rcone_srcone :> SemiRingCone cone_contains
  ; rcone_ring   : Ring A
  ; rcone_mult   : ∀ x y : A, cone_contains x -> cone_contains y -> cone_contains (x * y)
  }.

Context `{DecRecip A}.

Class FieldCone (cone_contains : A -> Prop) :=
  { fcone_rcone :> RingCone cone_contains
  ; fcone_field :  DecField A
  ; fcone_recip :  ∀ x : A, x ≠ 0 -> cone_contains x -> cone_contains (/ x)
  }.

End RingCones.

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

(**
 * Given a cone on A, we can form a relation R on A.  This generalizes the
 * relationship between positivity and ordering.
 *
 * We show various corrsepondences between order properties and cone properties.
 *)
Section ConeOrders.

Context `{Group A}.

Definition cone_relation (cone_contains : A -> Prop) : relation A :=
  λ x y, cone_contains (y & (- x)).

Definition relation_cone (compare : relation A) : A -> Prop :=
  λ x, compare mon_unit x.

Context `{!SemiGroupCone cone_contains}.

Infix "~" := (cone_relation cone_contains) (at level 70, no associativity).

Lemma cone_rel_compat_left : ∀ x y z, x ~ y -> z & x ~ z & y.
Proof. (* intros. unfold cone_relation in *.
  apply sgcone_flip.
  apply (sgcone_proper (-x & y) (- (z & x) & (z & y))).  group. *)
  admit.  Admitted.

End ConeOrders.

