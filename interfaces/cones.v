(*
This file gives an alternative characterization of ring orderings based on positive
cones.
*)

Require Import
  MathClasses.interfaces.abstract_algebra
  MathClasses.misc.group_automation.


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
(*  ; sgcone_flip   : ∀ x y : A, cone_contains (x & y) -> cone_contains (y & x)*)
  }.

Context  `{MonUnit A} `{Negate A}.

Class GroupCone (cone_contains : A -> Prop) :=
  { gcone_group : Group A
  ; gcone_both  : ∀ x : A, cone_contains x -> cone_contains (-x) -> x = mon_unit
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
Notation "(~)" := (cone_relation cone_contains).

Lemma cone_rel_compat_right : ∀ x y z, x ~ y -> x & z ~ y & z.
Proof. intros; unfold cone_relation; group_simplify; easy. Qed.

(*
Lemma cone_rel_compat_left : ∀ x y z, x ~ y -> z & x ~ z & y.
Proof. intros; unfold cone_relation;
  apply sgcone_flip; group_simplify; apply sgcone_flip. easy. Qed.
*)

Instance: Transitive (~).
Proof.
  repeat red; intros; unfold cone_relation;
  setoid_replace (z & -x) with ((z & -y) & (y & -x)) by group;
  apply sgcone_sgop; easy.
Qed.

Context `{!GroupCone cone_contains}.

Instance : Antisymmetric A (=) (~).
Proof. red. intros; unfold cone_relation in *.
assert (x & -y = mon_unit) as eq_unit.
  apply gcone_both; try setoid_replace (- (x & -y)) with (y & -x) by group; easy.
setoid_replace y with (mon_unit & y) by group; rewrite <- eq_unit; group.
Qed.

Section WeakOrder.
Context `{!WeakCone cone_contains}.

Instance : Reflexive (~).
Proof. repeat red; intros; group_simplify; exact wcone_weak. Qed.

Instance : PreOrder (~).
Proof. repeat (split; try apply _). Qed.

Instance : PartialOrder (=) (~).
Proof. split.
  intro xeq; repeat red; split; repeat red; rewrite xeq; group_simplify; exact wcone_weak.
  intro xeq; repeat red in xeq; destruct xeq as [xrel xrelflip]. red in xrel; repeat red in xrelflip.
  setoid_replace (x & -x0) with (-(x0 & -x)) in xrelflip by group.
  apply symmetry. group. apply gcone_both; easy.
  Qed.

End WeakOrder.

End ConeOrders.
