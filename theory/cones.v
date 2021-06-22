Require Import
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.orders
  MathClasses.interfaces.cones
  MathClasses.misc.group_automation.

(**
 * Given a cone on A, we can form a relation R on A.  This generalizes the
 * relationship between positivity and ordering.
 *
 * We show various corrsepondences between order properties and cone properties.
 *)
Section ConeOrders.

Context `{Group A} `{!SemiGroupCone cone_contains}.

Local Infix "~" := (cone_relation cone_contains) (at level 70, no associativity).
Local Notation "(~)" := (cone_relation cone_contains).

Lemma cone_rel_compat_right : ∀ x y z, x ~ y -> x & z ~ y & z.
Proof. intros; unfold cone_relation; group_simplify; easy. Qed.

(* TODO: is this the proper use of Proper? *)
Instance: ∀ z, Proper ((~) ==> (~)) (& z).
Proof. intros. red. red. intros. apply cone_rel_compat_right. assumption. Qed.

Instance: Proper ((=) ==> (=) ==> iff) (~).
Proof. unfold cone_relation; repeat red; intros x1 y1 eq1 x2 y2 eq2; rewrite eq1, eq2; easy. Qed.

Instance: Transitive (~).
Proof.
  repeat red; intros; unfold cone_relation;
  setoid_replace (z & -x) with ((z & -y) & (y & -x)) by group;
  apply sgcone_sgop; easy.
Qed.

Context `{!GroupCone cone_contains}.

Instance : AntiSymmetric (~).
Proof. red. intros; unfold cone_relation in *.
assert (x & -y = mon_unit) as eq_unit.
  apply gcone_both; try setoid_replace (- (x & -y)) with (y & -x) by group; easy.
setoid_replace y with (mon_unit & y) by group; rewrite <- eq_unit; group.
Qed.

Section WeakOrder.
Context `{!WeakCone cone_contains}.

Instance le_cone: Le A := (~).

Instance : Reflexive (≤).
Proof. repeat red; intros; group_simplify; exact wcone_weak. Qed.

Instance : PartialOrder (≤).
Proof. repeat (split; try apply _). Qed.

Context `{!TotalCone cone_contains}.

Instance: TotalRelation (≤).
Proof. repeat red; intros.
unfold le, le_cone, cone_relation. setoid_replace (y & -x) with (-(x & -y)) by group.
  destruct (tcone_total (x & -y)) as [pos | [nonneg | unit]]; auto.
    rewrite unit; right. exact wcone_weak.
Qed.

End WeakOrder.

Section StrictOrder.
Context `{!StrictCone cone_contains}.

Instance lt_cone: Lt A := (~).

Instance : Irreflexive (<).
Proof. repeat red; intros x equiv;
  apply scone_strict;
  unfold lt, lt_cone, cone_relation in equiv;
  rewrite right_inverse in equiv;
  assumption.
  Qed.

Instance: StrictSetoidOrder (<).
Proof. repeat (split; try apply _). Qed.

End StrictOrder.

End ConeOrders.
