Require Import
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.orders
  MathClasses.interfaces.cones
  MathClasses.theory.strong_setoids
  MathClasses.misc.group_automation.

(**
 * The relation R induced by a SemiGroupCone C is transitive;
 * if C is also a GroupCone then R is antisymmetric.
 *)
Section relation_from_cone.
  Context `{Group A} `{!SemiGroupCone cone_contains}.

  Local Infix "~" := (cone_relation cone_contains) (at level 70, no associativity).
  Local Notation "(~)" := (cone_relation cone_contains).

  Lemma cone_rel_compat_right : ∀ x y z, x ~ y -> x & z ~ y & z.
  Proof. intros; unfold cone_relation; group_simplify; easy. Qed.

  (* TODO: is this the proper use of Proper? *)
  Global Instance: ∀ z, Proper ((~) ==> (~)) (& z).
  Proof. intros. red. red. intros. apply cone_rel_compat_right. assumption. Qed.

  Global Instance: Proper ((=) ==> (=) ==> iff) (~).
  Proof. unfold cone_relation; repeat red; intros x1 y1 eq1 x2 y2 eq2; rewrite eq1, eq2; easy. Qed.

  Global Instance: Transitive (~).
  Proof.
    repeat red; intros; unfold cone_relation;
    setoid_replace (z & -x) with ((z & -y) & (y & -x)) by group;
    apply sgcone_sgop; easy.
  Qed.

  Context `{!GroupCone cone_contains}.

  Global Instance: AntiSymmetric (~).
  Proof. red. intros; unfold cone_relation in *.
  assert (x & -y = mon_unit) as eq_unit.
    apply gcone_both; try setoid_replace (- (x & -y)) with (y & -x) by group; easy.
  setoid_replace y with (mon_unit & y) by group; rewrite <- eq_unit; group.
  Qed.
End relation_from_cone.

(*******************************************************************************
 * The relation R induced by a weak group cone C is a partial order.
 * If C is total then so is R.
 *)
Section le_from_nonneg.
  Context `{Group A}
          `{!GroupCone cone} `{!WeakCone cone}.

  Local Instance: IsNonNeg A := cone.
  Local Existing Instance cone_rel_is_le | 0.

  Global Instance : Reflexive (≤).
  Proof. repeat red; fold is_nonneg; intros; group_simplify; exact wcone_weak. Qed.

  Global Instance cone_le_is_po : PartialOrder (≤).
  Proof. repeat (split; try apply _). Qed.

  Context `{!TotalCone is_nonneg}.

  Global Instance : TotalRelation (≤).
  Proof. repeat red; intros.
  unfold le, cone_rel_is_le, cone_relation. setoid_replace (y & -x) with (-(x & -y)) by group.
    destruct (tcone_total (x & -y)) as [pos | [nonneg | unit]]; auto.
      rewrite unit; right. exact wcone_weak.
  Qed.
End le_from_nonneg.


(*******************************************************************************
 * The relation R induced by a strict group cone C is a strict order.
 * If C is decidable and total, then so is R.
 *)
Section lt_from_pos.
  Context `{Group A}
          `{!GroupCone cone} `{!StrictCone cone}.

  Local Instance: IsPos A := cone.
  Local Existing Instance cone_rel_is_lt | 0.

  Global Instance : Irreflexive (<).
  Proof. repeat red; intros x equiv;
    apply scone_strict;
    unfold lt, cone_rel_is_lt, cone_relation in equiv;
    rewrite right_inverse in equiv;
    assumption.
    Qed.

  Global Instance: StrictSetoidOrder (<).
  Proof. repeat (split; try apply _). Qed.

  Context `{!TotalCone is_pos} `{∀ x y, Decision (x = y)}.

  Global Instance: Trichotomy (<).
  Proof.
    red. unfold lt, cone_rel_is_lt, cone_relation; intros.
    setoid_replace (y & -x) with (-(x & -y)) by group.
    destruct (tcone_total (x & -y)) as [lt | [gt | eq]].
      right; right; assumption.
      left; assumption.
      right; left; setoid_replace y with (mon_unit & y) by group; rewrite <- eq; group.
  Qed.

  Global Instance: CoTransitive (<).
  Proof. red. intros.
    destruct (trichotomy (<) x z) as [lt | [ eq | gt ] ];
      [ left; assumption
      | right; rewrite <- eq; assumption
      | right; transitivity x; assumption
      ].
  Qed.

  Global Instance: PseudoOrder (<).
  Proof. split. apply dec_strong_setoid.
    intros x y lts; unfold lt, cone_rel_is_lt, cone_relation in *;
      apply scone_strict; setoid_replace mon_unit with ((y & -x) & (x & -y)) by group. apply sgcone_sgop; easy.
    apply _.
    split.
      intro apart. destruct (trichotomy (<) x y) as [lt | [ eq | gt ]].
        left; assumption.
        contradiction.
        right; assumption.
    intros ineq. destruct ineq as [lt | gt].
    repeat red. intros eq. rewrite eq in lt. apply scone_strict. repeat red in lt. fold is_pos in lt. rewrite right_inverse in lt. assumption.
    repeat red. intros eq. rewrite eq in gt. apply scone_strict. repeat red in gt. fold is_pos in gt. rewrite right_inverse in gt. assumption.
    Qed.

End lt_from_pos.

(*******************************************************************************
 * The relation R induced by a ring cone C is a ring order.
 *)
(*
Section ring_order_from_rcone.
  Context `{Ring A} `{!RingCone cone} `{!WeakCone cone}.

  Local Instance: IsNonNeg A := cone.
  Local Existing Instance cone_rel_is_le | 0.
  
  Lemma plus_spec: ∀ z, OrderPreserving (z +).
  Proof. intros. split. split. apply _. Print Instances PartialOrder. split. apply _. unfold le. apply _. apply _.

Instance: 
End RingConeOrders.

Section OrderCones.

End OrderCones.
*)
