Require Import
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.orders MathClasses.orders.rings
  MathClasses.interfaces.cones
  MathClasses.theory.groups
  MathClasses.theory.strong_setoids
  MathClasses.theory.rings Coq.setoid_ring.Ring
  MathClasses.misc.group_automation.

(**
 * The relation R induced by a SemiGroupCone C is transitive;
 * if C is also a GroupCone then R is antisymmetric.
 *)
Section relation_from_cone.
  Context `{Group A} `{!SemiGroupCone cone_contains}.

  Local Infix "⊏" := (cone_relation cone_contains) (at level 70, no associativity).
  Local Notation "(⊏)" := (cone_relation cone_contains).

  Lemma cone_rel_compat_right : ∀ x y z, x ⊏ y -> x & z ⊏ y & z.
  Proof. intros; unfold cone_relation; group_simplify; easy. Qed.

  Lemma cone_rel_compat_left `{!AbGroup A}: ∀ x y z, x ⊏ y -> z & x ⊏ z & y.
  Proof. intros; unfold cone_relation; repeat rewrite (commutativity z); group_simplify; easy. Qed.

  (* TODO: is this the proper use of Proper? *)
  Global Instance: ∀ z, Proper ((⊏) ==> (⊏)) (& z).
  Proof. intros. red. red. intros. apply cone_rel_compat_right. assumption. Qed.

  Global Instance: Proper ((=) ==> (=) ==> iff) (⊏).
  Proof. unfold cone_relation; repeat red; intros x1 y1 eq1 x2 y2 eq2; rewrite eq1, eq2; easy. Qed.

  Global Instance: Transitive (⊏).
  Proof.
    repeat red; intros; unfold cone_relation;
    setoid_replace (z & -x) with ((z & -y) & (y & -x)) by group;
    apply sgcone_sgop; easy.
  Qed.

  Context `{!GroupCone cone_contains}.

  Global Instance: AntiSymmetric (⊏).
  Proof. red. intros; unfold cone_relation in *.
  assert (x & -y = mon_unit) as eq_unit.
    apply gcone_both; try setoid_replace (- (x & -y)) with (y & -x) by group; easy.
  setoid_replace y with (mon_unit & y) by group; rewrite <- eq_unit; group.
  Qed.

  Context `{!TotalCone cone_contains}.

  Global Instance : Trichotomy (⊏).
  Proof. red. unfold cone_relation; intros.
    setoid_replace (y & -x) with (-(x & -y)) by group.
    destruct (tcone_total (x & -y)) as [lt | [gt | eq]].
      right; right; assumption.
      left; assumption.
      right; left; setoid_replace y with (mon_unit & y) by group; rewrite <- eq; group.
  Qed.

End relation_from_cone.

(** We can use < to define ≤ and vice-versa ***********************************)
Section strict_cone_from_weak.

  Context `{Group A} `{!SemiGroupCone cone} `{!TotalCone cone}.

  Instance flip_group `{!GroupCone cone} : GroupCone (flipped_cone cone).
  Proof.  repeat (split; try apply _).
    unfold flipped_cone. rewrite H0; auto.
    unfold flipped_cone. rewrite H0; auto.
    unfold flipped_cone. unfold not. intros.
      destruct (tcone_total x) as [pos | [ neg | zer ]].
        apply H1. setoid_replace (-y) with (-(x & y) & x) by group. apply sgcone_sgop; assumption.
        apply H0; assumption.
        rewrite zer in H2. apply H1. setoid_replace (-y) with (- (mon_unit & y)) by group; assumption.
    unfold flipped_cone. intro x. setoid_replace (- - x) with x by group. unfold not. intros.
        destruct (tcone_total (x)) as [pos | [ neg | zer ]].
            contradiction.
            contradiction.
            easy.
  Qed.

End strict_cone_from_weak.

(*******************************************************************************
 * The relation R induced by a weak group cone C is a partial order.
 * If C is total then so is R.
 *)
Section le_from_nonneg.
  Context `{Group A}
          `{!GroupCone cone} `{!WeakCone cone}.

  Local Notation "(≤)" := (cone_relation cone).

  Global Instance : Reflexive (≤).
  Proof. repeat red; intros; group_simplify; exact wcone_weak. Qed.

  Global Instance cone_le_is_po : PartialOrder (≤).
  Proof. repeat (split; try apply _). Qed.

  Context `{!TotalCone cone}.

  Global Instance : TotalRelation (≤).
  Proof. repeat red; intros.
    destruct (trichotomy (≤) x y) as [leq | [eq | geq]].
      left; assumption.
      left; rewrite eq; reflexivity.
      right; assumption.
  Qed.
End le_from_nonneg.


(*******************************************************************************
 * The relation R induced by a strict group cone C is a strict order.
 * If C is decidable and total, then so is R.
 *)
Section lt_from_pos.
  Context `{Group A}
          `{!GroupCone cone} `{!StrictCone cone}.

  Local Notation "(<)" := (cone_relation cone).

  Global Instance : Irreflexive (<).
  Proof. repeat red; intros x equiv;
    apply scone_strict;
    unfold lt, cone_relation in equiv;
    rewrite right_inverse in equiv;
    assumption.
    Qed.

  Global Instance: StrictSetoidOrder (<).
  Proof. repeat (split; try apply _). Qed.

  Context `{!TotalCone cone}.

  Global Instance: CoTransitive (<).
  Proof. red. intros.
    destruct (trichotomy (<) x z) as [lt | [ eq | gt ] ].
      left; assumption.
      right; rewrite <- eq; assumption.
      right; transitivity x; assumption.
  Qed.

  Context `{∀ x y, Decision (x = y)}.
  Global Instance: PseudoOrder (<).
  Proof. split. apply dec_strong_setoid.
    intros x y lts. unfold lt, cone_relation in *;
      apply scone_strict; setoid_replace mon_unit with ((y & -x) & (x & -y)) by group. apply sgcone_sgop; easy.
    apply _.
    split.
      intro apart. destruct (trichotomy (<) x y) as [lt | [ eq | gt ]].
        left; assumption.
        contradiction.
        right; assumption.
    intros ineq; destruct ineq as [ineq | ineq];
      intros eq; apply scone_strict; rewrite eq in ineq;
      repeat red in ineq; rewrite right_inverse in ineq; assumption.
    Qed.

End lt_from_pos.

(*******************************************************************************
 * The relation R induced by a ring cone C is a ring order.
 *)

Section rcone_closed.
  Local Existing Instance plus_is_sg_op | 0.
  Context `{Ring A} `{!RingCone cone}.
  Add Ring R : (stdlib_ring_theory A).

  Local Infix "⊏" := (cone_relation cone) (at level 70, no associativity).
  Local Notation "(⊏)" := (cone_relation cone).

  Lemma subtract_zero : ∀ x, x - 0 = x.
  Proof. intros. ring. Qed.

  Lemma mult_spec : ∀ x y, PropHolds (0 ⊏ x) -> PropHolds (0 ⊏ y) -> PropHolds (0 ⊏ x * y).
  Proof. unfold PropHolds; unfold cone_relation, sg_op, plus_is_sg_op; fold plus;
    intros; rewrite subtract_zero in *; apply sgcone_sgop; assumption.
  Qed.

End rcone_closed.

Section ring_order_from_rcone.
  Local Existing Instance plus_is_sg_op | 0.
  Context `{Ring A} `{!WeakCone cone} `{!RingCone cone}.

  (*
  Local Instance: IsNonNeg A := cone.
  *)
  Local Instance : Le A := cone_relation cone.
  
  Lemma weak_plus_spec: ∀ z, OrderPreserving (z +).
  Proof. repeat (split; try apply _); intros. apply cone_rel_compat_left. easy. Qed.

  Global Instance: SemiRingOrder (≤).
  Proof. apply from_ring_order. apply weak_plus_spec. apply mult_spec. Qed.

End ring_order_from_rcone.

Section strict_ring_order_from_rcone.
  Local Existing Instance plus_is_sg_op | 0.
  Context `{Ring A} `{!StrictCone cone} `{!RingCone cone}.
  Add Ring R : (stdlib_ring_theory A).

  Local Existing Instance strict_cone_is_lt | 0.

  Local Lemma strict_plus_spec : ∀ z, StrictlyOrderPreserving (z +).
  Proof. repeat (split; try apply _); intros;  apply cone_rel_compat_left; easy. Qed.

  Lemma from_strict_ring_order: StrictSemiRingOrder (<).
  Proof. apply from_strict_ring_order. apply strict_plus_spec. apply mult_spec. Qed.

  Context `{!TotalCone cone}.

  Global Instance: NoZeroDivisors A.
  Proof. intros x xzd; destruct xzd as [xnonzero [y [ynonzero xyzero]]];
    destruct (tcone_total x) as [xpos | [xneg | xzero]];
    destruct (tcone_total y) as [ypos | [yneg | yzero]];
    apply scone_strict; try contradiction; change (cone 0).
    all: match goal with
      | [ _ : cone ?a , _ : cone ?b |- _ ] => setoid_replace 0 with (a * b); try (apply sgcone_sgop; assumption)
    end.
    all: (idtac + rewrite <- negate_mon_unit); rewrite <- xyzero; ring.
  Qed.

End strict_ring_order_from_rcone.

(** Deriving cones from orders ************************************************)

(* TODO *)

(** Results about ordered rings ***********************************************)
Section theory.
  Local Existing Instance plus_is_sg_op | 0.
  Context `{Ring A} `{!RingCone cone} `{!WeakCone cone} `{!TotalCone cone}.

End theory.

