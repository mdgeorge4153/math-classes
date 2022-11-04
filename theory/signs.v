Require Import
    MathClasses.interfaces.abstract_algebra
    MathClasses.interfaces.orders MathClasses.orders.rings
    MathClasses.interfaces.signs
    MathClasses.theory.groups
    MathClasses.theory.strong_setoids
    MathClasses.theory.rings Coq.setoid_ring.Ring
    MathClasses.misc.group_automation.

Section definitions.

Context `{Equiv A} `{Signed A} `{SgOp A} `{Negate A}.

#[global]
Instance lt_from_sign:
    Lt A := λ x y, sign (y & - x) = pos.

#[global]
Instance le_from_sign:
    Le A := λ x y, sign (y & -x) = pos ∨ sign (y & -x) = zer.

End definitions.

Section relation_from_signed.

Context `{SignedGroup A}.

Existing Instance lt_from_sign | 0.

Instance: Proper ((=) ==> (=) ==> iff) (<).
Proof. intros x1 x2 xeq y1 y2 yeq;
    unfold lt, lt_from_sign; rewrite xeq, yeq; easy.
    Qed.

Instance: Irreflexive (<).
Proof. repeat red; intro x;
    unfold lt, lt_from_sign; group_simplify. rewrite signedgroup_unit; easy. Qed.

Instance: Transitive lt_from_sign.
Proof. intros x y z xlty yltz;
    unfold lt_from_sign in *.
    setoid_replace (z & -x) with ((z & -y) & (y & -x)) by group;
    apply signedgroup_sgop; easy.
    Qed.

Instance: AntiSymmetric lt_from_sign.
Proof. intros x y. unfold lt_from_sign in *.
    setoid_replace (x & -y) with (-(y & - x)) by group.
    rewrite signedgroup_negate. intro s1. rewrite s1. easy. Qed.

Instance: StrictOrder lt_from_sign.
Proof. repeat (split; try apply _). Qed.

Lemma preserve: ∀ z x y: A, x < y → x & z < y & z.
Proof. intros; unfold lt, lt_from_sign in *;
    group_simplify; easy. Qed.

#[global]
Instance: ∀ z : A, StrictlyOrderPreserving (&z).
Proof. repeat (split; try apply _); apply preserve. Qed.

#[global]
Instance: ∀ z : A, StrictlyOrderPreserving (z&).
Proof. repeat (split; try apply _);
    unfold lt, lt_from_sign; intros;
    rewrite signedgroup_swap; group_simplify; rewrite signedgroup_swap; easy.  Qed.

#[global]
Instance: TotalRelation le_from_sign.
Proof. intros x y. unfold le_from_sign.
    setoid_replace (y & -x) with (-(x & -y)) by group;
    rewrite signedgroup_negate; unfold negate, sign_flip; fold negate; destruct (sign (x & -y)); auto. Qed.

End relation_from_signed.

Section ring_relation.

Context `{SignedRing R}.

Lemma nontrivial: 1 ≠ 0.
Proof. intros eq.
    assert (sign 1 = sign 0) as nonsense by (rewrite eq; easy).
    rewrite signedgroup_unit in nonsense.
    rewrite preserves_mon_unit in nonsense.
    easy. Qed.

Lemma not_zerodivisor: ∀ x y, sign (x * y) = 0 → sign x = 0 ∨ sign y = 0.
Proof. intros x y. rewrite preserves_sg_op.
    destruct (sign x), (sign y); auto; easy. Qed.

(*
Instance: NoZeroDivisors R.
Proof. intros x xzd. destruct xzd as [nonzero [y [ynonzero xyzero]]].
    destruct (sign x) eqn:sx, (sign y) eqn:sy.
    assert (sign (x * y) = 0). rewrite xyzero. apply signedgroup_unit.

Instance: IntegralDomain R.
Proof. repeat (split; try apply _).
    apply nontrivial.
    unfold NoZeroDivisors, ZeroDivisor.
*)

End ring_relation.

