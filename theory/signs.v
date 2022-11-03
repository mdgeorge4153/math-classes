Require Import
    MathClasses.interfaces.abstract_algebra
    MathClasses.interfaces.orders MathClasses.orders.rings
    MathClasses.interfaces.signs
    MathClasses.theory.groups
    MathClasses.theory.strong_setoids
    MathClasses.theory.rings Coq.setoid_ring.Ring
    MathClasses.misc.group_automation.

(*
Section relation_from_positivity.

Context `{PositiveGroup A}.

#[global]
Instance positivity_is_lt : Lt A := λ x y, positive (y & (-x)).

#[global]
Instance: Transitive (<).
Proof. unfold lt, positivity_is_lt; intros x y z;
    setoid_replace (z & -x) with ((z & -y) & (y & -x)) by group;
    intros; apply psg_sgop; easy.
Qed.

#[global]
Instance: AntiSymmetric (<).
Proof. unfold lt, positivity_is_lt; intros x y;
    setoid_replace (x & -y) with (- (y & -x)) by group;
    intros; exfalso; apply (pg_flip (y & -x)); easy.
Qed.

#[global]
Instance: Irreflexive (<).
Proof. repeat red; unfold lt, positivity_is_lt; intros x;
    setoid_replace (x & -x) with mon_unit by group; apply pg_unit.
Qed.

End relation_from_positivity.
*)

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
    unfold lt, lt_from_sign; group_simplify; rewrite signedgroup_unit; easy. Qed.

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
    rewrite signedgroup_negate. unfold flip. destruct (sign (x & -y)); auto. Qed.

End relation_from_signed.
(* 
#[global]
Instance: Trichotomy (<).
Proof. repeat red; unfold lt, positivity_is_lt, positive, sign_is_positivity;
    intros x y.
    setoid_replace (x & -y) with (- (y & -x)) by group.
    destruct (sign (y & -x)) eqn:sign; rewrite signedg_flip; rewrite sign; simpl;
    match goal with
        | [ |- context[?x = ?x] ] => auto
        | [ _ : ?e ≡ zer |- context[x = y] ] => enough (x = y) by auto; apply signedg_zero in sign; symmetry; group
    end.
Qed.

#[global]
Instance: Proper ((=) ==> (=) ==> iff) (<).
Proof. repeat red; intros x1 y1 eq1 x2 y2 eq2;
    unfold lt, positivity_is_lt, positive, sign_is_positivity;
    rewrite eq1, eq2; easy.
    Qed.

#[global]
Instance: StrictSetoidOrder (<).
Proof. repeat (split; try apply _). Qed.

#[global]
Instance: @CoTransitive A lt. (* TODO: without A, it is defaulting to nat *)
Proof. repeat red. intros. destruct (trichotomy (<) x z) as [lt | [ eq | gt ]].
    left; assumption.
    right; rewrite <- eq; assumption.
    right; transitivity x; assumption.
    Qed.

(*
Context `{∀ x y, Decision (x = y)}.

#[global]
Instance: PseudoOrder (<).
Proof. split.
    apply dec_strong_setoid.
    unfold lt, positivity_is_lt; intros x y lts; unfold lt, positivity_is_lt;
        apply (pg_flip (y & -x)); try setoid_replace (- (y & -x)) with (x & -y) by group; easy.
    apply _.
    split. intro apart.

*)
End relation_from_signed.
*)
