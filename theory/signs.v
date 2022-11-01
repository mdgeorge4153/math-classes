Require Import
    MathClasses.interfaces.abstract_algebra
    MathClasses.interfaces.orders MathClasses.orders.rings
    MathClasses.interfaces.signs
    MathClasses.theory.groups
    MathClasses.theory.strong_setoids
    MathClasses.theory.rings Coq.setoid_ring.Ring
    MathClasses.misc.group_automation.

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

Section relation_from_signed.

Context `{SignedGroup A}.

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

Context `{∀ x y, Decision (x = y)}.

#[global]
Instance: PseudoOrder (<).
Proof. split.
    apply dec_strong_setoid.
    unfold lt, positivity_is_lt; intros x y lts; unfold lt, positivity_is_lt;
        apply (pg_flip (y & -x)); try setoid_replace (- (y & -x)) with (x & -y) by group; easy.
    apply _.
    split. intro apart.


End relation_from_signed.
