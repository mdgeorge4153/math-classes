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
Instance positivity_is_lt: Lt A := λ x y, positive (y & (-x)).

#[global]
Instance: Transitive (<).
Proof. unfold lt, positivity_is_lt; intros x y z;
    setoid_replace (z & -x) with ((z & -y) & (y & -x)) by group;
    intros; apply psg_sgop; easy.
Qed.

End relation_from_positivity.

