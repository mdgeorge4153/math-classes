Require Import
    MathClasses.interfaces.abstract_algebra
    MathClasses.interfaces.orders MathClasses.orders.rings
    MathClasses.interfaces.signs
    MathClasses.theory.groups
    MathClasses.theory.strong_setoids
    MathClasses.theory.rings Coq.setoid_ring.Ring
    MathClasses.misc.group_automation.

Section relation_from_positivity.

Context `{Group A}.

#[global]
Instance positivity_is_le `{Positive A}: Le A := λ x y, positive (y & (-x)).

End relation_from_positivity.
