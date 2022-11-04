Require Import
  MathClasses.interfaces.abstract_algebra.

(** Operational typeclasses ***************************************************)

Inductive Sign := pos | neg | zer.
Class Signed A := sign : A -> Sign.

(** Signs form a commutative monoid *******************************************)

Global Instance: Equiv Sign := (≡).

Global Instance sign_flip:
    Negate Sign := λ s, match s with | pos => neg | neg => pos | zer => zer end.

Global Instance sign_mult:
    Mult Sign := λ s1 s2, match s1 with | pos => s2 | neg => -s2 | zer => zer end.

Global Instance: Zero Sign := zer.
Global Instance: One Sign := pos.

Local Existing Instance one_is_mon_unit | 0.
Local Existing Instance mult_is_sg_op | 0.

Global Instance: CommutativeMonoid Sign.
Proof. repeat (split; try apply _).
    intros x y z; destruct x,y,z; easy.
    intros x; destruct x; easy.
    intros x y; destruct x, y; easy.
    Qed.

(** Signed groups and rings ***************************************************)

Section signed_structures.

Context `{Equiv A} `{Signed A} `{Negate A}.

Class SignedGroup `{SgOp A} `{MonUnit A} :=
    { signedgroup_group    :> Group A
    ; signedgroup_sgop     :  ∀ x y, sign x = pos -> sign y = pos -> sign (x & y) = pos
    ; signedgroup_proper   :> Proper ((=) ==> (=)) sign
    ; signedgroup_swap     :  ∀ x y, sign (x & y) = sign (y & x)
    ; signedgroup_unit     :  sign mon_unit = 0
    ; signedgroup_negate   :  ∀ x, sign (-x) = - (sign x)
    }.

Context `{Plus A} `{Mult A} `{Zero A} `{One A}.

Class SignedRing :=
    { signedring_ring     :> Ring A
    ; signedring_sgroup   :> @SignedGroup plus_is_sg_op zero_is_mon_unit
    ; signedring_morphism :> @Monoid_Morphism _ _ _ _ one_is_mon_unit _ mult_is_sg_op _ sign
    }.

Context `{DecRecip A}.

Class SignedField :=
    { signedfield_field :> DecField A
    ; signedfield_recip :  ∀ x, sign (/x) = sign x
    }.

End signed_structures.

