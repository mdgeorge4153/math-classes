Require Import
  MathClasses.interfaces.abstract_algebra.

(** Operational typeclasses ***************************************************)

Class Positive A := positive : A -> Prop.
Class Negative A := negative : A -> Prop.

Inductive Sign := pos | neg | zer.
Class Signed A := sign : A -> Sign.

#[global]
Instance: Equiv Sign := (≡).

Definition flip (s : Sign) : Sign := match s with
    | pos => neg | neg => pos | zer => zer
end.

#[global]
Instance sign_is_positivity `{Signed A} : Positive A := λ x, sign x = pos.

#[global]
Instance sign_is_negativity `{Signed A} : Negative A := λ x, sign x = neg.

(** Semigroup positivity ******************************************************)
Section Groups.

Context `{Equiv A} `{SgOp A} `{Positive A}.

Class PositiveSemiGroup :=
    { psg_sg     :> SemiGroup A
    ; psg_proper :> Proper ((=) ==> iff) positive
    ; psg_sgop   :  ∀ x y : A, positive x -> positive y -> positive (x & y)
    ; psg_flip   :  ∀ x y : A, positive (x & y) -> positive (y & x)
    }.

Context `{MonUnit A} `{Negate A}.

Class PositiveGroup :=
    { pg_pg    :> PositiveSemiGroup
    ; pg_group :> Group A
    ; pg_flip  :  ∀ x : A, positive x -> positive (-x) -> False
    ; pg_unit  :  ¬ positive mon_unit
    }.

End Groups.

Section Rings.

Context `{Equiv A} `{Plus A} `{Mult A} `{Zero A} `{One A} `{Negate A}.
Context `{Signed A}.

Class SignedRing :=
    { signedr_r         :> Ring A
    ; signedr_signedg   :> @PositiveGroup     _ _ plus_is_sg_op _ _ _
    ; signedsr_mult_pos :> @PositiveSemiGroup _ _ mult_is_sg_op _
    }.

Context `{DecRecip A}.

Class SignedField :=
    { signedf_f       :> DecField A
    ; signedf_signedr :> SignedRing
    ; signedf_recip   :  ∀ x : A, sign (/ x) = sign x
    }.

End Rings.

