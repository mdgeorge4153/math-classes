Require Import
  MathClasses.interfaces.abstract_algebra.

(** Operational typeclasses ***************************************************)

Inductive Sign := pos | neg | zer.
Class Signed A := sign : A -> Sign.

#[global]
Instance: Equiv Sign := (≡).

Instance sign_flip: Negate Sign := λ s, match s with
    | pos => neg | neg => pos | zer => zer
end.

(** Semigroup positivity ******************************************************)
Section Groups.

Context `{Equiv A} `{SgOp A} `{MonUnit A} `{Negate A} `{Signed A}.

Class SignedGroup :=
    { signedgroup_group    :> Group A
    ; signedgroup_sgop     :  ∀ x y, sign x = pos -> sign y = pos -> sign (x & y) = pos
    ; signedgroup_proper   :> Proper ((=) ==> (=)) sign
    ; signedgroup_swap     :  ∀ x y, sign (x & y) = sign (y & x)
    ; signedgroup_unit     :  sign mon_unit = zer
    ; signedgroup_negate   :  ∀ x, sign (-x) = - (sign x)
    }.

End Groups.

(*

Class PositiveSemiGroup `{Positive A} :=
    { psg_sg     :> SemiGroup A
    ; psg_proper :> Proper ((=) ==> iff) positive
    ; psg_sgop   :  ∀ x y : A, positive x -> positive y -> positive (x & y)
    ; psg_flip   :  ∀ x y : A, positive (x & y) -> positive (y & x)
    }.

Context `{MonUnit A} `{Negate A}.

Class PositiveGroup `{Positive A} :=
    { pg_pg    :> PositiveSemiGroup
    ; pg_group :> Group A
    ; pg_flip  :  ∀ x : A, positive x -> positive (-x) -> False
    ; pg_unit  :  ¬ positive mon_unit
    }.

Class SignedGroup `{Signed A} :=
    { signedg_pg     :> PositiveGroup
    ; signedg_proper :> Proper ((=) ==> (=)) sign
    ; signedg_flip   :  ∀ x : A, sign (-x) = flip (sign x)
    ; signedg_zero   :  ∀ x : A, sign x = zer -> x = mon_unit
    }.

End Groups.

Section Rings.

Context `{Equiv A} `{Plus A} `{Mult A} `{Zero A} `{One A} `{Negate A}.
Context `{Signed A}.

Class SignedRing :=
    { signedr_r         :> Ring A
    ; signedr_signedg   :> PositiveGroup
    ; signedsr_mult_pos :> @PositiveSemiGroup _ _ mult_is_sg_op _
    }.

Context `{DecRecip A}.

Class SignedField :=
    { signedf_f       :> DecField A
    ; signedf_signedr :> SignedRing
    ; signedf_recip   :  ∀ x : A, sign (/ x) = sign x
    }.

End Rings.

*)
