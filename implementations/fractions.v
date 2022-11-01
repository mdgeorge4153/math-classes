Require Import 
  Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra 
  MathClasses.theory.rings MathClasses.theory.dec_fields
  MathClasses.interfaces.orders
  MathClasses.interfaces.signs
  MathClasses.misc.group_automation.


(* TODO: I suspect most of this works with a SemiRing, but the proofs rely
 * heavily on the stdlib ring theory.
 *
 * The IntegralDomain is only needed to prove transitivity of (=).
 *)
Context `{IntegralDomain R}.

Add Ring R: (stdlib_ring_theory R).

Class MultiplicativeSet (D : R -> Prop) : Prop :=
    { mset_unit : D 1
    ; mset_mult : ∀ x y, D x -> D y -> D (x * y)
    ; mset_zero : ¬ D 0
    ; mset_proper :> Proper ((=) ==> iff) D
    }.

Context `{MultiplicativeSet D}.


Inductive Frac: Type := frac { num: R; den: R; den_in_D: D den }.

Local Hint Extern 2 (D _) => apply mset_unit : typeclass_instances.
Local Hint Extern 2 (D _) => apply mset_mult : typeclass_instances.
Local Hint Extern 2 (D _) => apply den_in_D  : typeclass_instances.

Obligation Tactic := auto with typeclass_instances.

Global Instance Frac_equiv:
    Equiv Frac | 0 := λ x y, num x * den y = num y * den x.

Global Program Instance Frac_plus:
    Plus Frac := λ x y, frac (num x * den y + num y * den x) (den x * den y) _.

Global Program Instance Frac_negate:
    Negate Frac := λ x, frac (- num x) (den x) _.

Global Program Instance Frac_0:
    Zero Frac := frac 0 1 _.

Global Program Instance Frac_mult:
    Mult Frac := λ x y, frac (num x * num y) (den x * den y) _.

Global Program Instance Frac_1:
    One Frac := frac 1 1 _.

Global Program Instance Frac_inject:
    Cast R Frac := λ r, frac r 1 _.

(** Setoid properties *********************************************************)

Local Hint Unfold Frac_equiv  : core.
Local Hint Unfold Frac_plus   : core.
Local Hint Unfold Frac_negate : core.
Local Hint Unfold Frac_mult   : core.
Local Hint Unfold equiv       : core.
Local Hint Unfold Frac_inject : core.


#[global]
Instance: Reflexive Frac_equiv.
Proof. auto. Qed.

#[global]
Instance: Symmetric Frac_equiv.
Proof. auto. Qed.

(* TODO: the following proof of transitivity is terrible (and not a proof) *)
Lemma no_zd: ∀ x y : R, x * y = 0 -> x = 0 ∨ y = 0.
Admitted.

Lemma cancel: ∀ x y z : R, x * y = z * y -> x = z ∨ y = 0.
Proof. intros x y z E.
    destruct (no_zd (x - z) y).
    setoid_replace ((x-z)*y) with (x*y - z*y) by ring. rewrite E. ring.
    left. setoid_replace x with (x - 0) by ring. rewrite <- H1. ring.
    auto.
    Qed.

#[global]
Instance: Transitive Frac_equiv.
Proof.  red. unfold Frac_equiv. intros [nx dx] [ny dy] [nz dz] V W. simpl in *.
    assert (nx * dy * dz = nz * dy * dx) as E by (rewrite V; rewrite <- W; ring).
    setoid_replace (nx * dy * dz) with (nx * dz * dy) in E by ring.
    setoid_replace (nz * dy * dx) with (nz * dx * dy) in E by ring.
    destruct (cancel (nx * dz) dy (nz * dx)); auto. exfalso. apply mset_zero. rewrite <- H1. auto.
    Qed.

#[global]
Instance: Setoid Frac.
Proof. repeat (split; apply _). Qed.

(** Ring properties ***********************************************************)

Local Hint Extern 4 (_ = _) => simpl in *; ring : core.
Local Hint Extern 2 (_ = _) => match goal with
    | [H : _ = _ |- _ ] => ring_simplify [H]; clear H
    | _ => ring
    end : core.

(* TODO: the following three proofs are almost identical; can they be automated? *)
#[global]
Instance: Proper ((=) ==> (=) ==> (=)) Frac_plus.
Proof. intros [nx dx] [nx' dx'] eqx [ny dy] [ny' dy'] eqy.
    unfold Frac_plus, equiv, Frac_equiv in *; simpl in *; auto. Qed.

#[global]
Instance: Proper ((=) ==> (=)) Frac_negate.
Proof. intros [nx dx] [ny dy] e.
    unfold Frac_negate, equiv, Frac_equiv in *; simpl in *; auto. Qed.

#[global]
Instance: Proper ((=) ==> (=) ==> (=)) Frac_mult.
Proof. intros x x' eqx y y' eqy.
    unfold Frac_mult, equiv, Frac_equiv in *; simpl in *; auto. Qed.

#[global]
Instance: Ring Frac.
Proof. repeat (split; try apply _); repeat (intro x; auto). Qed.

(** Injection properties ******************************************************)

#[global]
Instance: Proper ((=) ==> (=)) Frac_inject.
Proof. intros x y eq.
    unfold Frac_inject, Frac_equiv, equiv in *. simpl in *. ring_simplify. auto. Qed.

#[global]
Instance: Setoid_Morphism Frac_inject.
Proof. repeat (split; try apply _). Qed.

(* TODO: each of the following lemmas has a trivial proof (auto); it would be
   nice to just unify them in the Instance proof below, but because the monoid
   operation and unit are overloaded, the proof search gets confused. *)

Lemma additive: ∀ x y : R, ('(x + y) : Frac) = ('x : Frac) + ('y : Frac).
Proof. auto. Qed.
Local Hint Resolve additive : core.

Lemma multiplicative: ∀ x y : R, ('(x * y) : Frac) = ('x : Frac) * ('y : Frac).
Proof. auto. Qed.
Local Hint Resolve multiplicative : core.

Lemma inject_0: ('0 : Frac) = 0.
Proof. auto. Qed.
Local Hint Resolve inject_0 : core.

Lemma inject_1: ('1 : Frac) = 1.
Proof. auto. Qed.
Local Hint Resolve inject_1 : core.

#[global]
Instance: SemiRing_Morphism Frac_inject.
Proof. repeat (split; try apply _); auto. Qed.

#[global]
Instance: Injective Frac_inject.
Proof. repeat (split; try apply _);
    intros x y e; unfold Frac_inject, equiv, Frac_equiv in e; simpl in *; auto.
    Qed.

(** Lifting *******************************************************************)

(** Universality **************************************************************)

(** Ordering ******************************************************************)

Context `{Signed R}.

Global Program Instance Frac_sign:
    Signed Frac := λ x, match sign (den x) with
        | pos => sign (num x)
        | neg => flip (sign (num x))
        | zer => _
    end.

#[global]
Instance: Proper ((=) ==> (=)) Frac_sign.
Proof. intros x y eq. unfold Frac_sign. destruct (sign (den x)) eqn:caseA. destruct (sign (den y)) eqn:caseB.
  unfold equiv, Frac_equiv in eq.

(*
a/b ≤ c/d

a sign(d) d / b ≤ c sign(d)
sign(b)sign(d) ac ≤ bc sign(b)sign(d)

match sign b, sign d with
    | neg, neg | pos, pos => a*d ≤ b*c
    | neg, pos | pos, neg => b*c ≤ a*d


Global Instance Frac_le:
    Le Frac := λ x y, num x ≤ 0 ∧ 

