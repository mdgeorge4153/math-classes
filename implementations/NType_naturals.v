Require
  MathClasses.implementations.stdlib_binary_integers MathClasses.theory.integers MathClasses.orders.semirings.
Require Import
  Coq.Setoids.Setoid Bignums.SpecViaZ.NSig Bignums.SpecViaZ.NSigNAxioms Coq.NArith.NArith Coq.ZArith.ZArith Coq.Program.Program Coq.Classes.Morphisms
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.naturals MathClasses.interfaces.integers
  MathClasses.interfaces.orders MathClasses.interfaces.additional_operations.

Module NType_Integers (Import anyN: NType).

Module axioms := NTypeIsNAxioms anyN.

#[global]
Instance NType_equiv : Equiv t := eq.
#[global]
Instance NType_plus : Plus t := add.
#[global]
Instance NType_0 : Zero t := zero.
#[global]
Instance NType_1 : One t := one.
#[global]
Instance NType_mult : Mult t := mul.

#[global]
Instance: Setoid t | 10 := {}.

#[global]
Program Instance: ∀ x y: t, Decision (x = y) := λ x y, match compare x y with
  | Eq => left _
  | _ => right _
  end.
Next Obligation.
  apply Zcompare_Eq_eq. now rewrite <-spec_compare.
Qed.
Next Obligation.
  rewrite spec_compare in *. intros E.
  apply Zcompare_Eq_iff_eq in E. auto.
Qed.

Ltac unfold_equiv := unfold equiv, NType_equiv, eq in *.

Lemma  NType_semiring_theory: semi_ring_theory zero one add mul eq.
Proof. repeat split; repeat intro; axioms.zify; auto with zarith. Qed.

#[global]
Instance: SemiRing t | 10 := rings.from_stdlib_semiring_theory NType_semiring_theory.

#[global]
Instance inject_NType_N: Cast t N := to_N.

#[global]
Instance: Proper ((=) ==> (=)) to_N.
Proof. intros x y E. unfold equiv, NType_equiv, eq in E. unfold to_N. now rewrite E. Qed.

#[global]
Instance: SemiRing_Morphism to_N.
Proof.
  repeat (split; try apply _); unfold to_N; intros.
     now rewrite spec_add, Z2N.inj_add by apply spec_pos.
    unfold mon_unit, zero_is_mon_unit, NType_0. now rewrite spec_0.
   now rewrite spec_mul, Z2N.inj_mul by apply spec_pos.
  unfold mon_unit, one_is_mon_unit, NType_1. now rewrite spec_1.
Qed.

#[global]
Instance inject_N_NType: Cast N t := of_N.
#[global]
Instance: Inverse to_N := of_N.

#[global]
Instance: Surjective to_N.
Proof.
  split; try apply _. intros x y E.
  rewrite <-E. unfold to_N, inverse, compose. rewrite spec_of_N.
  apply N2Z.id.
Qed.

#[global]
Instance: Injective to_N.
Proof.
  split; try apply _. intros x y E.
  unfold equiv, NType_equiv, eq. unfold to_N in E.
  rewrite <-(Z2N.id (to_Z x)), <-(Z2N.id (to_Z y)) by now apply spec_pos.
  now rewrite E.
Qed.

#[global]
Instance: Bijective to_N := {}.

#[global]
Instance: Inverse of_N := to_N.

#[global]
Instance: Bijective of_N.
Proof. apply jections.flip_bijection. Qed.

#[global]
Instance: SemiRing_Morphism of_N.
Proof. change (SemiRing_Morphism (to_N⁻¹)). split; apply _. Qed.

#[global]
Instance: NaturalsToSemiRing t := naturals.retract_is_nat_to_sr of_N.
#[global]
Instance: Naturals t := naturals.retract_is_nat of_N.

#[global]
Instance inject_NType_Z: Cast t Z := to_Z.

#[global]
Instance: Proper ((=) ==> (=)) to_Z.
Proof. now intros x y E. Qed.

#[global]
Instance: SemiRing_Morphism to_Z.
Proof.
  repeat (split; try apply _).
     exact spec_add.
    exact spec_0.
   exact spec_mul.
  exact spec_1.
Qed.

(* Order *)
#[global]
Instance  NType_le: Le t := le.
#[global]
Instance  NType_lt: Lt t := lt.

#[global]
Instance: Proper ((=) ==> (=) ==> iff) NType_le.
Proof.
  intros ? ? E1 ? ? E2. unfold NType_le, le. unfold equiv, NType_equiv, eq in *.
  now rewrite E1, E2.
Qed.

#[global]
Instance: SemiRingOrder NType_le.
Proof.
  apply (semirings.projected_srorder to_Z).
   reflexivity.
  intros x y E. exists (sub y x).
  unfold_equiv. rewrite spec_add, spec_sub.
  rewrite Z.max_r by now apply Z.le_0_sub.
  ring.
Qed.

#[global]
Instance: OrderEmbedding to_Z.
Proof. now repeat (split; try apply _). Qed.

#[global]
Instance: TotalRelation NType_le.
Proof. now apply (maps.projected_total_order to_Z). Qed.

#[global]
Instance: FullPseudoSemiRingOrder NType_le NType_lt.
Proof.
  rapply semirings.dec_full_pseudo_srorder.
  intros x y. split.
   intro. split.
    apply axioms.lt_eq_cases. now left.
   intros E. destruct (irreflexivity (<) (to_Z x)). now rewrite E at 2.
  intros [E1 E2].
  now destruct (proj1 (axioms.lt_eq_cases _ _) E1).
Qed.

(* Efficient comparison *)
#[global]
Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y, match (compare x y) with
  | Gt => right _
  | _ => left _
  end.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Z.compare_spec (to_Z x) (to_Z y)); try discriminate.
  now apply orders.lt_not_le_flip.
Qed.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Z.compare_spec (to_Z x) (to_Z y)); try discriminate; try intuition.
   now apply Zeq_le.
  now apply orders.lt_le.
Qed.

Lemma NType_succ_1_plus x : succ x = 1 + x.
Proof.
  unfold_equiv. rewrite spec_succ, rings.preserves_plus, rings.preserves_1.
  now rewrite commutativity.
Qed.

Lemma NType_two_2 : two = 2.
Proof.
  unfold_equiv. rewrite spec_2.
  now rewrite rings.preserves_plus, rings.preserves_1.
Qed.

(* Efficient [nat_pow] *)
#[global]
Program Instance NType_pow: Pow t t := pow.

#[global]
Instance: NatPowSpec t t NType_pow.
Proof.
  split.
    intros x1 y1 E1 x2 y2 E2.
    now apply axioms.pow_wd.
   intros x1. apply axioms.pow_0_r.
  intros x n.
  unfold_equiv. unfold "^", NType_pow.
  rewrite <-axioms.pow_succ_r by (red; rewrite spec_0; apply spec_pos).
  now rewrite NType_succ_1_plus.
Qed.

(* Efficient [shiftl] *)
#[global]
Program Instance NType_shiftl: ShiftL t t := shiftl.

#[global]
Instance: ShiftLSpec t t NType_shiftl.
Proof.
  apply shiftl_spec_from_nat_pow.
  intros x y.
  unfold additional_operations.pow, NType_pow, additional_operations.shiftl, NType_shiftl.
  unfold_equiv. simpl.
  rewrite rings.preserves_mult, spec_pow.
  rewrite spec_shiftl, Z.shiftl_mul_pow2 by apply spec_pos.
  now rewrite <-NType_two_2, spec_2.
Qed.

(* Efficient [shiftr] *)
#[global]
Program Instance: ShiftR t t := shiftr.

End NType_Integers.
