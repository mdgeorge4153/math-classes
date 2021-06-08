Require Import
  Coq.Classes.Morphisms
  FunInd Recdef
  Coq.Lists.List
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.orders
  MathClasses.theory.groups
  MathClasses.implementations.peano_naturals
  Psatz.

Import ListNotations.

Section GroupAutomation.

Context `{Group A}.

Inductive gexp : Type :=
  | Atomic   : nat -> gexp
  | Identity : gexp
  | GroupOp  : gexp -> gexp -> gexp
  | Inverse  : gexp -> gexp
  .

Fixpoint gexp_denote (env : list A) (e : gexp) : A := match e with
  | Atomic n => List.nth n env mon_unit
  | Identity => mon_unit
  | GroupOp a b => gexp_denote env a & gexp_denote env b
  | Inverse a => - (gexp_denote env a)
  end.

Fixpoint gexp_list_denote (env : list A) (e : list gexp) : A := match e with
  | []    => mon_unit
  | e::es => gexp_denote env e & gexp_list_denote env es
  end.

Fixpoint gexp_height a : nat := match a with
  | Atomic _    => 0
  | Identity    => 0
  | GroupOp a b => 1 + gexp_height a + gexp_height b
  | Inverse a   => 1 + gexp_height a
  end.

(* flatten produces a list that only contains Atomics and Inverse Atomics *)
Function flatten (e : gexp) {measure gexp_height} : list gexp :=
  match e with
  | GroupOp a b           => flatten a ++ flatten b
  | Inverse (GroupOp a b) => flatten (Inverse b) ++ flatten (Inverse a)
  | Inverse Identity      => []
  | Inverse (Inverse a)   => flatten a
  | Inverse (Atomic a)    => [Inverse (Atomic a)]
  | Identity              => []
  | Atomic a              => [Atomic a]
end.
all: intros; simpl; lia.
Defined.

Lemma denote_append : ∀ env a b, gexp_list_denote env (a ++ b) = (gexp_list_denote env a) & (gexp_list_denote env b).
Proof. induction a.
  intros. simpl. rewrite left_identity. reflexivity.
  intros. simpl. rewrite <- associativity. apply sg_op_proper. reflexivity. apply IHa. Qed.

Theorem flatten_correct: ∀ (env : list A) (e : gexp),
  gexp_denote env e = gexp_list_denote env (flatten e).
Proof. intros env e; functional induction (flatten e); simpl.
  rewrite denote_append. rewrite IHl. rewrite IHl0. reflexivity.
  rewrite denote_append. rewrite <- IHl. rewrite <- IHl0. simpl. apply negate_sg_op_distr_flip.
  apply negate_mon_unit.
  rewrite IHl. apply involutive.
  rewrite right_identity. reflexivity.
  reflexivity.
  rewrite right_identity. reflexivity.
Qed.

Function cancel (es : list gexp) {measure length} := 
match es with Atomic n :: Inverse (Atomic m) :: es' => if decide (n = m) then cancel es' else Atomic n :: cancel (Inverse (Atomic m) :: es')
  | Inverse (Atomic n) :: Atomic m :: es' => if decide (n = m) then cancel es' else Inverse (Atomic n) :: cancel (Atomic m :: es')
  | x :: es' => x :: cancel es'
  | [] => []
end.
all: simpl; intros; repeat constructor.
Defined.

Lemma cancel_correct: ∀ env es, gexp_list_denote env es = gexp_list_denote env (cancel es).
Proof. intros env es. functional induction cancel es.
  simpl. rewrite associativity. rewrite _x. rewrite right_inverse. rewrite left_identity. apply IHl.
  simpl. rewrite <- IHl. simpl. reflexivity.
  simpl. rewrite associativity. rewrite _x. rewrite left_inverse. rewrite left_identity. apply IHl.
  simpl. rewrite IHl. reflexivity.
  simpl. rewrite IHl. reflexivity.
  reflexivity.
Qed.

Theorem group_reflect : ∀ env e1 e2,
  gexp_list_denote env (flatten e1) = gexp_list_denote env (flatten e2)
  -> gexp_denote env e1 = gexp_denote env e2.
Proof. intros. rewrite flatten_correct. rewrite flatten_correct. assumption.
Qed.

Ltac inList x xs := match xs with
  | []      => false
  | x::_    => true
  | _::?xs' => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
    | true => xs
    | false => constr:(x::xs)
  end.

Ltac lookup x xs := match xs with
  | x::_    => O
  | _::?xs' => let n := (lookup x xs') in
               constr:(S n)
  | _ => fail "no match for" x "in" xs
  end.

Ltac allVars xs e := match e with
  | (?x = ?y) => let xs' := allVars xs x in
                 allVars xs' y
  | (?x & ?y) => let xs' := allVars xs x in
                 allVars xs' y
  | (- ?x)    => allVars xs x
  | mon_unit  => xs
  | _         => addToList e xs
end.

Ltac reifyTerm xs e :=
let _ := match goal with | _ => idtac "reifyTerm" e end in
match e with
  | (?x = ?y) => let a := reifyTerm xs x in
                 let b := reifyTerm xs y in
                 constr:((a,b))
  | (?x & ?y) => let a := reifyTerm xs x in
                 let b := reifyTerm xs y in
                 constr:(GroupOp a b)
  | (- ?x)    => let a := reifyTerm xs x in
                 constr:(Inverse a)
  | mon_unit  => constr:(Identity)
  | _         => let n := lookup e xs in
                 constr:(Atomic n)
  end.

Ltac reify := match goal with
  | [ |- ?ge1 = ?ge2 ] => let vars := allVars (nil : list A) ge1 in
                          let vars := allVars vars ge2 in
                          let e1   := reifyTerm vars ge1 in
                          let e2   := reifyTerm vars ge2 in
                          change (gexp_denote vars e1 = gexp_denote vars e2);
                          apply group_reflect; simpl
end.

Lemma foo : ∀ x y z, x & -y & -(z & y) = x & -z.
Proof. intros. reify. 
