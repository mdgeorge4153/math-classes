Require Import
  Coq.Classes.Morphisms
  Coq.Sorting.Mergesort Coq.Sorting.Permutation Coq.Structures.Orders 
  FunInd Recdef
  Coq.Lists.List
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.orders
  MathClasses.theory.groups
  MathClasses.implementations.peano_naturals
  Psatz.

Import ListNotations.

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

Function gexp_list_denote (env : list A) (e : list gexp) : A := match e with
  | []    => mon_unit
  | x::[] => gexp_denote env x
  | e::es => gexp_list_denote env es & gexp_denote env e
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
  | GroupOp a b           => flatten b ++ flatten a
  | Inverse (GroupOp a b) => flatten (Inverse a) ++ flatten (Inverse b)
  | Inverse Identity      => []
  | Inverse (Inverse a)   => flatten a
  | Inverse (Atomic a)    => [Inverse (Atomic a)]
  | Identity              => []
  | Atomic a              => [Atomic a]
end.
all: intros; simpl; lia.
Defined.

Lemma denote_append : ∀ env a b,
  gexp_list_denote env (a ++ b) = (gexp_list_denote env b) & (gexp_list_denote env a).
Proof. intros. functional induction (gexp_list_denote env) a.
  simpl. rewrite right_identity. reflexivity.
  simpl. destruct b.
    simpl. rewrite left_identity. reflexivity.
    reflexivity.
  rewrite <- app_comm_cons.
    destruct es. contradiction.
    rewrite associativity. rewrite <- IHa0. simpl. reflexivity.
Qed.

Lemma denote_cons : ∀ env a b, gexp_list_denote env (a :: b) = gexp_list_denote env b & gexp_denote env a.
Proof. intros. functional induction (gexp_list_denote env) b.
  rewrite left_identity. reflexivity.
  simpl. reflexivity.
  destruct es.
    contradiction.
    simpl. reflexivity.
Qed.

Theorem flatten_correct: ∀ (env : list A) (e : gexp),
  gexp_denote env e = gexp_list_denote env (flatten e).
Proof. intros env e; functional induction (flatten e); simpl.
  rewrite denote_append. rewrite IHl. rewrite IHl0. reflexivity.
  rewrite denote_append. rewrite <- IHl. rewrite <- IHl0. simpl. apply negate_sg_op_distr_flip.
  apply negate_mon_unit.
  rewrite IHl. apply involutive.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Function cancel (es : list gexp) {measure length} := 
match es with
  | Atomic n :: Inverse (Atomic m) :: es' => if decide (n = m) then cancel es' else Atomic n :: cancel (Inverse (Atomic m) :: es')
  | Inverse (Atomic n) :: Atomic m :: es' => if decide (n = m) then cancel es' else Inverse (Atomic n) :: cancel (Atomic m :: es')
  | x :: es' => x :: cancel es'
  | [] => []
end.
all: simpl; intros; repeat constructor.
Defined.

Lemma cancel_correct: ∀ env es, gexp_list_denote env es = gexp_list_denote env (cancel es).
Proof. intros env es. functional induction cancel es.
  rewrite _x. rewrite <- IHl. simpl. destruct es'.
    simpl. rewrite left_inverse. reflexivity.
    rewrite <- associativity. rewrite left_inverse. rewrite right_identity. reflexivity.
  rewrite denote_cons. rewrite denote_cons. rewrite denote_cons. rewrite <- IHl. rewrite denote_cons. reflexivity.
  repeat rewrite denote_cons. simpl. rewrite <- associativity. rewrite _x. rewrite right_inverse. rewrite right_identity. assumption.
  repeat rewrite denote_cons. rewrite <- IHl. rewrite denote_cons. reflexivity.
  repeat rewrite denote_cons. rewrite <- IHl. reflexivity.
  reflexivity.
Qed.

Theorem group_reflect : ∀ env e1 e2,
  gexp_list_denote env (cancel (flatten e1)) = gexp_list_denote env (cancel (flatten e2))
  -> gexp_denote env e1 = gexp_denote env e2.
Proof. intros;
  (rewrite_strat subterms flatten_correct);
  (rewrite_strat subterms cancel_correct);
  assumption.
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

Ltac group := match goal with
  | [ |- ?ge1 = ?ge2 ] => let vars := allVars (nil : list A) ge1 in
                          let vars := allVars vars ge2 in
                          let e1   := reifyTerm vars ge1 in
                          let e2   := reifyTerm vars ge2 in
                          change (gexp_denote vars e1 = gexp_denote vars e2);
                          apply group_reflect; simpl
end.

(* TODO: this should fail if there's no terms to simplify, partly so that it can
go on to the next term to simplify.
*)
Ltac group_simplify := repeat progress match goal with
  | [ |- context [?ge1 & ?ge2] ] => let ge := constr:(ge1 & ge2) in
                         let vars := allVars (nil:list A) ge in
                         let e := reifyTerm vars ge in
                         setoid_replace ge with (gexp_list_denote vars (cancel (flatten e)))
                         by (rewrite <- cancel_correct; rewrite <- flatten_correct; simpl; reflexivity);
                         simpl
end.

Lemma group_test : ∀ x y z w, x & w & y & -(z & y) = x & (y & -y) & w & -z .
Proof. intros; group. reflexivity. Qed.


Module TermOrder <: TotalLeBool.
  Definition t := gexp.
  Fixpoint index x := match x with
    | GroupOp _ _ => 0
    | Identity    => 0
    | Inverse x   => index x
    | Atomic n    => n
    end.

  Definition leb x y := if decide(index x ≤ index y) then true else false.

  Infix "<=?" := leb (at level 70, no associativity).

  Theorem leb_total : ∀ a1 a2, (eq (a1 <=? a2) true) \/ (eq (a2 <=? a1) true).
  Proof. unfold leb. intros a1 a2.
    destruct (total (≤) (index a1) (index a2));
      destruct (decide (index a1 ≤ index a2));
      destruct (decide (index a2 ≤ index a1));
      firstorder. Qed.
End TermOrder.

Module TermSort := Sort TermOrder.

Lemma denote_permutation `{!AbGroup A}: ∀ env l m, Permutation l m ->
  gexp_list_denote env l = gexp_list_denote env m.
Proof. intros env l m p. induction p.
  reflexivity.
  repeat rewrite denote_cons. rewrite IHp. reflexivity.
  repeat rewrite denote_cons. repeat rewrite <- associativity. apply sg_op_proper. reflexivity. apply commutativity.
  auto.
  Qed.

Lemma sort_correct `{!AbGroup A}: ∀ env es,
  gexp_list_denote env es = gexp_list_denote env (TermSort.sort es).
Proof. intros. apply denote_permutation. apply TermSort.Permuted_sort. Qed.

Theorem abgroup_reflect `{!AbGroup A}: ∀ env e1 e2,
  gexp_list_denote env (cancel (TermSort.sort (flatten e1))) = gexp_list_denote env (cancel (TermSort.sort (flatten e2)))
  -> gexp_denote env e1 = gexp_denote env e2.
Proof. intros.
  rewrite_strat subterms flatten_correct;
                subterms sort_correct;
                subterms cancel_correct.
  assumption.
  Qed.

Ltac abgroup := match goal with
  | [ |- ?ge1 = ?ge2 ] => let vars := allVars (nil : list A) ge1 in
                          let vars := allVars vars ge2 in
                          let e1   := reifyTerm vars ge1 in
                          let e2   := reifyTerm vars ge2 in
                          change (gexp_denote vars e1 = gexp_denote vars e2);
                          apply abgroup_reflect; simpl
end.

Lemma abgroup_test `{!AbGroup A}: ∀ x y z w, x & y & -x & -y & -(z & w) = -w & -w & -z & w.
Proof. intros; abgroup; reflexivity. Qed.


