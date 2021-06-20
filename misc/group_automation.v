Require Import
  Coq.Classes.Morphisms
  Coq.Sorting.Mergesort Coq.Sorting.Permutation Coq.Structures.Orders 
  FunInd Recdef
  Coq.Lists.List
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.orders
  MathClasses.theory.groups
  MathClasses.implementations.peano_naturals
  Coq.Init.Nat
  Psatz.

Import ListNotations.

Section GroupAutomation.

Context `{Group A}.

(* Basic reflection of group expressions **************************************)

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

Fixpoint gexp_height a : nat := match a with
  | Atomic _    => 0
  | Identity    => 0
  | GroupOp a b => 1 + gexp_height a + gexp_height b
  | Inverse a   => 1 + gexp_height a
  end.

(* Representing a group expression as a list of Atomics and Inverses **********)

Function gexp_list_denote (env : list A) (e : list gexp) : A := match e with
  | []    => mon_unit
  | x::[] => gexp_denote env x
  | e::es => gexp_list_denote env es & gexp_denote env e
  end.

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

(* Flattening group expressions ***********************************************)

(* flatten transforms e into a list that only contains Atomics and Inverse Atomics *)
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

(* Cancelling out adjacent inverses *******************************************)

Function cancel (es : list gexp) {struct es} :=
match es with
  | [] => []
  | e :: es' => let ces' := cancel es' in
                match e, ces' with
                  | Atomic n, Inverse (Atomic m) :: ces''
                  | Inverse (Atomic n), Atomic m :: ces'' =>
                      if decide (n = m) then ces'' else e::ces'
                  | _, _ => e :: ces'
                end
end.

Lemma cancel_correct: ∀ env es, gexp_list_denote env es = gexp_list_denote env (cancel es).
Proof. intros env es. functional induction cancel es.
  reflexivity.
  rewrite denote_cons; rewrite IHl; rewrite e2; rewrite denote_cons; simpl; rewrite _x; group.
  repeat rewrite denote_cons; rewrite IHl; reflexivity.
  rewrite denote_cons; rewrite IHl; rewrite e2; rewrite denote_cons; simpl; rewrite _x; group.
  repeat rewrite denote_cons; rewrite IHl; reflexivity.
  repeat rewrite denote_cons. rewrite IHl. reflexivity.
Qed.

(* Reorganizing equations *****************************************************)

Lemma move_to_left : ∀ a b, a & -b = mon_unit -> a = b.
Proof. intros. setoid_replace b with (a & -b & b).
  rewrite <- associativity. rewrite left_inverse. rewrite right_identity. reflexivity.
  rewrite H0. rewrite left_identity. reflexivity.
Qed.


(**
 * einvs should be the simplified inverse of es, so that the tail of es is the
 * inverse of the head of einvs.
 *)
Function deconjugate_mirrors (front : list gexp) (back : list gexp) : list gexp :=
  match front, back with
    |         (Atomic n) :: es', Inverse (Atomic m) :: einvs'
    | Inverse (Atomic n) :: es',         (Atomic m) :: einvs' =>
      if decide(n = m) then deconjugate_mirrors es' einvs'
      else front ++ rev back
    | _, _ => front ++ rev back
  end.

Lemma deconj_mirrors_correct : ∀ f b : list gexp, ∀ env,
  gexp_list_denote env (deconjugate_mirrors f b) = mon_unit ->
  gexp_list_denote env (f ++ rev b) = mon_unit.
Proof. intros f b env assum; functional induction deconjugate_mirrors f b; (try assumption);
  simpl rev; repeat rewrite denote_append, denote_cons; simpl;
  match goal with
    | [ |- (mon_unit & ?x & ?y & (?z & ?w)) = mon_unit ] => setoid_replace (mon_unit & x & y & (z & w)) with (x & (y & z) & w) by group
  end;
  rewrite _x; rewrite denote_append in IHl; rewrite IHl by assumption; group.
Qed.

Definition deconjugate `(xs : list gexp) :=
  let n     := div (length xs) 2 in
  let front := firstn n xs in
  let back  := rev (skipn  n xs) in
  deconjugate_mirrors front back.

Lemma deconj_correct : ∀ xs env,
  gexp_list_denote env (deconjugate xs) = mon_unit ->
  gexp_list_denote env xs = mon_unit.
Proof. unfold deconjugate. intros xs env deconj_unit.
apply deconj_mirrors_correct in deconj_unit.
rewrite rev_involutive, firstn_skipn in deconj_unit.
assumption.
Qed.

(* Main theorems for rewriting goals ******************************************)

Theorem group_reflect : ∀ env e1 e2,
  gexp_list_denote env (cancel (flatten e1)) = gexp_list_denote env (cancel (flatten e2))
  -> gexp_denote env e1 = gexp_denote env e2.
Proof. intros;
  (rewrite_strat subterms flatten_correct);
  (rewrite_strat subterms cancel_correct);
  assumption.
Qed.


Theorem group_reflect_flip : ∀ env e1 e2,
  gexp_list_denote env (deconjugate (cancel (flatten (GroupOp e1 (Inverse e2))))) = mon_unit
  -> gexp_denote env e1 = gexp_denote env e2.
Proof. intros. apply move_to_left.
replace (gexp_denote env e1 & - gexp_denote env e2)
   with (gexp_denote env (GroupOp e1 (Inverse e2))).
    rewrite flatten_correct. rewrite cancel_correct. rewrite deconj_correct. reflexivity. assumption.
    simpl. reflexivity.
Qed.

End GroupAutomation.

(* Ltac refification **********************************************************)

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
  | [ |- ?ge1 = ?ge2 ] => let t    := type of ge1 in
                          let vars := allVars (nil : list t) ge1 in
                          let vars := allVars vars ge2 in
                          let e1   := reifyTerm vars ge1 in
                          let e2   := reifyTerm vars ge2 in
                          change (gexp_denote vars e1 = gexp_denote vars e2);
                          apply group_reflect_flip; simpl
end; try easy.

(* TODO: this should fail if there's no terms to simplify, partly so that it can
go on to the next term to simplify.
*)
Ltac group_simplify := repeat progress match goal with
  | [ |- context [?ge1 & ?ge2] ] =>
                         let ge := constr:(ge1 & ge2) in
                         let t  := type of ge in
                         let vars := allVars (nil : list t) ge in
                         let e := reifyTerm vars ge in
                         setoid_replace ge with (gexp_list_denote vars (cancel (flatten e)))
                         by (rewrite <- cancel_correct; rewrite <- flatten_correct; simpl; reflexivity);
                         simpl
end.

Lemma group_test `{Group A} : ∀ x y z w, x & w & y & -(z & y) = x & (y & -y) & w & -z .
Proof. intros. group. Qed.

Lemma group_test2 `{Group A}: ∀ x y z, -x & y = - (z & x) & (z & y).
Proof. intros; group. Qed.

Lemma group_test3 `{Group A}: ∀ x y,
  y = mon_unit -> -x & y & x = mon_unit.
Proof. intros. group. Qed.

(** Reordering in abelian groups **********************************************)

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

Lemma denote_permutation `{AbGroup A}: ∀ env l m, Permutation l m ->
  gexp_list_denote env l = gexp_list_denote env m.
Proof. intros env l m p. induction p.
  reflexivity.
  repeat rewrite denote_cons. rewrite IHp. reflexivity.
  repeat rewrite denote_cons. repeat rewrite <- associativity. apply sg_op_proper. reflexivity. apply commutativity.
  auto.
  Qed.

Lemma sort_correct `{AbGroup A}: ∀ env es,
  gexp_list_denote env es = gexp_list_denote env (TermSort.sort es).
Proof. intros. apply denote_permutation. apply TermSort.Permuted_sort. Qed.

Theorem abgroup_reflect `{AbGroup A}: ∀ env e1 e2,
  gexp_list_denote env (cancel (TermSort.sort (flatten e1))) = gexp_list_denote env (cancel (TermSort.sort (flatten e2)))
  -> gexp_denote env e1 = gexp_denote env e2.
Proof. intros.
  rewrite_strat subterms flatten_correct;
                subterms sort_correct;
                subterms cancel_correct.
  assumption.
  Qed.

Ltac abgroup := match goal with
  | [ |- ?ge1 = ?ge2 ] => let t    := type of ge1 in
                          let vars := allVars (nil : list t) ge1 in
                          let vars := allVars vars ge2 in
                          let e1   := reifyTerm vars ge1 in
                          let e2   := reifyTerm vars ge2 in
                          change (gexp_denote vars e1 = gexp_denote vars e2);
                          apply abgroup_reflect; simpl
end; try easy.

Lemma abgroup_test `{AbGroup A}: ∀ x y z w, x & y & -x & -y & -(z & w) = -w & -w & -z & w.
Proof. intros; abgroup; reflexivity. Qed.


