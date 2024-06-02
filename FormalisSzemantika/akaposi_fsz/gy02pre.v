
(*
    negneg, andor, orand, nat, is_one, double, plus, four, six, dummy_zero, plus_left_id, plus_right_id, plus_r_s, succ_cong

    Fixpoint, Notation (+)

    induction, rewrite, symmetry
*)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Definition isOne (n : Nat) : bool :=
(* fun-nal is *)
match n with
| O => false
| S O => true
| S (S n) => false
end.

Lemma oneisOne : isOne (S O) = true. (* TOADD *)

Lemma notIsOne (n : Nat) : isOne (S (S n)) = false. (* TOADD *)


Compute isOne four.
Compute isOne six.
Compute isOne O.
Compute isOne (S O).

Fixpoint twice (n : Nat) : Nat :=
match n with
| O => O
| S n => S (S (twice n))
end.

Compute twice six.

Lemma SStwice : forall (n : Nat),
  S (S (S (twice n))) = S (twice (S n)).

Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.

Check Type.

Lemma (a : Nat) : f a = O.

(* Fixpoint f (n : Nat) : Nat := f n. *)

Fixpoint plus (n m : Nat) {struct n} : Nat :=

Compute plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

Lemma leftid (n : Nat) : O + n = n.

Lemma rightid (n : Nat) : n + O = n.

Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c).

Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.

Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.

Lemma comm (a b : Nat) : a + b = b + a.

Fixpoint pred (n : Nat) : Nat :=

Lemma S_inj (a b : Nat) : S a = S b -> a = b.

Definition P : Nat -> Prop := fun n =>

Lemma O_S_disj (a : Nat) : O <> S a.

Fixpoint times (a b : Nat) : Nat :=

Notation "x * y" := (times x y)
  (at level 40, left associativity).

Lemma times_leftid (a : Nat) : S O * a = a.

Lemma times_rightid (a : Nat) : a * S O = a.

Lemma times_leftzero (a : Nat) : O * a = O.

Lemma times_rightzero (a : Nat) : a * O = O.

Lemma times_assoc (a b c : Nat) : (a * b) * c = a * (b * c).

Lemma times_comm (a b : Nat) : a * b = b * a.

Fixpoint max (a b : Nat) : Nat :=

Lemma decEq (a b : Nat) : a = b \/ a <> b.

Compute (max four six).

Inductive BinaryTree : Type :=
| Leaf (n : Nat)
| Node (l r : BinaryTree).

Fixpoint height (t : BinaryTree) : Nat :=

Fixpoint leaves_count (t : BinaryTree) : Nat :=

Fixpoint sum1 (t : BinaryTree) : Nat :=
match t with
| Leaf n => n
| Node l r => sum1 l + sum1 r
end.

Fixpoint sum2 (t : BinaryTree) : Nat :=
match t with
| Leaf n => n
| Node l r => sum2 r + sum2 l
end.

Lemma sum1_2_eq : forall t : BinaryTree, sum1 t = sum2 t.
