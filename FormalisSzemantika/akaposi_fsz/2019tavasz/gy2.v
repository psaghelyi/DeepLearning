(* BEGIN FIX *)
Inductive Bool : Type :=
  | true
  | false.

Definition orb (b1 b2 : Bool) : Bool
(* END FIX *)
 := match b1 with
 | true => true
 | false => b2
 end.

Notation "x || y" := (orb x y) 
  (at level 50, left associativity).

(* BEGIN FIX *)
Example test_orb_1 : true || false = true.
(* END FIX *)
simpl.
reflexivity.
Qed.

(* BEGIN FIX *)
Example test_orb_2 : false || false = false.
(* END FIX *)
simpl.
reflexivity.
Qed.

Definition negb (b : Bool) : Bool := 
  match b with
  | true => false
  | false => true
  end.

Example negneg (b : Bool) : negb (negb b) = b.
intros b.
destruct b.
(* true *)
simpl.
reflexivity.
(* false *)
simpl.
reflexivity.
Qed.

Eval compute in (true || false).

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Definition isOne (n : Nat) : Bool :=
  match n with
  | O => false
  | S O => true
  | _ => false
  end.

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Eval compute in isOne four.
Eval compute in isOne six.
Eval compute in isOne O.
Eval compute in isOne (S O).

Fixpoint twice (n : Nat) : Nat :=
  match n with
  | O => O
  | S n => S (S (twice n))
  end.

Eval compute in twice six.

Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.

Check Type.

(* Fixpoint f (n : Nat) : Nat := f n. *)

Fixpoint plus (n m : Nat) {struct n} : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Eval compute in plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

Lemma leftid (n : Nat) : O + n = n.
simpl.
reflexivity.
Qed.

Lemma rightid (n : Nat) : n + O = n.
intros n.
simpl.
induction n as [|m H].
reflexivity.
simpl.
rewrite -> H.
reflexivity.
Qed.


