(*
    negneg, andor, orand, nat, is_one, double, plus, four, six, dummy_zero, plus_left_id, plus_right_id, plus_r_s, succ_cong

    Fixpoint, Notation (+)

    induction, rewrite, symmetry
*)

(*
Inductive Bool : Type :=
  | true : Bool
  | false : Bool.
Bool = {true, false}
*)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.
(*
Nat = { O, S O, S (S O), S (S (S O)), ... }
        0   1      2         3      , ...
*)


Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Definition isOne (n : Nat) : bool := match n with
  | S O => true
  | _   => false
  end.

(* fun-nal is *)
Definition isOne' : Nat -> bool := fun n => match n with
  | S O => true
  | _   => false
  end.

(*  
id x = x
id = \x -> x
id = fun x => x
*)

Compute isOne four.
Compute isOne six.
Compute isOne O.
Compute isOne (S O).

Lemma oneisOne : isOne (S O) = true. (* TOADD *)
simpl. reflexivity.
Qed.

Lemma notIsOne (n : Nat) : isOne (S (S n)) = false. (* TOADD *)
simpl. reflexivity.
Qed.

Fixpoint replaceOwith (m n : Nat) : Nat := match n with
  | O => m
  | S x => S (replaceOwith m x)
  end.

Definition twice' (n : Nat) : Nat := replaceOwith n n.

Fixpoint twice (n : Nat) : Nat := match n with
  | O => O
  | S m => S (S (twice m))
  end.

(* twice (S O) = S (S (twice O)) = S (S O) *)

Compute twice six.
Compute twice' six.

Lemma SStwice : forall (n : Nat),
  S (S (S (twice n))) = S (twice (S n)).
intro n. simpl. reflexivity.
Qed.

Lemma SStwice' (n : Nat) :
  S (S (S (twice n))) = S (twice (S n)).
Proof. reflexivity. Qed.

Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.

Check f.
Check S.

Lemma fO (a : Nat) : f a = O.
Proof.
induction a.
* simpl. reflexivity.
* simpl. (* rewrite IHa. reflexivity. *) assumption.
Qed.

(*
alapeset : P O
induktiveset: forall (m : Nat), P m -> P (S m)
----------------------------------------------
forall (n : Nat), P n

P n := (f n = O)
alapeset : O = O
induktiveset : forall (a : Nat), f a = O -> f a = O
---------------------------------------------------
forall (n : Nat), f n = O
*)

(* Fixpoint f (n : Nat) : Nat := f n. *)

(* Definition plus (n m : Nat) : Nat := replaceOwith m n. *)

Fixpoint plus (n m : Nat) : Nat := match n with
  | O    => m
  | S n' => S (plus n' m)
  end.

Compute plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity). (* (3 + (2 * 3)) + 1 *)

Lemma leftid (n : Nat) : O + n = n.
Proof. simpl. reflexivity. Qed.

Lemma rightid (n : Nat) : n + O = n.
Proof. simpl. induction n.
* reflexivity.
* simpl. rewrite -> IHn. reflexivity.
Qed.

(* Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c). *)

Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.
intro. rewrite H. reflexivity. Qed.

(*
            bevezeto           eliminacios
->          intro              apply
forall      intro              apply
=           reflexivity        rewrite
            symmetry
------------------------------------------------
Nat         O,S                induction, destruct
*)

Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
intro a. intro b. simpl. induction a.
* simpl. reflexivity.
* simpl. apply (cong S). (* f = S, a = (S (a + b)), b = (a + S b) *)
  assumption.
Qed.
(*
P a = S (a + b) = a + S b
P O = (S b = S b)
(forall n, P n -> P (S n)) = 
   (forall n, S (n + b) = n + S b -> S (S (n + b)) = S (n + S b))
*)

Lemma comm (a b : Nat) : a + b = b + a.
Proof.
  induction a.
  * simpl. Check rightid. symmetry. apply rightid.
  * simpl. rewrite IHa. apply plus_r_s.
Qed. 

Definition pred (n : Nat) : Nat := match n with
  | O => O
  | S n => n
  end.

Lemma S_inj (a b : Nat) : S a = S b -> a = b.
intro. Check (cong pred _ _ H). apply (cong pred (S a) (S b)).
assumption.
Qed.

(* kov. ora 1 perccel rovidebb lesz! *)

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
