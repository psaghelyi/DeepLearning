
(*
    negneg, andor, orand, nat, is_one, double, plus, four, six, dummy_zero, plus_left_id, plus_right_id, plus_r_s, succ_cong

    Fixpoint, Notation (+)

    induction, rewrite, symmetry
*)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

(* Nat = {O, S O, S (S O), S (S (S O)), ...  }*)

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Definition isOne (n : Nat) : bool := match n with
  | O => false
  | (S O) => true
  | _ => false
  end.
(* fun-nal is *)

Lemma oneisOne : isOne (S O) = true.
Proof. simpl. reflexivity. Qed.

Lemma notIsOne (n : Nat) : isOne (S (S n)) = false.
Proof. simpl. reflexivity. Qed.

Lemma zeroNotOne : isOne O = false.
Proof. simpl. reflexivity. Qed.

Compute isOne four.
Compute isOne six.
Compute isOne O.
Compute isOne (S O).

Fixpoint twice (n : Nat) : Nat := match n with
  | O => O
  | S n => S (S (twice n))
  end.

(*  
twice (S O) = S (S (twice O)) = S (S O)
*)

Compute twice six.

Lemma SStwice : forall (n : Nat),
  S (S (S (twice n))) = S (twice (S n)).
Proof. simpl. intro. reflexivity. Qed.


Fixpoint twiceHelper (n : Nat)(m : Nat) : Nat := match n with
  | O => m
  | S x => S (twiceHelper x m)
  end.

Definition twice' (n : Nat) : Nat := twiceHelper n n.

Compute twice' four.


Lemma SStwice' : forall (n : Nat),
  S (S (S (twice' n))) = S (twice' (S n)).
Proof. intro. rewrite 
- 


    * simpl. reflexivity.
    * simpl. reflexivity. 


Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.

Check Type.

Lemma fConstNull (a : Nat) : f a = O.
(*
Proof. destruct a.
- simpl. reflexivity.
- simpl. destruct a.
-- simpl. reflexivity.
-- simpl. destruct a.
--- simpl. reflexivity.
--- simpl. destruct a.

teljes indukcio: P(n) teljesul minden n : nat-ra:
1. P(O) teljesul
2. minden m-re, ha P(m) teljesul, akkor P(S m) is teljesul
-------------------
P(S(S(SO)))  <----- P(SSO) <----- P(SO) <------ P(O)
*)
Proof. induction a. (*
 P(a) := (f a = O)
1. P(O) = (f O = O) = (O = O)
2. P(m) = (f m = O) -----> P(S m) = (f (S m) = O) = (f m = O)
 *)
- simpl. reflexivity.
- simpl. assumption.
Qed.

(* Fixpoint f (n : Nat) : Nat := f n. *)

Fixpoint plus (n m : Nat) : Nat := match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

Lemma rightid (n : Nat) : n + O = n.
Proof.
simpl. induction n.
- simpl. reflexivity.
- simpl. rewrite -> IHn. reflexivity.
Qed.

(*
logikai osszekoto        forall     ->      True    False

bevezeto szabaly         intro      intro   split
  (ha ilyet akarok 
  bizonyitani)

eliminacios szabaly      apply      apply           destruct
  (ha ilyet feltetelem
   van)

*)

Lemma trueTrue : True.
Proof. split. Qed.

Lemma exfalso (A : Prop) :  False -> A.
Proof. intro. destruct H. Qed.

Lemma hamisbolValami : False -> 0 = 13.
Proof. intro. destruct H. Qed.

(* Inductive False : Prop := .*)


Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.
Proof. intro e. rewrite <- e. reflexivity. Qed.

Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
Proof. intros. induction a.
- simpl. reflexivity.
- simpl. simpl in IHa. rewrite -> IHa. reflexivity.
Qed.

Lemma comm (a b : Nat) : a + b = b + a.
Proof. induction a.
- simpl. Check rightid. symmetry. Check rightid. 
  apply rightid.
- simpl. rewrite -> IHa. Check plus_r_s.
  apply plus_r_s.
Qed.

Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c).
Proof. induction a.
- simpl. reflexivity.
- simpl. rewrite -> IHa. reflexivity.
Qed.

Lemma leftid (n : Nat) : O + n = n.
Proof. simpl. reflexivity. Qed.


(*
S a = S b
------------------------cong pred
pred (S a) = pred (S b)
------------------------simpl
   a = b


0 <> S n   =    0 = Sn -> False
0 = S n
P 0 -> P (S n)   minden P-re
P 0 = True
P (S n) = False


*)


Definition pred (n : Nat) : Nat := match n with
  | O => S(S(S(S(S(S O)))))
  | S n => n
  end.

Lemma S_inj (a b : Nat) : S a = S b -> a = b.
Proof. intro e. apply (cong pred (S a) (S b)). assumption.
Qed.

(* kovetkezo ora 4 perccel rovidebb *)

Definition P : Nat -> Prop := fun n => 
  match n with
  | O => True
  | S _ => False
  end.

Lemma O_S_disj (a : Nat) : O <> S a.
Proof.
  intro. assert (P O = P (S a)).
  - rewrite -> H. reflexivity.
  - simpl in H0. destruct a.
    + simpl in H0. rewrite <- H0. trivial.

Fixpoint times (a b : Nat) : Nat :=
  match a with
  | O => O
  | S a' => b + (times a' b)
  end.

Notation "x * y" := (times x y).
  (at level 40, left associativity).

Lemma times_leftid (a : Nat) : S O * a = a.
Proof.
  simpl. apply rightid. Qed.


Lemma times_rightid (a : Nat) : a * S O = a.
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite -> IHa. reflexivity.
Qed.

Lemma times_leftzero (a : Nat) : O * a = O.
Proof.
  simpl. reflexivity. Qed.


Lemma times_rightzero (a : Nat) : a * O = O.
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite -> IHa. reflexivity.
Qed.


Theorem plus_assoc : forall a b c : Nat, a + (b + c) = (a + b) + c.
Proof.
  intros a b c.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite -> IHa. reflexivity.
Qed.

Theorem mul_distributes_over_add : forall a b c : Nat, a * (b + c) = (a * b) + (a * c).
Proof.
  intros a b c.
  induction a as [| a' IHa'].
  - simpl. reflexivity.
  - simpl. rewrite IHa'. rewrite plus_assoc. rewrite plus_assoc. apply 

Lemma times_assoc (a b c : Nat) : (a * b) * c = a * (b * c).
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- IHa. rewrite <- assoc.


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
