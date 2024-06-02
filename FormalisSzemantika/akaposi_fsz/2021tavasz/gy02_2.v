
(*Lemma nehez : forall (f : bool -> bool)(x : bool), f (f (f x)) = f x.*)
Lemma nehez (f : bool -> bool)(x : bool) : f (f (f x)) = f x.
Proof.
destruct x.
* destruct (f true) eqn:H.
** rewrite -> H. exact H.
** destruct (f false) eqn:H1.
**** rewrite -> H. reflexivity.
**** exact H1.
* destruct (f false) eqn:H.
** (* f false = true *) 
   destruct (f true) eqn:H1.
*** exact H1.
*** exact H.
** (* f false = false *)
   rewrite -> H. exact H.
Qed.
(* HF: ugy leirni, hogy eloszor f true-ra, f false-ra destructolunk, es mindegyik alesetben kulon az x-re. *)

(*
f :: Bool -> Bool
f x = f x
*)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat. (* S n = n' (diszkret matek jegyzetben) *)
(* data Nat = O | S Nat  *)

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Definition isOne : Nat -> bool := fun n => match n with
(* Definition isOne (n : Nat) : bool := match n with *)
  | O => false
  | S O => true
  | S (S n) => false
  end.

(* fun-nal is *)

Compute isOne four.
Compute isOne six.
Compute isOne O.
Compute isOne (S O).

Fixpoint twice (k : Nat) : Nat := match k with
  | O => O
  | S n => S (S (twice n))
  end.

(*
twice (S (S (S O))) =
S (S (twice (S (S O)))     =
S (S (S (S (twice (S O)         =
S (S (S (S (S (S (twice O             =
S (S (S (S (S (S (O
*)
Compute twice six.

Eval compute in twice six.

Lemma SStwice : forall (n : Nat),
  S (S (S (twice n))) = S (twice (S n)).
(* 3+2*n = 1+2+2*n = 1+2*(1+n) *)
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.
Definition f' (n : Nat) : Nat := O.

Lemma f'null (a : Nat) : f' a = O.
Proof. unfold f'. reflexivity. Qed.

Lemma fnull (a : Nat) : f a = O.
Proof.
(*
P O
minden m-re, ha P m -> P (S m)
----------------
minden n-ra P n
*)
induction a.
(*
P n := (f n = 0)
1. f 0 = 0
2. (f m = 0) -> (f (S m) = 0)
*)
* simpl. reflexivity.
* simpl. exact IHa.
Qed.

(* Fixpoint f (n : Nat) : Nat := f n. *)

(* minden m∈N-re létezik olyan s_m:N→N függvény *)
Fixpoint plus (m n : Nat) : Nat := match n with
  | O => m           (* s_m(0)=m *)
  | S n => S (plus m n) (* n∈N-re s_m(n′) = (s_m(n))′ *)
  end.
(*   m+(S n) = m+(1+n) = 1+(m+n) = S(m+n) *)

Compute plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

(* 4.1.5 tetel (2) *)
Lemma leftid (n : Nat) : O + n = n.
Proof. induction n as [|n IH].
* simpl. reflexivity. (* nyilvánvaló *)
* simpl. rewrite -> IH. reflexivity. 
(*        simpl        IH 
Ekkor 0+n′  =  (0+n)′  =  n′, *)
Qed.

Lemma rightid (n : Nat) : n + O = n.
Proof. simpl. reflexivity.
Qed.

(*
Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c).

Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.

Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.

Lemma comm (a b : Nat) : a + b = b + a.

Definition pred (n : Nat) : Nat :=

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
*)
(*
Inductive BinaryTree : Type :=
| Leaf (n : Nat)
| Node (l r : BinaryTree).
*)
Inductive BinaryTree : Type :=
| Leaf : Nat -> BinaryTree
| Node : BinaryTree -> BinaryTree -> BinaryTree.
(* data BinaryTree = Leaf Nat | Node BinaryTree BinaryTree *)
(*
   /\
  /\ 0
 0  1
*)
Definition ex : BinaryTree :=
  Node (Node (Leaf O) (Leaf (S O))) (Leaf O).

(*Fixpoint height (t : BinaryTree) : Nat := *)

Fixpoint leaves_count (t : BinaryTree) : Nat := match t with
  | Leaf _ => S O
  | Node t1 t2 => leaves_count t1 + leaves_count t2
  end.



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

(* destruct a eqn:H, rewrite ->, induction *)
