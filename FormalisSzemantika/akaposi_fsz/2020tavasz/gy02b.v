Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Compute six.

Definition isOne (n : Nat) : bool :=
  match n with
  | O        => false
  | S O      => true
  | S (S n') => false
  end.
(*
  | S O => true
  | _   => false
*)

Compute isOne four.
Compute isOne six.
Compute isOne O.
Compute isOne (S O).

Lemma lemma_isOne (n : Nat) : isOne (S (S n)) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Check true.
Check false.
Check True.
Check (S (S (S O)) = S O).
Check (false = false).
Check bool. (* Set = Type *)
Check False. 

(*
P false = True
P true  = False
*)
Definition P (b : bool) : Prop := 
  match b with
  | false => True
  | true  => False
  end.

Lemma bool_disj : false <> true.
Proof.
  unfold not.
  intro.
  assert (K : P false = P true).
  - rewrite -> H.
    reflexivity.
  - simpl in K.
    rewrite <- K.
    trivial.
Qed.

(*
simpl [in H]
reflexivity
destruct a [eqn:H].
rewrite [->|<-] H [in K]. 
unfold f [in H].
intro
intros
trivial
exact
induction
*)
(*
HF
Lemma lemma_isOne' : 
  not (forall (n : Nat), isOne n <> isOne (S n)).
*)
(*
Fixpoint twice (n : Nat) : Nat :=

Eval compute in twice six.

Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.

Check Type.

Lemma (a : Nat) : f a = O.

(* Fixpoint f (n : Nat) : Nat := f n. *)
*)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m
  | S n => S (plus n m)
  end.
(*
plus 3 2 = plus (S 2) 2 = S (plus 2 2) = S (plus (S 1) 2) = 
                   n' m                             n' m

S (S (plus 1 2)) = S (S (plus (S O) 2)) = S (S (S (plus O 2))) = 
                                 n' m                   n m

S (S (S (2))) = 5
*)

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

Compute six + four.

Lemma leftid (n : Nat) : O + n = n.
simpl. reflexivity. Qed.

Lemma rightid (n : Nat) : n + O = n.
simpl. 
(*
1. P O
2. forall (n : Nat), P n -> P (S n)
-----------------------------------
forall (n : Nat), P n

P n := (n + O = n)
1. O + O = O
2. forall (n : Nat), (n + O = n) -> (S (n + O) = S n)
-----------------------------------------------------
forall (n : Nat), n + O = n
*)
induction n.
 - reflexivity.
 - simpl. rewrite -> IHn. reflexivity.
Qed.

Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c).
induction a.
- reflexivity.
- simpl. rewrite -> IHa. reflexivity.
Qed.
(*
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
*)
Inductive BinaryTree : Type :=
| Leaf (n : Nat)
| Node (l r : BinaryTree).
(*
b ::= L n | N b b
data BinTree = Leaf Nat | Node BinTree BinTree
| Leaf : Nat -> BinTree
| Node : BinTree -> BinTree -> BinTree

          /\
         /  \
        /    \
       /      \
      /\      /\
     /  \    /  \      
    1   /\  4    5
       /  \
      2    3
*)

Definition tree : BinaryTree :=
  Node
    (Node
       (Leaf (S O))
       (Node
          (Leaf (S (S O)))
          (Leaf (S (S (S O))))))
    (Node
       (Leaf four)
       (Leaf (S four))).

Fixpoint leaves_count (t : BinaryTree) : Nat :=
  match t with
  | Leaf n => S O
  | Node t t' => leaves_count t + leaves_count t'
  end.

Compute leaves_count tree.

Fixpoint height (t : BinaryTree) : Nat :=



Fixpoint exp2 (n : Nat) : Nat :=
  match n with
  | O => S O
  | S m => exp2 m + exp2 m (* 2*2^m *)
  end.

Lemma leaves_height (t : BinaryTree) :
  max (exp2 (height t)) (leaves_count t) =
  exp2 (height t).

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
