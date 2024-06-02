Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Definition isOne (n : Nat) : bool :=
  match n with
  | S O => true
  | _ => false
  end.

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

Compute twice (S O).

Lemma SStwice : forall (n : Nat),
  S (S (S (twice n))) = S (twice (S n)).
intros.
simpl.
reflexivity.
Qed.

Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.

(*
f (S (S O)) = f (S O) = f O = O
     \___/         n
       n
*)

Lemma fO (a : Nat) : f a = O.
Proof.
(*
teljes indukcio:
P a = (f a = O)

 - P O = (f O = O)
 - (forall (a : Nat), P a -> P (S a)) = 
     forall (a : Nat), (f a = O) -> f (S a) = O
-------------------------
forall (a : Nat), P a = 
   forall (a : Nat), f a = O
*)
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite -> IHa. reflexivity.
Qed.

Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).
(*
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

Lemma decEq (a b : Nat) : a = b \/ a <> b.

Compute (max four six).
*)

Inductive BinaryTree : Type :=
| Leaf (n : Nat)
| Node (l r : BinaryTree).
(* 
| Leaf : Nat -> Type
| Node : BinaryTree -> BinaryTree -> BinaryTree

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

Definition five := S four.
Definition one  := S O.
Definition two  := S one.
Definition three := S two.

Definition tree  : BinaryTree := 
   Node
     (Node
        (Leaf one)
        (Node
           (Leaf two)
           (Leaf three)))
     (Node
        (Leaf four) 
        (Leaf five)).

Fixpoint max (a b : Nat) : Nat :=
  match a,b with
  | O,b => b
  | S a,O => S a
  | S a,S b => S (max a b)
  end.

Compute max four O.

Fixpoint height (t : BinaryTree) : Nat :=
  match t with
  | Leaf n => O
  | Node t t' => S (max (height t) (height t'))
  end.

Fixpoint leaves_count (t : BinaryTree) : Nat :=
  match t with
  | Leaf n => S O
  | Node t t' => leaves_count t + leaves_count t'
  end.

Fixpoint exp2 (n : Nat) : Nat :=
  match n with
  | O => S O
  | S m => exp2 m + exp2 m
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
