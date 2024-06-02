Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Inductive BinaryTree : Type :=
| Leaf (n : Nat)
| Node (l r : BinaryTree).

Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y)
  (at level 50, left associativity).


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

Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
Proof.
intros. simpl. (* plus n (S m) *)
  induction a.
  * simpl. reflexivity.
  * simpl. rewrite IHa. reflexivity.
Qed.

Lemma rightid (n : Nat) : n + O = n.
simpl. 
induction n.
 - reflexivity.
 - simpl. rewrite -> IHn. reflexivity.
Qed.

Lemma plus_comm : forall a b : Nat, a + b = b + a.
Proof.
  intros. induction a.
  * simpl. rewrite rightid. reflexivity.
  * simpl. rewrite IHa. rewrite <- plus_r_s. simpl. reflexivity.
Qed.

Lemma sum1_2_eq : forall t : BinaryTree, sum1 t = sum2 t.
Proof.
  intro. induction t.
  * simpl. reflexivity.
  * simpl. rewrite -> IHt1, -> IHt2. rewrite plus_comm. reflexivity.
Qed.


