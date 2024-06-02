(* HF *)

Definition t : bool := negb true.

Compute t.

Lemma lem (a : 3 = 4) : 3 = 4.
assumption. Qed.


Lemma not3x (f : bool -> bool)(b : bool) : f (f (f b)) = f b.
(*
bool -> bool = 2->2 = 2^2 = 4
*)
Proof.
destruct (f true) eqn:H; destruct (f false) eqn:H'; destruct b;
  try (rewrite -> H); 
  try (rewrite -> H'); 
  try (rewrite -> H); 
  try (rewrite -> H'); 
  try (rewrite -> H); 
  try (rewrite -> H'); 
  reflexivity.
Qed.

Print not3x.


Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

(* {O,S O,S (S O),S (S (S O)), ...}
    0,1  ,2      ,3          ,
 *)

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Definition isOne (n : Nat) : bool := match n with
| O => false
| S O => true
| S (S n) => false
end.
(* fun-nal is *)

(* Definition evil : 0 = 1 := evil. *)
(* Fixpoint evil (n : Nat) : 0 = 1 := evil n. *)

Definition isOne' : Nat -> bool := fun n => isOne n. (* Haskellben (\n-> isOne n)*)

Compute isOne four.
Compute isOne six.
Compute isOne O.
Compute isOne (S O).

Fixpoint twice (n : Nat) : Nat := match n with
| O => O
| S n => S (S (twice n))
end.
(*
twice O := O
twice (S n) = 2*(1+n) = 2+2*n = 2+twice n = S (S (twice n))
*)
(*
twice (S (S O)) = S (S (twice (S O)) = S (S (S (S (twice O)))) = 
S (S (S (S O)))
*)

Fixpoint twice' (n : Nat) : Nat := match n with
| O => O
| S O => S (S O)
| S (S n) => S (S (S (S (twice' n))))
end.

(*
twice (S (S O)) = S (S (S (S (twice O)))) = S (S (S (S O)))
*)
(* HF: futasi ido kulonbseget talalni *)

Compute twice six.

Lemma SStwice : forall (n : Nat),
  S (S (S (twice n))) = S (twice (S n)).
Proof. simpl. intro. reflexivity. Qed.

Lemma lem1 : forall a, S a = S a.
Proof. intro. reflexivity. Qed.
Lemma lem2 (a : Nat) : S a = S a.
Proof. reflexivity. Qed.

Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.
(* f 3 = f (S(S(SO))) = f(S(SO)) = f(SO) = fO = O *)

Lemma lem3 (a : Nat) : f a = O.
(*
P(a) = (f a = 0)
1. P(0) = (f O = O) = (O = O)
2. n:Nat, P(n)        -> P(S n)
          (f n = O)      (f (S n) = O)
*)
Proof.
induction a.
* simpl. reflexivity.
* simpl. assumption.
Qed.

(* Fixpoint f (n : Nat) : Nat := f n. *)

Fixpoint plus (n m : Nat) {struct n} : Nat := match n with
| O => m
| S n' => (* n=S n'*) S (plus n' m) (*  (1+n')+m = 1+(n'+m) *)
end.

Compute plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

Lemma leftid (n : Nat) : O + n = n.
Proof. simpl. reflexivity. Qed.

Lemma rightid (n : Nat) : n + O = n.
Proof. simpl. induction n.
* reflexivity.
* simpl. rewrite -> IHn. reflexivity. Qed.

(* itt jelentkezz! *)
(*
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
*)

Inductive BinaryTree : Type :=
| Leaf (n : Nat)  (*  Leaf : Nat -> BinaryTree *)
| Node (l r : BinaryTree). (*  Node : BinaryTree -> BinaryTree -> BinaryTree *)

(*
   /\
  /\ 3
  0 1
*)
Definition aTree : BinaryTree := Node (Node (Leaf O) (Leaf (S O))) (Leaf (S(S(S O)))).

(*
Fixpoint height (t : BinaryTree) : Nat :=

Fixpoint leaves_count (t : BinaryTree) : Nat :=
*)

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
Proof.
(*
P(t) minden t-re:
1. P(Leaf n) teljesul minden n-re
2. ha van t1,t2 : BinaryTree, P(t1) -> P(t2) -> P(Node t1 t2)
*)
intro t.
induction t.
* simpl. reflexivity.
* simpl. rewrite -> IHt1. rewrite -> IHt2. (* ide kene, hogy az osszeadas kommutativ *)



(* assumption, rewrite, Fixpoint, intro, induction
meg egy taktika, amivel korabbi bizonyitasok felhasznalhatok: apply
 *)
