Lemma nehez : forall (f : bool -> bool)(x : bool), f (f (f x)) = f x.
Proof.
intros.
destruct (f true) eqn:ftrue.
* destruct (f false) eqn:ffalse.
** destruct x.
*** rewrite -> ftrue. rewrite -> ftrue. exact ftrue.
*** rewrite -> ffalse. rewrite -> ftrue. exact ftrue.
** destruct x.
*** rewrite -> ftrue. rewrite -> ftrue. exact ftrue.
*** rewrite -> ffalse. rewrite -> ffalse. exact ffalse.
* destruct (f false) eqn:ffalse.
** destruct x.
*** rewrite -> ftrue. rewrite -> ffalse. exact ftrue.
*** rewrite -> ffalse. rewrite -> ftrue. exact ffalse.
** destruct x.
*** rewrite -> ftrue. rewrite -> ffalse. exact ffalse.
*** rewrite -> ffalse. rewrite -> ffalse. exact ffalse.
Qed.
(* kell hozza: "destruct a eqn:H", rewrite *)

(*
f :: Bool -> Bool
f True = False
-- nincs megadva, hogy f False = mi. 

f b = f b -- vegtelen ciklus, Coq-ban nincs
*)
(*
Definition nemmukodik (b : bool) : bool := match b with
  | true => false
  end.
*)
(*
Fixpoint f (b : bool) : bool := f b.
*)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

(*  {O}, {O, S O, S (S O), ...}
    {O}   O != S O
*)
(* Definition S' (n : Nat) : Nat := n. *)

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).
(*
Inductive F : Type :=
  | c : F
  | s : F -> F
  | s' : F -> F.
(* F = {c, s c, s' c, s (s' c), s' (s' c), ...} *)

Inductive T : Type :=
  | l : T
  | n : T -> T -> T.
(* T = {l, n l l, n (n l l) l, n (n l l) (n l l)}

  /\   /\     /\
      /\     /\/\
 *)

Inductive T' : Type :=
  | l' : Nat -> T'
  | n' : T' -> T' -> T'.
(* T' = {l' 0, l' 1, l' 2, l' 3, ..., n' (l' 0) (l' 1)}

   /\
  0  1
*)
*)
Definition isOne (n : Nat) : bool := match n with
  | O => false
  | S O => true
  | _ => false
  end.  

(* fun-nal is *)

Compute isOne four.
Compute isOne six.
Compute isOne O.
Compute isOne (S O).

Fixpoint twice (n : Nat) : Nat := match n with
  | O => O
  | S k => S (S (twice k)) (* twice (S k)=2*(1+k) = 2+(2*k) = SS(twice k) *)
  end.

Compute twice six.

Lemma SStwice : forall (n : Nat),
  S (S (S (twice n))) = S (twice (S n)).
(* 3+2*n = 1+2+2*n = 1+2*(1+n) *)
Proof. intro n. reflexivity. Qed.
(*
twice (S n) = 
match (S n) with
  | O => O
  | S k => S (S (twice k))
  end =
S (S (twice n))
*)

Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.
(*
f (S (S (S O))) = f (S (S O)) = f (S O) = f O = O
*)
Definition f' (n : Nat) : Nat := O.

Lemma fprop (a : Nat) : f a = O.
(* teljes indukcio:
P(0)
minden k-ra, ha P(k), akkor P(S k)
----------------------------------
minden n-re P(n)

P(n)    := (f n = 0)
1. P(0) =  (f O = O)
2. minden k-ra, ha f k = O, akkor f (S k) = O
*)
Proof. induction a.
* simpl. reflexivity.
* simpl. exact IHa.
Qed.

Lemma f'prop (a : Nat) : f' a = O.
Proof. unfold f'. reflexivity. Qed.

(* Fixpoint f (n : Nat) : Nat := f n. *)

(* S n = n′, 3 = O′′′ *)

(* rekurziótétel alapján minden m∈N-re létezik olyan s_m:N→N függvény: *)
Fixpoint plus (m n : Nat) : Nat := match n with
 | O => m (* s_m(0)=m *) (*  m + 0 = m *)
 | S n => S (plus m n)  (* s_m(n′) = (s_m(n))′ *) (* m+(1+n) = 1+(m+n) *)
 end.

Compute plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

(* 4.1.5 tetel, (2) pont *)
Lemma leftid (n : Nat) : O + n = n.
Proof. simpl. induction n.
* simpl. reflexivity.
* simpl. rewrite -> IHn. reflexivity.
Qed.

Lemma rightid (n : Nat) : n + O = n.
Proof. simpl. reflexivity.
Qed.
(*
Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c).
*)
Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.
Proof. intro e. rewrite -> e. reflexivity. Qed.

(*
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
| Leaf : Nat -> BinaryTree
| Node : BinaryTree -> BinaryTree -> BinaryTree
*)

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

(* destruct a eqn:H, rewrite -> *)

