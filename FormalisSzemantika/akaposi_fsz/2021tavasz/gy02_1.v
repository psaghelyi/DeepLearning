
(* Fixpoint f (b : bool) : bool := f b. vegtelen rekurzio nincs *)
(* match b with true => false | _ => true end. *)

(* kell hozza: "destruct a eqn:H", rewrite *)
Lemma nehez (f : bool -> bool)(x : bool) : f (f (f x)) = f x.
Proof.
  destruct x.
  * (* x = true *)
    destruct (f true) eqn:H.
  ** (* f true = true *)
     rewrite -> H.
     exact H.
  ** (* f true = false *)
     destruct (f false) eqn:I.
  *** exact H.
  *** exact I.
  * (* x = false *)
    destruct (f false) eqn:H.
  ** destruct (f true) eqn:I.
  *** exact I.
  *** exact H.
  ** rewrite -> H. rewrite -> H. reflexivity.
Qed.

(*
bool -> bool
Bool
bool -> Maybe bool
f : A -> B
f x = f x
*)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

(* data Nat = O | S Nat *)

(* 
Definition isOne (n : Nat) : bool :=         *)
Definition isOne : Nat -> bool := fun n => 
  match n with
  | O => false
  | S O => true
  | S (S n) => false
  end.

(* fun-nal is *)

Compute isOne four.
Compute isOne six.
Compute isOne O.
Compute isOne (S O).

Fixpoint twice (n : Nat) : Nat := match n with
  | O => O
  | S n => S (S (twice n)) (* twice(1+n) = 2*(1+n) = 2*1+2*n = 2+2*n = 2+twice(n) = S (S (twice(n))) *)
  end.

(* twice (S (S O)) = S (S (twice (S O))) = S (S (S (S (twice O)))) = S (S (S (S O))) *)

Compute twice six.

Lemma SStwice : forall (n : Nat),
  S (S (S (twice n))) = S (twice (S n)).
(*  3+2*n = 1+(2*(1+n)) *)
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
(* kiserlet: f lassabb, mint f' *)
Compute f (twice (twice (twice (twice six)))).

(*Lemma f0 (a : Nat) : f a = O.*)
Lemma f0 : forall (a : Nat), f a = O.
Proof.
  intro.
(* teljes indukcio:
   ha be akarjuk latni P(n)-t minden n:Nat-ra, akkor:
   kell: P(O)
   kell: minden n-re, ha P(n), akkor P(S n) is teljesul
   ---------------------------------------
   minden n-re P(n)
*)
  induction a.
  (* 1. f O = O
     2. n  : N
        IH : f n = O
        -------------
        f (S n) = O
  *)
  * simpl. reflexivity.
  * simpl. exact IHa.
Qed.

(* Fixpoint f (n : Nat) : Nat := f n. *)

Fixpoint plus (m k : Nat) : Nat := match k with
  | O => m                (* plus_m(0)=m *)
  | S n => S (plus m n)   (* plus_m(S n) = S (plus_m(n)). *)
  end.
(*
A rekurziótétel alapján minden m:N-re létezik olyan
plus_m : Nat→Nat függvény, amelyre plus_m(0)=m, és minden
n:Nat-re plus_m(S n) = S (plus_m(n)).
*)

Compute plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).
Lemma leftid (n : Nat) : O + n = n.
Proof.
  induction n.
  * simpl. reflexivity. (* az n=0 esetben nyilvánvaló *)
  * simpl. rewrite -> IHn. reflexivity. (* Ekkor 0+n′=(0+n)′= n′, így az állítás minden n∈N-re teljesül *)
Qed.

Lemma rightid (n : Nat) : n + O = n.
Proof. reflexivity. Qed.
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
| Leaf (n : Nat)
| Node (l r : BinaryTree).
(* data BinaryTree = Leaf Nat | Node BinaryTree BinaryTree 

   /\
  /  \
 /\   0           0
/  \
0   1
*)

Definition ex : BinaryTree := Node (Node (Leaf O) (Leaf (S O))) (Leaf O).

(* Fixpoint height (t : BinaryTree) : Nat := *)

Fixpoint leaves_count (t : BinaryTree) : Nat := match t with
  | Leaf _ => S O
  | Node t1 t2 => leaves_count t1 + leaves_count t2
  end.

Compute leaves_count ex.

Lemma trivi (t : BinaryTree) : S (leaves_count t) =
   leaves_count (Node t (Leaf O)).
Proof.
  destruct t.
  * simpl. reflexivity.
  * simpl. reflexivity.
Qed.
(* nem kellett indukcio. *)

(*
  t        13


   /\
  /  \     14
 t    0
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


(* destruct a eqn:H, rewrite -> H, rewrite <- H*)
