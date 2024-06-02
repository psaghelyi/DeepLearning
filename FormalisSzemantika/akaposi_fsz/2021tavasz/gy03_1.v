Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Fixpoint twice (n : Nat) : Nat :=
  match n with
  | O => O
  | S n => S (S (twice n))
  end.

Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Lemma plus_r_s : forall (a b : Nat), plus (S a) b = plus a (S b).
Proof. intros. induction a.
  - reflexivity.
  - simpl. simpl in IHa. rewrite -> IHa. reflexivity.
Qed.

Lemma twice_prop (a : Nat) : twice a = plus a a.
(* END FIX *)
(* Tanacs: hasznald a plus_r_s-t az induktiv lepesben! *)
Proof. induction a.
* simpl. reflexivity.
* simpl. rewrite -> IHa. Check (plus_r_s a a).
  rewrite <- (plus_r_s a a). simpl. reflexivity.
Qed.
(*
S (S (a + a)) = S (a + S a)
S (S (a + a)) = S (S a + a)
S (S (a + a)) = S (S (a + a))
*)

(* HF *)

Definition pred (n : Nat) : Nat :=
  match n with
  | O => O
  | S n => n
  end.

Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.
Proof. intro. rewrite -> H. reflexivity. Qed.

Lemma S_inj (a b : Nat) : S a = S b -> a = b.
Proof. intro. assert (pred (S a) = pred (S b)).
* exact (cong pred (S a) (S b) H).
* simpl in H0. exact H0. Qed.
(* Use cong pred!    
f(g x,y,z)    felel meg  f (g x) y z
f(g,x,y,z)    felel meg  f g x y z

S a = S b
pred (S a) = pred (S b)
a          = b
*)

Definition P : Nat -> Prop := fun n =>
  match n with
  | O => True
  | S _ => False
  end.
(* P O = True
   P _ = False *)

Compute (P (S (S O))).
Compute (P O). 

Lemma congP (f : Nat -> Prop)(a b : Nat) : a = b -> f a = f b.
Proof. intro. rewrite -> H. reflexivity. Qed.

Lemma O_S_disj (a : Nat) : O <> S a.
Proof. unfold not. intro. assert (P O = P (S a)).
exact (congP P O (S a) H).
simpl in H0. rewrite <- H0. trivial. Qed.
(* O = S a
P O  = P (S a)
True = False
(a > 5)
(5 < a)
 *)
(* discriminate H. *)

(*            bevezetes          eliminalas
              (ha ez a Goal)     (ha ez a feltetel)
->            intro              apply   (exact (H ...))
forall        intro              apply
/\            split              destruct
\/            left, right        destruct
exists        exists             destruct
False         nincs              destruct
True          trivial            nincs

               H : A
------         -----
A -> B         B

1 = 2 -> False  <- igy irjuk le Coq-ban, hogy 1 <> 2.
(0 <> S a)      (0 = S a) -> False
not A = (A -> False)
a <> b = not (a = b) = (a = b) -> False.
*)

Lemma hamisbolMinden : False -> (O = S (S O)).
Proof. intro. destruct H. Qed.

Lemma valamibolHamis : (O = S (S O)) -> False.
intro. discriminate H. Qed.


(* Aritmetikai kifejezésnyelv és denotációs szemantika, példa
   kiértékelések *)

From Coq Require Import Init.Nat.

Check nat.

Check 5.

Compute 1 + 3.


Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).
(*   a ::= n       | a1 + a2     | a1 - a2      *)
(*   a ::= alit(n) | plus(a1,a2) | sub(a1,a2) *)

Check ASub.

(* Checkek *)
(* (5 + 7) - 42 *)
Check (ASub (APlus (ALit 5) (ALit 7)) (ALit 42)).
(*
Ird le, mint AExp elemet!
    -
   / \
  +   42
 / \
5  7
*)
Compute ((5 + 7) - 42).
(*
metanyelv = Coq                                            matematika
objektumnyelv = aritmetikai kifejezesek nyelve             prog.nyelv, amit tanulmanyozunk
*)

(*
Ird le, mint AExp elemet!
    +
   / \
  +   3
 / \
1  2
*)
Definition t1 : AExp := APlus (APlus (ALit 1) (ALit 2)) (ALit 3).

(*
Ird le, mint AExp elemet!
    +
   / \
  1   +
     / \
    2   3
*)
Definition t1' : AExp := APlus (ALit 1) (APlus (ALit 2) (ALit 3)) .

Lemma t1t1' : t1 <> t1'.
Proof. unfold not. intro. discriminate H. Qed.

(*
Ird le, mint AExp elemet!
    +
   / \
  3   +
     / \
    1  2
*)
Definition t1'' : AExp := APlus (ALit 3) (APlus (ALit 1) (ALit 2)).

(*
Ird le, mint AExp elemet!
     -
   /  \
  +    +
 / \   /\
1  2  +  3
     / \
    4  5
*)
Definition t2 : AExp :=
  ASub
   (APlus
     (ALit 1)
     (ALit 2))
   (APlus
     (APlus
       (ALit 4)
       (ALit 5))
     (ALit 3)).

(* Rajzold le! *)
Definition t3 := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).
Definition t3' := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).

Compute 5 + 15.
Compute (APlus (ALit 5) (ALit 15)).

(* denotacios szemantika
 [[_]]  szemantikus lekepezes
 [[_]] : AExp -> nat
 *)
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

Compute aeval t1.
Compute aeval t2.

Compute aeval (ASub (APlus (ALit 5) (ALit 7)) (ALit 3)).
Compute ((5 + 7) - 3).

Fixpoint leaves_count (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 => leaves_count a1 + leaves_count a2
| ASub a1 a2 =>  leaves_count a1 + leaves_count a2
end.

Compute leaves_count t1.
Compute leaves_count t2.

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
intros. simpl. Search "+". apply Nat.add_comm. Qed.


(* assert, simpl in , discriminate(induktiv tipus kulonbozo konstruktorati kulonbozok) *)
