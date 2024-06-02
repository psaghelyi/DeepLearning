(* HF *)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Fixpoint plus (n m : Nat) : Nat :=
  match m with
  | O => n (* 1 *)
  | S m' => S (plus n m') (*2*)
  end.
(*
Notation "x + y" := (plus x y) (at level 50, left associativity).

Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
Proof.
  intros. induction b.
- simpl. reflexivity.
- simpl. rewrite -> IHb. simpl. reflexivity.
Qed.
*)
(*
S a + O =(1) S a

a + S O =(2) S (a + O) =(1) S a
*)

(*
kerdeseket irjatok a tantargy chat-be!
*)

(*
jovo hettol fizikai jelenleti oktatas!
*)

(* 65. oldal: *)
(*
Fixpoint p (m : Nat)(n : Nat) : Nat := match n with
  | O => O
  | S n => p m n + m
  end.

Notation "x * y" := (p x y) (at level 40, left associativity).

Theorem plus_assoc : forall (k m n : Nat), (k + m) + n = k + (m + n).
Admitted.

Theorem thm4_1_6_1 : forall (k m n : Nat), k * (m + n) = k * m + k * n.
Proof.
 induction n.
- simpl. reflexivity.
- simpl. rewrite -> IHn. exact (plus_assoc (k * m) (k * n) k). 
(*apply plus_assoc.*) Qed.
*)
(*
         forall   ->       =             nat          barmi               /\  \/  True  False  exists
cel      intros   intros   reflexivity   O,S                              
feltelel apply    apply    rewrite       induction    assumption,exact    

k : nat
p : forall n : nat, S n = k         p : forall n : A, P n            p : A -> B
---------------------------         ---------------------            ----------
S 3 = k                             P m                              B

apply p
*)

Lemma lem_pelda (x y : nat) (q : x = 1)(p : x = 1 -> y = 2) : y = 2.
Proof. apply p. (*exact q.*) assumption. Qed.

(* Aritmetikai kifejezesnyelv es denotacios szemantika, pelda
   kiertekelesek *)

From Coq Require Import Init.Nat.

Check nat.

Check 5.

Compute (1 + 3).

(* absztrakcios szintek*)

(*
  3 + ((1 - 2) + 2)

        +
       / \
      3   +
         / \
         -  2
 ...

  3 + (1 - 2)
  3 + (1  - 2)

    +
   / \
  3   -
     / \
    1   2

  2
*)

(*a ::= n | a1 + a2 | a1 - a2*)
(*a ::= alit(n) | plus(a1,a2) | sub(a1,a2)*)
Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

(* Checkek *)
(* (5 + 7) - 42 *)
Check (ASub (APlus (ALit 5) (ALit 7)) (ALit 42)).

(*
Ird le, mint AExp elemet!
    +
   / \
  +   3
 / \
1  2
*)
Definition t1 : AExp := 
  APlus
    (APlus
      (ALit 1)
      (ALit 2))
    (ALit 3).

(*
Ird le, mint AExp elemet!
    +
   / \
  1   +
     / \
    2   3
*)
Definition t1' : AExp := 
  APlus (ALit 1) (APlus (ALit 2) (ALit 3)).

(*
Ird le, mint AExp elemet!
    +
   / \
  3   +
     / \
    1  2
*)
Definition t1'' : AExp :=
  APlus (ALit 3) (APlus (ALit 1) (ALit 2)).

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
(*
    -
   / \
  +   42
  /\
  5 7
*)
Definition t3' := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).
(*
    -
   / \
  +   42
  /\
  5 7
*)
(* itt jelentkezzel! *)

Compute (ASub (ALit 5) (ALit 15)).

Compute (5 - 15).

(* notation AExp-re is *)

(* idaig jutottunk *)

(* denotacios szemantika *)
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

Compute aeval t1.
Compute aeval t2.

Fixpoint leaves_count (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 => leaves_count a1 + leaves_count a2
| ASub a1 a2 =>  leaves_count a1 + leaves_count a2
end
.

Compute leaves_count t1.
Compute leaves_count t3'.

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).


Lemma leaf_l_r2: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).


(* Admitted, Check *)
