(* HF *)

Inductive Nat : Set :=
 | O : Nat
 | S : Nat -> Nat.
(* Nat = {O , S O, S (S O), S(S(S O)), ... }*)

Lemma haromnegy : S (S (S O)) <> S (S (S (S O))).
Proof. unfold not. intro. discriminate H. Qed.

(*
                     bevezeto               eliminacio
                     (ha ezt akarjuk        (ha van ilyen feltetel)
                     belatni, ez a Goal)  
----------------------------------------------------------------
A -> B               intro                  exact (f a) (ha f : A -> B)
                                            apply f
forall (x : N), A    intro                  apply
exists (x : N), A    exists                 destruct
A /\ B               split                  destruct
A \/ B               left, right            destruct
True                 split                  NINCS
False                NINCS                  destruct
"="                  reflexivity            rewrite

(a <> b) = not (a = b) = (a = b) -> False


                 left
-------------   ------->      ----------
Goal = A \/ B                 Goal = A


                 intro a       a : A
--------------   ------>       -------------
Goal = A -> B                  Goal = B


f : A -> B       apply f        f : A -> B
-----------      ------->       -------------
Goal = B                        Goal = A




*)

(* Aritmetikai kifejezésnyelv és denotációs szemantika, példa
   kiértékelések *)

(*From Coq Require Import Init.Nat.*)

Check nat.

Check 5.

Compute 1 + 3.

Search plus.
From Coq Require Import Arith.PeanoNat.
Search plus.
(*
metanyelv: Coq
objektumnyelv: majd a WHILE nyelv, most egy egyszeru kifejezesnyelv, AExp
*)

(* absztrakcios szintek*)

(* a ::= n | a1 + a2 | a1 - a2 *)
(* a ::= alit(n) | plus(a1,a2) | sub(a1,a2)*)
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
Definition t1 : AExp := APlus (APlus (ALit 1) (ALit 2)) (ALit 3).

(*
Ird le, mint AExp elemet!
    +
   / \
  1   +
     / \
    2   3
*)
Definition t1' : AExp := APlus (ALit 1) (APlus (ALit 2) (ALit 3)).

Example t1t1' : t1 <> t1'.
Proof. unfold not. intro. discriminate H. Qed.

Example masik : (1 + 2) + 3 = 1 + (2 + 3).
Proof. simpl. reflexivity. Qed.

Check t1. Check (1 + 3) + 4.

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
(*
      -
     / \
    +   42
   / \
  5   7
*)
Definition t3' := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).

Compute 5 - 15.

(* notation AExp-re is *)

(* denotacios szemantika 
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

(* f injektiv, ha f x = f y -> x = y *)

Lemma nemInj : not (forall a1 a2, aeval a1 = aeval a2 -> a1 = a2).
Proof. unfold "~". intro. assert (t1 = t1') as I. apply H. 
simpl. reflexivity. (*discriminate H0.*)
apply t1t1'. exact I. Qed.

(* be kell latni C-t, es be tudod latni B-bol C-t. es van A-d.
assert B.
A ---> B ---> C
*)

(* t1 <> t1' = (t1 = t1' -> False) *)

Example balId' :     forall (a : nat),  0 + a = a.
Proof. simpl. reflexivity. Qed.

Example balId : not (forall (a : AExp), APlus (ALit 0) a = a).
unfold "~". intro. assert ((APlus (ALit 0) (ALit 1)) = (ALit 1)).
exact (H (ALit 1)). discriminate H0. Qed.

(*
Example balIdErosebb : forall (a : AExp), APlus (ALit 0) a <> a.
Proof. intro. induction a.
* intro H. discriminate H.
* intro H.
*)
(*
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.
   +                +
  / \              / \  
  0  +       =    a1  a2
     /\           
    a1 a2

P(a) = (APlus (ALit 0) a) <> a

forall n, P(ALit n)
forall a1, a2, P(a1)/\P(a2) -> P(APlus a1 a2)
forall a1, a2, P(a1)/\P(a2) -> P(ASub  a1 a2)
----------------------------------------------
forall (a : AExp), P(a)

*)

(*
S n = S m -> n = m
*)


(*  +
   /\
  0  +
     /\
    0  +
       /\
       0 +
         ...
*)

(*                     forall (n : nat),  S n <> n              *)



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
intros. simpl. Search plus. apply Nat.add_comm. Qed.



Inductive T : Set :=
  | Leaf : T
  | Node : (nat -> T) -> T.
(*
   Node
   /  |  \   \
  /0  |1  \2  \3 ....
 Node Leaf
*)

Set Primitive Projections.
CoInductive Tinf : Set := tinf { des : nat * (Tinf * Tinf) + unit }.
(*
    1
   /  \
  2    3                 3
  /\  / \                /\
 4 5  6  7              1
/\ /\ /\ /\             /\
...                       1
                          /\
                            1
                            /\
                              1
                              /\
                               ...
*)
