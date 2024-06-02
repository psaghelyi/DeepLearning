(*
  Közérdekű:
    Teams kód (konzultációhoz): 8vtszz1
    Konzultáció ideje: kedd, 14:15-15:45
    Konzultáció helye: D00-412 (hibrid, online is részt lehet venni)
*)
(* HF *)


(* Aritmetikai kifejezesnyelv es denotacios szemantika, pelda
   kiertekelesek 

    bin_tree, height, sum
    aexp, aeval, leaves_cnt, height

*)

(* From Coq Require Import Init.Nat. *)

Check nat.

Check 5.

(*
  +
 / \
1   3
 *)
Compute 1 + 3.

(* absztrakcios szintek - mi az a program? *)

(*
  - utasítás sorozat
  - szöveg
  - lexikális elemek sorozata
  - (absztrakt) szintaxisfa

 *)

(* 
  n számliterál - n ∈ N
  a ::= n | a1 + a2 | a1 - a2   <- BNF = Bachus Naur form *)

(*
  AExp := { 1, 2, 3, ..., 2 + 2, ..., 2 - 3, (2 - 3) - (2 + 2), ... }
 *)
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

(1 + 2) + 3
*)
Definition t1 : AExp :=
  APlus (APlus (ALit 1) (ALit 2)) (ALit 3).

(*
Ird le, mint AExp elemet!
    +
   / \
  1   +
     / \
    2   3

1 + (2 + 3)
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

((1 + 2) - ((4 + 5) + 3))
*)
Definition t2 : AExp :=
  ASub (APlus (ALit 1) (ALit 2))
       (APlus (APlus (ALit 4) (ALit 5)) (ALit 3)).

(* Rajzold le!

    -
   / \
  +   42
 / \
5   7

*)
Definition t3 := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).
Definition t3' := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).

Goal 1 + (2 + 3) = (1 + 2) + 3. (* (+) : nat -> nat -> nat *)
Proof.
  simpl. reflexivity.
Qed.

(* vs
 *)
Goal t1 = t1'. (* szintaxisfa egyenlőség *)
Proof.
  unfold t1, t1'.
  simpl. (* t1 és t2 is már értékek (szintaxisfák) *)
  Fail reflexivity.
Abort.

Compute 5 - 15.

(* notation AExp-re is *)
(*
  Kell egy interpreter/kiértékelő függvény AExp-ekre
  denotációs szemantika
 *)
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 (*                    v---- nat-ok közi/metaelméletbeli összeadás
    ⟦ a1 + a2 ⟧ = ⟦a1⟧ + ⟦a2⟧
         ^--- szintaktikus összeadás
 
 *)
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

(* kompozicionalitás elve:
   összetett kifejezések jelentése csak a részkifejezések
   jelentésétől függhet
   
   - Coq szempontjából is előnyös: így jól definiált a rekurzió
   - 
 *)
Compute aeval t1.
Compute aeval t2.

Fixpoint leaves_count (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 => leaves_count a1 + leaves_count a2
| ASub a1 a2 =>  leaves_count a1 + leaves_count a2
end.

Fixpoint middle_nodes_count (a : AExp) : nat :=
match a with
| ALit _ => 0
| APlus a1 a2 | ASub a1 a2 => 1 + middle_nodes_count a1 + middle_nodes_count a2
end.

Fixpoint nodes_count (a : AExp) : nat :=
match a with
| ALit _ => 1
| APlus a1 a2 | ASub a1 a2 => 1 + nodes_count a1 + nodes_count a2
end.

Compute leaves_count t1.
Compute leaves_count t3'.

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof.
  intros. simpl.
  Search "+" nat "comm".
  rewrite Nat.add_comm. reflexivity.
Qed.

Search (_ + 0 = _).

(* 
Lemma leaf_l_r2: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
 *)

Theorem nodes_count_equal :
  forall a : AExp,
    leaves_count a + middle_nodes_count a = nodes_count a.
Proof.
  intros.
  (* Strukturális indukció *)
  Check AExp_ind.
  induction a.
  * simpl leaves_count. simpl.
    reflexivity.
  * simpl.
    Search S plus.
    rewrite Nat.add_succ_r.
    rewrite Nat.add_assoc.
    rewrite <- (Nat.add_assoc (leaves_count a1)).
    (* HF *)
Qed.

Fixpoint leaves_count' (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 => 1 + leaves_count' a1 + leaves_count' a2
| ASub a1 a2 =>  1 + leaves_count' a1 + leaves_count' a2
end.

  