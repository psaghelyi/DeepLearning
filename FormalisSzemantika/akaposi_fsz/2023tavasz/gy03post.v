(* HF *)


Lemma pl (A B : Prop) : A /\ B -> (B /\ A) \/ A.
Proof. intro. destruct H. left. split.
* (*exact H0.*) assumption.
* assert (B -> A). 
** intro. assumption.
Qed.

Lemma egyszeru (A : Prop) : False -> A.
Proof. intro. (*  H : A *) destruct H. Qed.

(* 
        ->
        /  \
       es   vagy
       / \    / \
      A   B  es  A
             / \
             B  A


  logika Coq-ban:
                           (a cel ilyen alaku)(ha egy feltetel/egy korabbi lemma ilyen alaku)
  logikai osszekoto        bevezeto           eliminacios
  /\                       split              destruct
  \/                       left, right        destruct
  True                     split
  False                                       destruct
  ->                       intro              apply
  forall                   intro              apply
  exists                   exists             destruct
  =                        reflexivity        rewrite
  -------------------------------------------------------------
  akarmi, de cel=feltetel             assumption
  + assert



   Aritmetikai kifejezesnyelv es denotacios szemantika, pelda
   kiertekelesek 

    bin_tree, height, sum
    aexp, aeval, leaves_cnt, height

*)

From Coq Require Import Init.Nat.

Check nat.

Check 5.

Compute 1 + 3.

(* absztrakcios szintek*)

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
Definition t1 : AExp := APlus (APlus (ALit 1) (ALit 2)) (ALit 3).

Check t1.
Check ((1 + 2) + 3).
(*
(*
Ird le, mint AExp elemet!
    +
   / \
  1   +
     / \
    2   3
*)
Definition t1' : AExp := 

(*
Ird le, mint AExp elemet!
    +
   / \
  3   +
     / \
    1  2
*)
Definition t1'' : AExp := 

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


(* Rajzold le! *)
Definition t3 := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).
Definition t3' := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).
*)
Compute 5 - 15. (* 5 - 15 = 0*)
Compute (ASub (ALit 5) (ALit 15)).  (*(ASub (ALit 5) (ALit 15)) != ALit 0 *)

(* notation AExp-re is *)

Notation "x + y" := (APlus x y) (at level 50, left associativity).
Notation "x - y" := (ASub x y) (at level 50, left associativity).
Coercion ALit : nat >-> AExp.

Definition ae : AExp := 2 + (3 - 1).
Compute ae.
Definition egySzam : nat := 2 + (3 - 1).
Compute egySzam.

Example egyenloseg : 1 + 1 = APlus (ALit 1) (ALit 1).
Proof. reflexivity. Qed. (* ez csak pretty printing, semmi lenyeges. *)

(* az AExp kifejezesnyelv denotacios szemantikaja *)
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

Compute t1.
Compute aeval t1.
(*Compute aeval t2.*)

Fixpoint leaves_count (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 => leaves_count a1 + leaves_count a2
| ASub a1 a2 =>  leaves_count a1 + leaves_count a2
end
.

Compute leaves_count t1.
(*Compute leaves_count t3'.*)

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof. simpl. intro. intro. Check Nat.add_comm. apply Nat.add_comm. Qed.

(* kovetkezo gyakorlat 2 perccel rovidebb, nezzuk meg assert-ot *)
