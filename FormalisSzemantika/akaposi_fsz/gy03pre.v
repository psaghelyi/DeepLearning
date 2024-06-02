(* HF *)


(* Aritmetikai kifejezesnyelv es denotacios szemantika, pelda
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


(*
Ird le, mint AExp elemet!
    +
   / \
  1   +
     / \
    2   3
*)
Definition t1' : AExp := APlus (ALit 1) (APlus (ALit 2) (ALit 3)).

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
Definition t2 : AExp := ASub (APlus (ALit 1) (ALit 2)) (APlus (ALit 4) (ALit 5)).


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
(*
    -
   / \
  +   42
 / \ 
5   7
*)

Goal 1 + (2 + 3) = (1 + 2) + 3.
Proof.
    simpl.
    reflexivity.
Qed.

Goal t1 = t1'.
Proof.
    unfold t1, t1'.
    simpl. Fail reflexivity.
Abort.


Compute 5 - 15.

(* notation AExp-re is *)


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
end.

Compute leaves_count t1.
Compute leaves_count t3'.


Fixpoint middle_nodes_count (a : AExp) : nat :=
match a with
| ALit n => 0
| APlus a1 a2 => 1 + middle_nodes_count a1 + middle_nodes_count a2
| ASub a1 a2 => 1 + middle_nodes_count a1 + middle_nodes_count a2
end.


Fixpoint middle_nodes_count' (a : AExp) : nat :=
match a with
| ALit n => 0
| APlus a1 a2 | ASub a1 a2 => 1 + middle_nodes_count' a1 + middle_nodes_count' a2
end.

Compute middle_nodes_count t1.
Compute middle_nodes_count' t1.

Fixpoint nodes_count (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 | ASub a1 a2 => 1 + nodes_count a1 + nodes_count a2
end.

Compute nodes_count t1.


From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof.
    intros. simpl. 
    Search "+" nat "com".
    rewrite Nat.add_comm. 
    reflexivity.
Qed.

Search (_ + 0 = _).

Theorem nodes_count_equal :
    forall a : AExp,
    leaves_count a + middle_nodes_count a = nodes_count a.
Proof.
    intros. 
    (* structural induction *)
    Check AExp_ind.
    induction a.
    - simpl. reflexivity.
    - simpl.                                        (* l1 + l2 + S (m1 + m2) = S (n1 + n2) *)
    Search S plus. 
    rewrite Nat.add_succ_r.                         (* S (l1 + l2 + (m1 + m2)) = S (n1 + n2) *)
    rewrite Nat.add_assoc.                          (* S (l1 + l2 + m1 + m2) = S (n1 + n2) *)
    rewrite <- (Nat.add_assoc (leaves_count a1)).   (* S (l1 + (l2 + m1) + m2) = S (n1 + n2) *)
    rewrite (Nat.add_comm (leaves_count a1)).       (* S (l2 + m1 + l1 + m2) = S (n1 + n2) *)
    rewrite <- (Nat.add_assoc (leaves_count a2)).   (* S (l2 + (m1 + l1) + m2) = S (n1 + n2) *)
    rewrite (Nat.add_comm (leaves_count a2)).       (* S (m1 + l1 + l2 + m2) = S (n1 + n2) *)
    rewrite <- Nat.add_succ_l.                      (* S (m1 + l1 + l2) + m2 = S (n1 + n2) *)
    rewrite <- Nat.add_succ_l.                      (* S (m1 + l1) + l2 + m2 = S (n1 + n2) *)
    rewrite <- (Nat.add_succ_l (nodes_count a1)).   (* S (m1 + l1) + l2 + m2 = S (n1) + n2 *)
    rewrite (Nat.add_comm(middle_nodes_count a1 )(leaves_count a1)).
    rewrite IHa1.
      

      rewrite <- (Nat.add_assoc (leaves_count a2)).
      



Lemma leaf_l_r2: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
