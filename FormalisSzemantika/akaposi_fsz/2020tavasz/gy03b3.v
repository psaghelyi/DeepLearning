

(*a ::= n | a1 + a2 | a1 - a2*)
(*a ::= alit(n) | plus(a1,a2) | sub(a1,a2)*)
Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

Definition myA1 := 
         APlus 
       (*/             \*)  
    (APlus 
(ALit 5) (ALit 7))   (ALit 42).
Definition myA2 := ALit 42.

Fixpoint leaves_count (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 => leaves_count a1 + leaves_count a2
| ASub a1 a2 => leaves_count a1 + leaves_count a2
end
.

Eval compute in leaves_count(myA1).
Eval compute in leaves_count(myA2).

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r : forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof.
  intros. simpl. Search "comm" plus. rewrite Nat.add_comm. reflexivity.
Qed.

Lemma leaf_l_r2 : forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof.
  intros. induction a1.
  * simpl. Search plus S. rewrite Nat.add_1_r. reflexivity.
  * simpl. rewrite Nat.add_comm. reflexivity.
  * simpl. rewrite Nat.add_comm. reflexivity.
Qed.

(* Checkek *)

Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end
.

Compute aeval myA1.
Compute aeval myA2.

Lemma alma : forall n m, aeval (APlus (ALit n) (ALit m)) = n + m.
Proof.
  simpl. reflexivity.
Qed.
