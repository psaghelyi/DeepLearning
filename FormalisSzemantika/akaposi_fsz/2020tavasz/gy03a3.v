From Coq Require Import Init.Nat.

Check nat.

Check 5.

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

Definition myA1 := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).
Definition myA2 := ALit 2.

Compute 5 - 15.

(* Hogyan tudunk kiĂŠrtĂŠkelni aritmetikai kifejezĂŠseket --> denotĂĄciĂłs szemantika *)
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end
.

Compute aeval myA1.
Compute aeval myA2.

Fixpoint leaves_count (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 => leaves_count a1 + leaves_count a2
| ASub a1 a2 =>  leaves_count a1 + leaves_count a2
end
.

Eval compute in leaves_count(myA1).
Eval compute in leaves_count(myA2).

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof.
  intros.
  simpl. Search "+". rewrite Nat.add_comm. reflexivity.
Qed.

Lemma leaf_l_r2: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof.
  intros. induction a1.
  * simpl. (* S a = a + 1 *) Search "+" S. rewrite Nat.add_1_r. reflexivity.
  * simpl. rewrite Nat.add_comm. reflexivity.
  * simpl. rewrite Nat.add_comm. reflexivity.
Qed.