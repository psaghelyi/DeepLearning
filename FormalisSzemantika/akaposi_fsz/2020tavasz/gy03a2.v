Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Inductive BinaryTree : Type :=
| Leaf (n : Nat)
| Node (l r : BinaryTree).

Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y)
  (at level 50, left associativity).


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

Lemma plus_rid :
  forall n : Nat, n + O = n.
Proof.
  intro.
  induction n as [|n'].
    (* n = O *)  (* would also work: *)
    simpl.       (* apply plusn_lid. *)
    reflexivity.
    (* n = S n', n' + O = n' *)
    simpl.         (* would also work: *)
    rewrite IHn'.  (* apply S_cong.    *)
    reflexivity.   (* apply IHn'.      *)
Qed.

Lemma plus_r_S :
  forall n m : Nat, n + S m = S (n + m).
Proof.
  intros. induction n.
  * simpl. reflexivity.
  * simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_comm : forall a b : Nat, a + b = b + a.
Proof.
  intros. induction a.
  * simpl. rewrite plus_rid. reflexivity.
  * simpl. rewrite plus_r_S. rewrite IHa. reflexivity. 
Qed.

Lemma sum1_2_eq : forall t : BinaryTree, sum1 t = sum2 t.
Proof.
  intros. induction t.
  * simpl. reflexivity.
  * simpl. rewrite <- IHt1. rewrite IHt2. rewrite plus_comm. reflexivity.
Qed.

(* InnentĹl kezdve hasznĂĄljuk az STDLB NAT-jĂĄt *)
(* Aritmetikai nyelv formalizĂĄlĂĄsa, BNF: *)
(*a ::= n | a1 + a2 | a1 - a2*)
(*a ::= alit(n) | plus(a1,a2) | sub(a1,a2)*)
Inductive AExp : Type :=
.

(* Checkek *)

(* Hogyan tudunk kiĂŠrtĂŠkelni aritmetikai kifejezĂŠseket --> denotĂĄciĂłs szemantika *)
Fixpoint aeval (a : AExp) : nat :=
.

Fixpoint leaves_count (a : AExp) : nat := 
.

Definition myA1 := .
Definition myA2 := .

Eval compute in leaves_count(myA1).
Eval compute in leaves_count(myA2).

Lemma leaf_l_r: .
Proof.

Qed.