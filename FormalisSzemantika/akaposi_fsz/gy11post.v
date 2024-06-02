(*
0-6 : 1
7-8 : 2
9-11 : 3
12-13 : 4
14-16 : 5

beadando: 8 pont

TODO: kiszh-javitas lehet-e?

*)

(* gy01 *)

Lemma bool3 (f : bool -> bool)(x : bool) : f (f (f x)) = f x.
Proof. 
  destruct (f true) eqn:Htrue; 
  destruct (f false) eqn:Hfalse; 
  destruct x;
  try ( rewrite Htrue  );
  try ( rewrite Hfalse );
  try ( rewrite Htrue  );
  try ( rewrite Hfalse );
  try ( rewrite Htrue  );
  try ( rewrite Hfalse );
  reflexivity.
Qed.

(* gy3 *)

Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

Lemma egymeg0 : 1 + 0 = 1.
simpl. reflexivity. Qed.

Lemma egymeg0' : ~ (APlus (ALit 1) (ALit 0) = ALit 1).
unfold "<>". intro. discriminate H.
Qed.

Fixpoint eval (a : AExp) : nat := match a with
  | ALit n => n
  | APlus a1 a2 => eval a1 + eval a2
  | ASub a1 a2 => eval a1 - eval a2
  end.

Lemma egymeg0'' : eval (APlus (ALit 1) (ALit 0)) = eval (ALit 1).
Proof. simpl. reflexivity. Qed.

Fixpoint leaves_count (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 => leaves_count a1 + leaves_count a2
| ASub a1 a2 =>  leaves_count a1 + leaves_count a2
end.

Fixpoint leaves_count' (a : AExp) : nat :=
match a with
| ALit n => 0
| APlus a1 a2 => 1 + leaves_count' a1 + leaves_count' a2
| ASub a1 a2 =>  1 + leaves_count' a1 + leaves_count' a2
end.

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a : AExp,
  leaves_count a = 1 + leaves_count' a.
Proof. intro. 
(*
P : AExp -> Prop
forall n, P (ALit n)
forall a1 a2, P a1 -> P a2 -> P (APlus a1 a2)
forall a1 a2, P a1 -> P a2 -> P (ASub a1 a2)
---------------------------------------------
forall a, P a
*)
induction a.
- simpl. reflexivity.
- simpl. rewrite -> IHa1. rewrite -> IHa2. simpl.
  Search "+". 
  rewrite <- (Nat.add_succ_comm (leaves_count' a1)
    (leaves_count' a2)). simpl.
  reflexivity.
- simpl. rewrite -> IHa1. rewrite -> IHa2. simpl.
  rewrite <- (Nat.add_succ_comm (leaves_count' a1)
  (leaves_count' a2)). simpl.
  reflexivity.
Qed.

(* gy6 *)

Require Import Strings.String.

Inductive exp : Type :=
  | lit : nat -> exp
  | var : string -> exp
  | plus : exp -> exp -> exp.

Definition state : Type := string -> nat.
Definition empty : state := fun x => 0.
Definition update (x : string)(n : nat)(s : state)
  : state := fun x' => match string_dec x x' with
  | left e  => n
  | right ne => s x'
  end.

Reserved Notation "e , s => e'" (at level 50).
Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :

    var x , s => lit (s x)

  | eval_plus_lhs (e1 e2 e1' : exp)(s : state) :

    e1 , s => e1' ->
    (*-------------------------*)
    plus e1 e2 , s => plus e1' e2

  | eval_plus_rhs (e2 e2' : exp)(s : state)(n : nat) :

    e2 , s => e2' ->
    (*-----------------------------------*)
    plus (lit n) e2 , s => plus (lit n) e2'

  | eval_plus_fin (n m : nat)(s : state) :

    plus (lit m) (lit n) , s => lit (m + n)

  where "e , s => e'" := (evalo e s e').

Lemma notrefl (e : exp)(s : state) : ~ (e , s => e).
(* P e = ~ e , s => e *)
induction e; intro.
- inversion H.
- inversion H.
- inversion H. 
-- subst. apply IHe1. assumption.
-- subst. apply IHe2. assumption.
Qed.

(*
determinism gy10-bol

*)





