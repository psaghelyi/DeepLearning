(*
STRING   "1+1"      "1a+1"  "1++1"       "1 +1"   "((1)+1)"
LEX.ELS  [1,+,1]       -    [1,+,+,1]    [1,+,1]  [(,(,1,),+,1,)]

AST         +                   -                    +
            /\                                       /\
           1  1                                     1  1

ABT      nincs "\x.(x+y)" 
WTT      nincs "true+1"
Alg
HOAS
*)

Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).
(*
P : AExp -> Prop
P a := (aeval (optim a) = aeval a)

forall n, P (ALit n)
P a1 -> P a2 -> P (APlus a1 a2)
P a1 -> P a2 -> P (ASub  a1 a2)
-------------------------------
forall a, P a
*)


(*Definition exTree : AExp :=*)

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.

Fixpoint height (a : AExp) : nat := match a with
  | ALit n => 0
  | APlus a1 a2 => 1 + max (height a1) (height a2)
  | ASub a1 a2 => 1 + max (height a1) (height a2)
  end.

Example exExp : AExp := APlus (ALit 0) (ALit 0).

Lemma exExpProp : height exExp = 1.
Proof. simpl. reflexivity. Qed.
  
(*
Tactic reminder:

           Goal a log.ossz. Ha hipotezis
           INTRODUCTION     ELIMINATION
True       split
False                       destruct
A /\ B     split            destruct
A \/ B     left, right      destruct
->         intro            apply
forall     intro            apply
exists     exists           destruct

others:
assert
discriminate
simpl
trivial
auto

not A := A -> False
*)



Example expWithProperty : exists (a : AExp), leaves a = 3 /\ height a = 2.
exists (APlus (APlus (ALit 0) (ALit 0)) (ALit 0)). split. simpl. reflexivity.
simpl. reflexivity. Qed.

Example notPoss : 
  not (exists (a : AExp), leaves a = 2 /\ height a = 0).
unfold not. intro. destruct H. destruct x.
- simpl in H. destruct H. discriminate H.
- destruct H. simpl in H0. discriminate H0.
- destruct H. simpl in H0. discriminate H0.
Qed.

(* [[_]] : AExp -> nat *)
Fixpoint aeval (a : AExp) : nat :=
  match a with
  | ALit n      => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | ASub  a1 a2 => aeval a1 - aeval a2
  end.

Compute exExp.
Compute aeval exExp.

Lemma eval_exExp : aeval exExp = 0.
reflexivity. Qed.

(*  a + 0 = a *)
Fixpoint optim (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus e1 (ALit 0) => optim e1
  | APlus e1 e2 => APlus (optim e1) (optim e2)
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.

Compute optim exExp.
Compute aeval exExp.
Compute aeval (optim exExp).

Require Import Coq.Arith.Plus.

Check plus_0_r.

Lemma optim_sound (a : AExp) :
  aeval (optim a) = aeval a.
Proof. induction a.
  - simpl. reflexivity.
  - simpl. destruct a2.
    + destruct n.
      * simpl. rewrite -> IHa1. rewrite (plus_0_r (aeval a1)). reflexivity.
      * simpl. rewrite -> IHa1. reflexivity.
    + (*APlus*) simpl. simpl in IHa2.
      rewrite -> IHa1. rewrite -> IHa2. reflexivity.
    + (*ASub*) simpl. simpl in IHa2.
      rewrite -> IHa1. rewrite -> IHa2. reflexivity.
  - simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
Qed.
(*
  induction a;
  try (simpl; reflexivity);
  try (simpl; rewrite -> IHa1; rewrite -> IHa2; reflexivity);
  try (simpl; destruct a2;
    try (destruct n;
      try (simpl; rewrite -> IHa1; rewrite (plus_0_r (aeval a1));
           reflexivity);
      try (simpl; rewrite -> IHa1; reflexivity);
    try (simpl; rewrite -> IHa1; rewrite -> IHa2; reflexivity))).
*)
(*
  - simpl. reflexivity.
  - simpl. destruct a2.
    + destruct n.
      * simpl. rewrite -> IHa1. rewrite (plus_0_r (aeval a1)). reflexivity.
      * simpl. rewrite -> IHa1. reflexivity.
    + (*APlus*) simpl. simpl in IHa2.
      rewrite -> IHa1. rewrite -> IHa2. reflexivity.
    + (*ASub*) simpl. simpl in IHa2.
      rewrite -> IHa1. rewrite -> IHa2. reflexivity.
  - simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
Qed.
*)

(* try, ; *)

Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim e1) (optim e2)
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.

(* exercise: create more optimisations and prove them sound! *)
						   
Require Import Nat.
Require Import Arith.

(* standard library documentation *)

(* See Arith.Le *)

Check Nat.le_refl.
Check Nat.le_trans.
Check Nat.le_max_l.
Check Nat.le_max_r.
Check Nat.pow_le_mono.
Check Nat.add_le_mono.

Lemma leaves_height (a : AExp) : leaves a <= 2 ^ height a.

