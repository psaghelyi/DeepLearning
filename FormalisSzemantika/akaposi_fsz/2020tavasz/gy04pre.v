Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).

Definition exTree : AExp :=

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

Example exExp : AExp :=

Lemma exExpProp : height exExp = 1.
  
(*
Tactic reminder:

           INTRODUCTION     ELIMINATION
True       trivial
False                       destruct
/\         split            destruct
\/         left, right      destruct
forall     intro            apply
exists     exists           destruct

others:
assert
discriminate
simpl
*)

Example expWithProperty : exists (a : AExp), leaves a = 3 /\ height a = 2.

Example notPoss : not (exists (a : AExp), leaves a = 2 /\ height a = 0).

Fixpoint aeval (a : AExp) : nat :=
  match a with
  | ALit n      => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | ASub  a1 a2 => aeval a1 - aeval a2
  end.

Compute aeval exTree.

Lemma eval_exExp : aeval exExp = 3.

Lemma eval_exExpWithProperty : aeval exExpWithProperty = 3.

Fixpoint optim (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus e1 (ALit 0) => optim e1
  | APlus e1 e2 => APlus (optim e1) (optim e2)
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.

Compute optim (aeval exTree).

Require Import Coq.Arith.Plus.

Check plus_0_r.

Lemma optim_sound (a : AExp) :
  aeval (optim a) = aeval a.

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
