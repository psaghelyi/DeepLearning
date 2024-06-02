Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).

Fixpoint aeval (a : AExp) : nat :=
  match a with
  | ALit n      => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | ASub  a1 a2 => aeval a1 - aeval a2
  end.

Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim' e1) (optim' e2)
  | ASub  e1 e2 => ASub  (optim' e1) (optim' e2)
  end.

Require Import Nat.
Require Import Arith.

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

Check Nat.le_refl.
Check Nat.le_trans.
Check Nat.le_max_l.
Check Nat.le_max_r.
Check Nat.pow_le_mono.
Check Nat.add_le_mono.

Lemma leaves_height (a : AExp) : leaves a <= 2 ^ height a.
induction a.
 * simpl. apply Nat.le_refl.
 * simpl.
   assert (leaves a1 + leaves a2 <= 
           2 ^ height a1 + 2 ^ height a2).
   Check Nat.add_le_mono.
   apply Nat.add_le_mono. exact IHa1. exact IHa2.
   rewrite -> plus_0_r.
   assert (2 ^ height a1 <= 
           2 ^ max (height a1) (height a2)).
   apply Nat.pow_le_mono. auto. apply Nat.le_refl. apply Nat.le_max_l.
   assert (2 ^ height a2 <= 
           2 ^ max (height a1) (height a2)).
   apply Nat.pow_le_mono. auto. apply Nat.le_refl. apply Nat.le_max_r.
   assert (2 ^ height a1 + 2 ^ height a2 <= 2 ^ max (height a1) (height a2) + 2 ^ max (height a1) (height a2)).
   apply Nat.add_le_mono. exact H0. exact H1.
   exact (le_trans _ _ _ H H2).
 * simpl.
   assert (leaves a1 + leaves a2 <= 
           2 ^ height a1 + 2 ^ height a2).
   Check Nat.add_le_mono.
   apply Nat.add_le_mono. exact IHa1. exact IHa2.
   rewrite -> plus_0_r.
   assert (2 ^ height a1 <= 
           2 ^ max (height a1) (height a2)).
   apply Nat.pow_le_mono. auto. apply Nat.le_refl. apply Nat.le_max_l.
   assert (2 ^ height a2 <= 
           2 ^ max (height a1) (height a2)).
   apply Nat.pow_le_mono. auto. apply Nat.le_refl. apply Nat.le_max_r.
   assert (2 ^ height a1 + 2 ^ height a2 <= 2 ^ max (height a1) (height a2) + 2 ^ max (height a1) (height a2)).
   apply Nat.add_le_mono. exact H0. exact H1.
   exact (le_trans _ _ _ H H2).
Qed.
