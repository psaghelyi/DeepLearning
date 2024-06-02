(*
string        "1+1"    "1a+1"  "+1 1"  "1 + 1"  "(1+1)"
lex el. sor.  [1,+,1]  ------  [+,1,1] [1,+,1]   [(,1,+,1,)]
AST              +
                 /\            -------            ==
                1  1
ABT          nincs "\x.x+y"          "\x.x" = "\y.y"
WTT          nincs "true+3"
ALG                                  "1+1" = "2"
HOAS
*)

Inductive AExp : Type :=
| ALit (n : nat)
| ASub (a1 a2 : AExp)
| APlus (a1 a2 : AExp).
(*
P : AExp -> Prop                          P : nat -> Prop
P a = (aeval (optim a) = aeval a)

- forall n, P (ALit n)                    P zero
- P a1 -> P a2 -> P (APlus a1 a2)         P n -> P (suc n)
- P a1 -> P a2 -> P (ASub  a1 a2)
---------------------------------         ----------------
forall a, P a                             forall n, P n
*)


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

Lemma exExpProp : height exExp = 1. reflexivity. Qed.
  
(*
Tactic reminder:

           Goal             Hypothesis
           INTRODUCTION     ELIMINATION
True       split
False                       destruct
/\         split            destruct
\/         left, right      destruct
->         intro            apply
forall     intro            apply
exists     exists           destruct

others:
assert
discriminate
simpl
*)

Example expWithProperty : exists (a : AExp), leaves a = 3 /\ height a = 2.
exists (APlus (APlus (ALit 0) (ALit 0)) (ALit 0)). simpl.
split; reflexivity. Qed.

(*
f(x,y) := f x y
f(x+y, g(z, 1)) := f (x+y) (g z 1)
*)

Example notPoss : 
  not (exists (a : AExp), leaves a = 2 /\ height a = 0).
unfold not. intro. destruct H. destruct x.
- (* ALit *) simpl in H. destruct H. discriminate H.
- (* APlus *) simpl in H. destruct H. discriminate H0.
- (* ASub *) simpl in H. destruct H. discriminate H0.
Qed.

(*  [[_]] : Syntax -> Semantics
            AExp      nat
 *)
Fixpoint aeval (a : AExp) : nat :=
  match a with
  | ALit n      => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | ASub  a1 a2 => aeval a1 - aeval a2
  end.

Compute aeval exExp.

Fixpoint optim (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus e1 e2 => match e2 with
    | ALit n => match n with
      | O => optim e1
      | _ => APlus (optim e1) (optim e2)
      end
    | _ => APlus (optim e1) (optim e2)
    end
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.

Compute aeval (optim exExp).

Require Import Coq.Arith.Plus.

Check plus_0_r.

Lemma optim_sound (a : AExp) :
  aeval (optim a) = aeval a.
Proof. induction a.
  - (* a = ALit *)
    simpl. reflexivity.
  - (* a = ASub *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* a = APlus *)
    simpl. destruct a2.
    + (* a2 = ALit *)
      simpl.
      destruct n.
      * (* n = 0 *)
        rewrite IHa1. symmetry. apply plus_0_r.
      * (* n = S n' *)
        simpl. rewrite IHa1. reflexivity.
    + (* a2 = APlus *)
      simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
    + (* a2 = ASub *)
      simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
Qed.

(* try, ; *)

Definition optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim e1) (optim e2)
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.

(*Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.*)

Definition optim'' a := ALit (aeval a).

Lemma optim''_sound (a : AExp) : aeval (optim'' a) = aeval a.
reflexivity. Qed.



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
