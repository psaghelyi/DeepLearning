
Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).

(*
           +
          /\
         /  \
        /    \
       /      \
      -        +
      /\       /\
     /  \     /  \
    0    1   +    5
            /\
           /  \
          2    3
*)
Definition exExp : AExp :=
  APlus
    (ASub
      (ALit 0)
      (ALit 1))
    (APlus
      (APlus
        (ALit 2)
        (ALit 3))
      (ALit 5)).

(*
eddigi taktikak:
1. simpl, unfold, exact, assert (strukturalis)
2. intro(s), exists, split, left, right, reflexivity (bevezet, Goal adott formaju)
3. apply, destruct, induction, rewrite (eliminal, feltetel adott formaju)
4. discriminate, inversion, trivial, auto, symmetry (osszetett, kenyelmi)
*)

Example pelda : forall n, n <> S n.
Proof. intro. induction n.
(*
P n = (n <> S n)

P 0
forall m, P m -> P (S m)
------------------------
P n
*)
- intro H. discriminate H. (* 0 = O, 1 = S O *)
- intro H. unfold not in IHn. apply IHn.
(* 1+a=1+b -> ?  a=b  
S n = S (S n) ->
pred (S n) = pred (S (S n)) ->
n = S n
*)
inversion H.
exact H.
Qed.

(* hasznald notSubterm-et! *)
Example balIdErosebb : forall (a : AExp),
  APlus (ALit 0) a <> a.
Proof.
intro. induction a.
- intro. discriminate H.
- intro. inversion H. unfold not in IHa2. apply IHa2. exact H2.
- intro. discriminate H.
Qed.

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.

Check max.
Compute max 30 4.
Fixpoint height (a : AExp) : nat := match a with
  | ALit n => 0
  | APlus a1 a2 => 1 + max (height a1) (height a2)
  | ASub a1 a2 => 1 + max (height a1) (height a2)
  end.

Example unittest : height (APlus (ALit 0) (ALit 1)) = 1.
simpl. reflexivity. Qed.
Example unittest' : height (APlus (ALit 0) (APlus (ALit 1) (ALit 1))) = 2.
simpl. reflexivity. Qed.

Example expWithProperty : 
  exists (a : AExp), leaves a = 3 /\ height a = 2.
Proof. exists (APlus (APlus (ALit 0) (ALit 0)) (ALit 0)). simpl.
split; reflexivity. Qed.

(*
 /\   /\         /\
/\     /\       /\/\
*)

Example notPoss : 
  not (exists (a : AExp), leaves a = 2 /\ height a = 0).
Proof. unfold not. intro.
destruct H. destruct H. destruct x.
- simpl in H. discriminate H.
- simpl in H0. discriminate H0.
- simpl in H0. discriminate H0.
Qed.

Fixpoint aeval (a : AExp) : nat :=
  match a with
  | ALit n      => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | ASub  a1 a2 => aeval a1 - aeval a2
  end.

(*  a + 0 = a *)
Fixpoint optim (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus e1 (ALit 0) => optim e1
  | APlus e1 e2 => APlus (optim e1) (optim e2)
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.
(*
  match a with
  | ALit n => ALit n
  | APlus e1 e2 => match e2 with
                   | ALit n => match n
                               | O => optim e1
                               | _ => APlus (optim e1) (optim e2)
                               end
                   | _      => APlus (optim e1) (optim e2)
                   end
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.
*)

Compute optim (APlus (APlus (ALit 1) (ALit 0)) (ALit 0)).
(*
  /\
 /\ 0  -->  1
1 0
*)

Require Import Coq.Arith.Plus.
Check plus_0_r.

Lemma optim_sound (a : AExp) :
  aeval (optim a) = aeval a.
Proof. induction a.
- unfold optim. reflexivity.
- simpl. destruct a2.
-- simpl. destruct n.
--- rewrite -> IHa1. symmetry. apply plus_0_r.
--- simpl. rewrite -> IHa1. reflexivity.
-- simpl. rewrite -> IHa1. simpl in IHa2. rewrite -> IHa2. reflexivity.
-- simpl. rewrite -> IHa1. simpl in IHa2. rewrite -> IHa2. reflexivity.
- simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
Qed.

Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim' e1) (optim' e2)
  | ASub  e1 e2 => ASub  (optim' e1) (optim' e2)
  end.
(*
+
/\    ->   3
1 2
*)

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.
Admitted.

Definition optim'' a := ALit (aeval a).

(*
  -
 / \            -
 -  3000   ->  / \
/ \           x   5000
x  2000
*)

Lemma optim''_sound (a : AExp) : aeval (optim'' a) = aeval a.
Proof. simpl. reflexivity. Qed.
(*
aeval (optim'' a) =
aeval (ALit (aeval a)) =
aeval a
*)

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
Proof. induction a.
- simpl. apply Nat.le_refl.
- simpl.



