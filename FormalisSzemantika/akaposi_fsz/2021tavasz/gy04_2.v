Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).

Example pelda : 3 <> 4.
Proof. unfold not. intro. discriminate H. Qed.

Example pelda' : forall n, n <> S n.
Proof. intro. induction n.
- intro. discriminate H.
- intro. unfold not in IHn. inversion H. apply IHn. exact H1.
Qed.

(* inversion: induktiv tipusok konstruktorai injektivek *)

Example balIdAExp' : 
  forall (a : AExp), not (APlus (ALit 0) a = a).
intro. induction a.
- intro. discriminate H.
- intro. inversion H. unfold not in IHa2. apply IHa2. exact H2.
- intro. discriminate H.
Qed.

(*
eddigi taktikak:
1. unfold, simpl, exact, assert (strukturalis taktikak)
2. reflexivity, intro(s), split, exists, left, right (bevezeto taktikak: a Goal-tol fog)
3. rewrite, apply, destruct, induction (eliminacios: feltetelek felhasznalasa)
4. symmetry, discriminate, inversion, trivial, auto (osszetett, kenyelmi)
*)

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.

Check max.
Compute max 4 2.
Fixpoint height (a : AExp) : nat := match a with
  | ALit _ => 0
  | APlus a1 a2 => 1 + max (height a1) (height a2)
  | ASub  a1 a2 => 1 + max (height a1) (height a2)
  end.

Example expWithProperty : exists (a : AExp),
  leaves a = 3 /\ height a = 2.
Proof. exists (APlus (ASub (ALit 1) (ALit 1)) (ALit 1)).
simpl. split; reflexivity.
Qed.
(*  +
   /\
   - 1
  /\
  1 1
*)

Example notPoss : 
  not (exists (a : AExp), leaves a = 2 /\ height a = 0).
Proof. unfold not. intros. destruct H. destruct H. destruct x.
- simpl in H. discriminate H.
- simpl in H. simpl in H0. discriminate H0.
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

Compute optim (APlus (APlus (ALit 1) (ALit 0)) (ALit 0)).

Require Import Coq.Arith.Plus.
Check plus_0_r.
Lemma optim_sound (a : AExp) :
  aeval (optim a) = aeval a.
Proof. induction a.
- unfold optim. reflexivity.
- simpl. destruct a2. destruct n.
-- simpl. rewrite -> IHa1. Check plus_0_r. symmetry. apply plus_0_r.
-- simpl. rewrite -> IHa1. reflexivity.
-- simpl. simpl in IHa2. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
-- simpl. simpl in IHa2. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
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
/\  ---> (a+b)
a b
*)

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.
Proof. induction a.
- simpl. reflexivity.
- simpl. destruct a1; destruct a2;
  simpl; simpl in IHa1; simpl in IHa2;
  try (rewrite -> IHa1); try (rewrite -> IHa2); reflexivity.
- simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
Qed. 

Definition optim'' a := ALit (aeval a).

Lemma optim''_sound (a : AExp) : aeval (optim'' a) = aeval a.
Proof. simpl. reflexivity. Qed.
(*
 aeval (optim'' a) = aeval (ALit (aeval a)) = (aeval a)
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

