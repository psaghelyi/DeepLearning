(*            bevezetes          eliminalas
              (ha ez a Goal)     (ha ez a feltetel)
->            intro               apply
forall        intro               apply
/\            split             destruct
\/            left, right       destruct
exists        exists            destruct
False                           destruct
True          split             
=             symetry           rewrite



Roviditesek: ~A = A -> False, (a <> b) = (a=b)->False
*)


Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

Definition t1 : AExp := APlus (APlus (ALit 1) (ALit 2))(ALit 3).

Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

Compute aeval t1.

Fixpoint leaves_count (a : AExp) : nat :=
match a with
 | ALit n => 1
 | APlus a1 a2 => leaves_count a1 + leaves_count a2
 | ASub a1 a2 => leaves_count a1 + leaves_count a2
end.

Compute leaves_count t1.

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof.
  intros. simpl.
  apply Nat.add_comm.
Qed.
(* Search "+". *)

Example balIdIsmert : forall (a : nat),  0 + a = a.
Proof.
  intros. simpl. reflexivity.
Qed.

Example balId : not (forall (a : AExp), APlus (ALit 0) a = a).
Proof.
  (* assert, discriminate *)
  intro.
  Check (H (ALit 1)).
  assert (leaves_count(APlus (ALit 0) (ALit 1)) = leaves_count(ALit 1)).
  - rewrite (H (ALit 1)). reflexivity.
  - simpl in H0. discriminate.

  (* unfold not. intros. specialize (H (ALit 1)). simpl in H. discriminate. *)
Qed.



Definition f : nat -> Prop := fun a => match a with
  | O => True
  | S _ => False
  end.

(* hasznald f-et! *)
Lemma discriminateOS (a : nat) : O <> S a.
Proof.
  unfold not. intro. discriminate.
Qed. 




Example balIdErosebb : forall (a  a' : AExp), APlus a' a <> a.
Proof.
  intro. induction a. intros.
  - discriminate.
  - intro. intro. inversion H. apply IHa2 with a1. assumption.
  - discriminate.
Qed.  
(* inversion *)

(* Fakultativ HF. Tipp: hasznald a pred fuggvenyt*)
Lemma inversionS (a b : nat) : S a = S b -> a = b.
Proof.
  intro. inversion H. reflexivity.
Qed.


Lemma nemInj : ~ (forall a1 a2, aeval a1 = aeval a2 -> a1 = a2).  
Proof.
  intro. assert (APlus (ALit 0) (ALit 0) = ALit 0).
  - apply H. simpl. reflexivity.
  - discriminate H0.
Qed.



Example notSubterm : forall (a b : AExp), APlus b a <> a.
Proof.
  intros. induction a.
  - discriminate.
  - intro. inversion H. rewrite <- H1 in H2. unfold not in IHa2. apply IHa2 in H2. assumption.
  - discriminate.
Qed.

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.

Check max.
Fixpoint height (a : AExp) : nat := 
  match a with
  | ALit n => 1
  | APlus a1 a2 => 1 + max (height a1) (height a2)
  | ASub a1 a2 => 1 + max (height a1) (height a2)
  end.

(*
Example expWithProperty : exists (a : AExp), leaves a = 3 /\ height a = 2.
Proof.
  exists (APlus (ALit 1) (APlus (ALit 2) (ALit 0))).
  split.
  - reflexivity.
  - reflexivity.
*)

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

Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim' e1) (optim' e2)
  | ASub  e1 e2 => ASub  (optim' e1) (optim' e2)
  end.

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.
Proof. induction a.
  - simpl. reflexivity.
  - simpl. destruct a2. simpl.
  -- destruct n.
  --- rewrite IHa1.


Definition optim'' a := ALit (aeval a).

Lemma optim''_sound (a : AExp) : aeval (optim'' a) = aeval a.

Check Nat.le_refl.
Check Nat.le_trans.
Check Nat.le_max_l.
Check Nat.le_max_r.
Check Nat.pow_le_mono.
Check Nat.add_le_mono.
Lemma leaves_height (a : AExp) : leaves a <= 2 ^ height a.

(* eddigi taktikak:
Inductive
Definition
Theorem
Lemma
Proof
Qed
Fixpoint
Admitted
Check

match
simpl
unfold (at 1, at 2)
reflexivity
destruct
assumption
rewrite
intro
induction
apply
 *)

(* ma:
Search
assert
...
simpl in
discriminate (induktiv tipus kulonbozo konstruktorati kulonbozok)
*)
