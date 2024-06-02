Require Import Coq.Strings.String.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (x : string)
  | APlus (a a' : aexp).

(* MULT ORA: Inductive claexp : Type :=
   | ANum (n : nat)
   | APlus (a a' : aexp).
Fixpoint embed : claexp -> aexp *)

Fixpoint closed (e : aexp) : bool :=
  match e with
  | ANum n => true
  | AVar x => false
  | APlus a a' => closed a && closed a'
  end.

Example ex1 : closed (APlus (ANum 3) (ANum 4)) = true. reflexivity. Qed.

Example ex2 : closed (APlus (ANum 3) (AVar "x")) = false. reflexivity. Qed.

Definition state : Type := string -> nat.

Fixpoint aeval (e : aexp)(s : state) : nat := match e with
  | ANum n => n
  | AVar x => s x
  | APlus a a' => aeval a s + aeval a' s
  end.

Definition F (b : bool) : Type :=
  if b then True else False.

Definition hamisbol (p : true = false) : False.
assert (F false). rewrite <- p. simpl. trivial.
simpl in X. exact X. Qed.

Require Import Coq.Bool.Bool.

Theorem closedEval (e : aexp)(s s' : state)(p : closed e = true) :
  aeval e s = aeval e s'.
induction e. simpl. reflexivity. simpl in p.
exfalso. apply hamisbol. symmetry. exact p.
simpl. simpl in p.
Check andb_true_iff.
apply andb_true_iff in p. destruct p as [H1 H2].
rewrite -> IHe1. rewrite -> IHe2. reflexivity.
exact H2. exact H1. Qed.

Inductive zart : aexp -> Prop :=
  | szam (n : nat) : zart (ANum n)
  | osszeg (a a' : aexp)(az : zart a)
           (a'z : zart a') : zart (APlus a a').

Example pl1 : zart (APlus (ANum 3) (ANum 4)).
apply osszeg. apply szam. apply szam. Qed.

Example pl3 : zart (APlus (ANum 3) 
                          (APlus (ANum 1) (ANum 2))).
apply osszeg. apply szam. apply osszeg; apply szam.
Qed.
(*exact (osszeg _ _ (szam _) (osszeg _ _ (szam _) (szam _))).*)

(*
Theorem zartEval (e : aexp)(s s' : state)(p : zart e) :
  aeval e s = aeval e s'.
*)

Inductive fstep : aexp -> state -> nat -> Prop :=
  | snum (n : nat)(s : state) : fstep (ANum n) s n
  | svar (x : string)(s : state) : fstep (AVar x) s (s x)
  | splus (n i : nat)(a2 : aexp)(s : state) :
          fstep a2 s i -> 
          fstep (APlus (ANum n) a2) s (n + i).

Notation "< a , s >=> i" := (fstep a s i) (at level 50).

Definition empty : state := fun _ => 0.

Example ex3 : < APlus (ANum 3) (ANum 4) , empty >=> 7.
apply (splus 3 4). apply snum. Qed.

Inductive step : aexp -> state -> aexp -> state -> Prop :=
  | splus2 (a1 a2 a1' : aexp)(s : state) :
           step a1 s a1' s -> 
           step (APlus a1 a2) s (APlus a1' a2) s.
(* TODO: tobbi eset *)


Notation "< a , s >=>< a' , s' >" := (step2 a s a' s') (at level 50).


