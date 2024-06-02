Definition name : Type := nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (x : name)
  | APlus (a a' : aexp).

Coercion ANum : nat >-> aexp.
Coercion AVar : name >-> aexp.
Notation "a1 +' a2" := (APlus a1 a2) (at level 50).

Definition W : name := 1.
Definition X : name := 2.
Definition Y : name := 3.
Definition Z : name := 4.

Definition state : Type := name -> nat.
Definition update (x : name)(n : nat)(s : state)
 : state := fun x' => if Nat.eqb x x' then n else s x'.
Definition empty : state := fun _ => 0.

Inductive fstep : aexp * state -> nat -> Prop :=
  | num (n : nat)(s : state) : fstep (ANum n , s) n
  | var (x : name)(s : state) : fstep (AVar x , s) (s x)
  | fplusr (n i : nat)(a2 : aexp)(s : state) :
           fstep (a2 , s) i -> 
           fstep (n +' a2 , s) (n + i).
Inductive step : aexp * state -> aexp * state -> Prop :=
  | plusl (a1 a2 a1t : aexp)(s : state) :
          step (a1 , s) (a1t , s) -> 
          step (a1 +' a2 , s) (a1t +' a2 , s)
  | fplusl (a1 a2 : aexp)(s : state)(i : nat) :
           fstep (a1 , s) i ->
           step (a1 +' a2 , s) (i +' a2 , s)
  | plusr (a2 a2t : aexp)(s : state)(n : nat) :
          step (a2 , s) (a2t , s) ->
          step (n +' a2 , s) (n +' a2t , s).

Notation "w f=> i" := (fstep w i) (at level 50).
Notation "w s=> w'" := (step w w') (at level 50).

Require Import Coq.Arith.Plus.

Lemma lem1 : (ANum 3 , empty) f=> 100 -> False.
intros. inversion H. Qed.

Lemma lem2 : forall n s1 s2 i, 
  (ANum n , s1) f=> i -> (ANum n , s2) f=> i.
intros. inversion H. apply num. Qed.

Fixpoint aeval (a : aexp)(s : state) : nat :=
  match a with
  | ANum n => n
  | AVar x => s x
  | APlus a1 a2 => aeval a1 s + aeval a2 s
  end.

Inductive bstep : aexp * state -> nat -> Prop :=
  | bnum (n : nat)(s : state) : bstep (ANum n , s) n
  | bvar (x : name)(s : state) : bstep (AVar x , s) (s x)
  | bsum (a1 a2 : aexp)(s : state)(n1 n2 : nat) :
      bstep (a1 , s) n1 -> 
      bstep (a2 , s) n2 ->
      bstep (a1 +' a2 , s) (n1 + n2).

Notation "w ˇ i" := (bstep w i) (at level 50).

Lemma todenot : forall a s n, (a , s) ˇ n -> aeval a s = n.
intros. generalize dependent n.
induction a.
  intros. inversion H. simpl. reflexivity.
  intros. inversion H. simpl. reflexivity.
  intros. simpl. inversion H.
    rewrite -> (IHa1 n1 H4).
    rewrite -> (IHa2 n2 H5).
    reflexivity.
Qed.


Lemma fromdenot : forall a s n, aeval a s = n -> (a , s) ˇ n.
Admitted.
 
