Require Import Coq.Strings.String.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (x : string)
  | APlus (a a' : aexp).

Coercion ANum : nat >-> aexp.
Coercion AVar : string >-> aexp.
Notation "a1 +' a2" := (APlus a1 a2) (at level 50).

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition W : string := "W".

Definition state : Type := string -> nat.
Definition update (x : string)(i : nat)(s : state) : state := fun y =>
  if eqb x y then i else s y.
Definition empty : state := fun _ => 0.

Example exAexp : aexp := X +' (Y +' (2 +' Z)).

Inductive fstep : aexp * state -> nat -> Prop :=
  | num (n : nat)(s : state) : fstep (ANum n , s) n
  | var (x : string)(s : state) : fstep (AVar x , s) (s x)
  | fplusr (n i : nat)(a2 : aexp)(s : state) :
          fstep (a2 , s) i -> 
          fstep (n +' a2 , s) (n + i).

Notation "w f=> i" := (fstep w i) (at level 50).

Example ex1 : (3 +' 4 , empty) f=> 7.
apply (fplusr 3). apply num. Qed.

Example ex2 : (AVar X , update X 3 empty) f=> 3.
apply var. Qed.

Example ex3 : (ANum 3 , empty) f=> 3.
apply num. Qed.

Inductive step : aexp * state -> aexp * state -> Prop :=
  | plusl (a1 a2 a1' : aexp)(s : state) :
          step (a1 , s) (a1' , s) -> 
          step (a1 +' a2 , s) (a1' +' a2 , s)
  | fplusl (a1 a2 : aexp)(s : state)(i : nat) :
           (a1 , s) f=> i ->
           step (a1 +' a2 , s) (i +' a2 , s)
  | plusr (a2 a2' : aexp)(s : state)(n : nat) :
          step (a2 , s) (a2' , s) ->
          step (n +' a2 , s) (n +' a2' , s).

Notation "w => w'" := (step w w') (at level 50).

Definition st : state := update Y 12 (update Z 34 empty).

Example ex4a : ((Y +' 5) +' Z , st) => ((12 +' 5) +' Z , st).
apply plusl. apply fplusl. apply var. Qed.

Example ex4b : ((12 +' 5) +' Z , st) => (17 +' Z , st).
apply fplusl. apply (fplusr 12). apply num. Qed.

Example ex4c : (17 +' Z , st) f=> 51.
apply (fplusr 17). apply var. Qed.

Lemma determ (a : aexp)(s : state)(i j : nat)
  (p : (a , s) f=> i)(p' : (a , s) f=> j) : i = j.
generalize dependent j.
induction p.
intros. inversion p'. reflexivity.
intros. inversion p'. reflexivity.
intros. inversion p'. rewrite -> (IHp i0 H3). reflexivity. Qed.

Inductive fstept : aexp * state -> nat -> Prop :=
  | numt (n : nat)(s : state) : fstept (ANum n , s) n
  | vart (x : string)(s : state) : fstept (AVar x , s) (s x)
  | fplusrt (n i : nat)(a2 : aexp)(s : state) :
            fstept (a2 , s) i -> 
            fstept (n +' a2 , s) (n + i)
  | ftranst (w1 w2 : aexp * state)(i : nat) :
            stept w1 w2 -> fstept w2 i -> fstept w1 i
with stept : aexp * state -> aexp * state -> Prop :=
  | pluslt (a1 a2 a1t : aexp)(s : state) :
           stept (a1 , s) (a1t , s) -> 
           stept (a1 +' a2 , s) (a1t +' a2 , s)
  | fpluslt (a1 a2 : aexp)(s : state)(i : nat) :
            fstept (a1 , s) i ->
            stept (a1 +' a2 , s) (i +' a2 , s)
  | plusrt (a2 a2t : aexp)(s : state)(n : nat) :
           stept (a2 , s) (a2t , s) ->
           stept (n +' a2 , s) (n +' a2t , s)
  | transt (w1 w2 w3 : aexp * state) :
           stept w1 w2 -> stept w2 w3 -> stept w1 w3.

Notation "w f=>t i" := (fstept w i) (at level 50).
Notation "w =>t w'" := (stept w w') (at level 50).

(* (a,s) => (a,s) nem levezetheto *)

Example ex4 : ((Y +' 5) +' Z , st) f=>t 51.
apply (ftranst _ (17 +' Z , st)).
- apply fpluslt.
  apply (ftranst _ (12 +' 5 , st)).
  * apply fpluslt. apply vart.
  * apply (fplusrt 12 5). apply numt.
- apply (fplusrt 17 _ Z). apply vart.
Qed.

(*
FELADAT: atirni ugy, hogy a jobb oldal legyen eloszor kiertekelve
*)
