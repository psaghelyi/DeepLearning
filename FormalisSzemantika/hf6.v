Require Import Strings.String.

Inductive exp : Type :=
  | lit : nat -> exp
  | var : string -> exp
  | plus : exp -> exp -> exp.
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition state : Type := string -> nat.
Definition empty : state := fun x => 0.
Definition update (x : string)(n : nat)(s : state)
  : state := fun x' => match string_dec x x' with
  | left e  => n
  | right ne => s x'
  end.

Reserved Notation "e , s => e'" (at level 50).
Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :

    (*-------------------*)
    var x , s => lit (s x)

  | eval_plus_lhs (e1 e2 e1' : exp)(s : state) :

    e1 , s => e1' ->
    (*-------------------------*)
    plus e1 e2 , s => plus e1' e2

  | eval_plus_rhs (e2 e2' : exp)(s : state)(n : nat) :

    e2 , s => e2' ->
    (*-----------------------------------*)
    plus (lit n) e2 , s => plus (lit n) e2'

  | eval_plus_fin (n m : nat)(s : state) :

    (*------------------------------------*)
    plus (lit m) (lit n) , s => lit (m + n)

  where "e , s => e'" := (evalo e s e').

Example eval3 : exists s,
  plus (plus (var X) (lit 3)) (lit 2) , s => 
  plus (plus (lit 4) (lit 3)) (lit 2).

(* hasznalj inversion-t! *)
Example eval3' : ~ exists s,
  plus (plus (var X) (lit 3)) (lit 2) , s => 
  plus (plus (lit 4) (lit 3)) (lit 3).

(* hasznalj inversion-t! *)
Example eval4 : ~ exists s,
  plus (plus (lit 4) (lit 3)) (var Y) , s => 
  lit 7.

Example eval5 : exists s,
  plus (lit 3) (var Y) , s => 
  plus (lit 3) (lit 0).

Example eval6 : forall s,
  plus (lit 7) (lit 8) , s => 
  lit 15.

Example exStep : exists s,
  plus (lit 1) (plus (plus (plus (lit 2) (var X)) (lit 3)) (lit 4)) , s => 
  plus (lit 1) (plus (plus (plus (lit 2) (lit 5)) (lit 3)) (lit 4)).

Definition s : state 
  := empty. (* Ezt modositsd ugy, hogy eval7,eval8,eval9 bizonyithato legyen*)
Example eval7 : plus (var X) (var Y) , s => plus (lit 3) (var Y).

Example eval8 : plus (lit 3) (var Y) , s => plus (lit 3) (lit 4).

Example eval9 : plus (lit 3) (lit 4) , s => lit 7.


Lemma lem1 : ~ (exists e, lit 3 , empty => e).

Lemma lem2 : forall x m n s, 
  ~ (plus (var x) (lit n) , s => lit m).
