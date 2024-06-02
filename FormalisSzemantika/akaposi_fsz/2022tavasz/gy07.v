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
Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | plus e1 e2 => eval e1 s + eval e2 s
  end.
Definition empty : state := fun x => 0.
Definition update (x : string)(n : nat)(s : state)
  : state := fun x' => match string_dec x x' with
  | left e  => n
  | right ne => s x'
  end.

(* egy lepeses atiras relacio *)
Reserved Notation "e , s => e'" (at level 50).
Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :

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

    plus (lit m) (lit n) , s => lit (m + n)

  where "e , s => e'" := (evalo e s e').


Example step : plus (lit 3) (var X) , empty => plus (lit 3) (lit 0).
Admitted.

Lemma lem1 : ~ (lit 3 , empty => lit 100).
Admitted.

Lemma lem2 : forall n s, 
  ~ (lit n , s => plus (lit n) (lit 0)).
Admitted.

Require Import Coq.Program.Equality.

Lemma notrefl (e : exp) : ~ (e , empty => e).
intro. (* dependent induction H. *)
(*
P : exp -> Prop
forall n, P (lit n)
forall x, P (var x)
forall e1 e2, P e1 /\ P e2 -> P (plus e1 e2)
--------------------------------------------
forall e, P e

P e := (~ e, empty => e)
*)
induction e.
- inversion H.
- inversion H.
- inversion H.
-- (* H az a eval_plus_lhs-el jott letre *) apply IHe1. assumption.
-- (* H az eval_plus_rhs-el jott letre *) apply IHe2. assumption.
Qed.

(* tobb lepeses atiras relacio *)
Reserved Notation "e , s =>* e'" (at level 50).

Inductive evalo_rtc : exp -> state -> exp -> Prop :=
  | eval_refl (e : exp)(s : state) : 

    e , s =>* e

  | eval_trans (e e' e'' : exp)(s : state) :

    e , s => e'    ->    e' , s =>* e'' ->
    (*-------------------------------*)
    e , s =>* e''

  where "e , s =>* e'" := (evalo_rtc e s e').

Example steps1 : plus (var X) (lit 3) , (update X 4 empty) =>* lit 7.
apply eval_trans with (e' := plus (lit 4) (lit 3)).
- apply eval_plus_lhs. apply eval_var.
- apply eval_trans with (lit 7).
-- apply eval_plus_fin.
-- apply eval_refl.
Qed.

Example steps2 : plus (var X) (plus (lit 1) (var X)) , (update X 4 empty) =>* lit 9.
apply eval_trans with (plus (lit 4) (plus (lit 1) (var X))).
- apply eval_plus_lhs. apply eval_var.
- apply eval_trans with (plus (lit 4) (plus (lit 1) (lit 4))).
-- apply eval_plus_rhs. apply eval_plus_rhs. apply eval_var.
-- apply eval_trans with (plus (lit 4) (lit 5)).
--- apply eval_plus_rhs. apply eval_plus_fin.
--- apply eval_trans with (lit 9).
---- apply eval_plus_fin.
---- apply eval_refl.
Qed.
