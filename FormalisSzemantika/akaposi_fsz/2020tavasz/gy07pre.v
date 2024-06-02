From Coq Require Import Strings.String.

Inductive exp : Type :=
| lit (n : nat)
| var (x : string)
| plus (e1 e2 : exp).

Definition state : Type := string -> nat.

Definition empty : state := fun x => 0.

Definition update (x:string)(n:nat)(s:state) : state :=
  fun x' => match string_dec x x' with
  | left  e => n
  | right e => s x'
  end.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Fixpoint evald (e : exp) : state -> nat := fun s => match e with
  | lit n => n
  | var x => s x
  | plus e1 e2 => evald e1 s + evald e2 s
  end.
Reserved Notation "e , s => e'" (at level 50).
Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :

    (*------------------*)
    var x , s => lit (s x)

  | eval_plus_lhs (e1 e2 e1' : exp)(s : state) :

          e1 , s => e1'           ->
    (*-------------------------*)
    plus e1 e2 , s => plus e1' e2

  | eval_plus_rhs (e2 e2' : exp)(s : state)(n : nat) :

             e2 , s => e2'                  ->
    (*-----------------------------------*)
    plus (lit n) e2 , s => plus (lit n) e2'

  | eval_plus_fin (n m : nat)(s : state) :

    (*-----------------------------------*)
    plus (lit m) (lit n) , s => lit (m + n)

  where "e , s => e'" := (evalo e s e').

Reserved Notation "e , s =>* e'" (at level 50).
Inductive evalo_rtc : exp -> state -> exp -> Prop :=
  | eval_refl (e : exp)(s : state) : 

    e , s =>* e

  | eval_trans (e e' e'' : exp)(s : state) :

    e , s => e'    ->    e' , s =>* e'' ->
    (*-------------------------------*)
    e , s =>* e''

  where "e , s =>* e'" := (evalo_rtc e s e').

Lemma progress (e : exp)(s : state) : (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.
Admitted.

Lemma determ (e e' : exp)(s : state) : e , s => e' -> forall e'', e , s => e'' -> e' = e''.
Admitted.

Definition eval_singl (e e' : exp)(s : state) : e , s => e' -> e , s =>* e'.
Admitted.

(* HF *)
Lemma trans (e e' e'' : exp)(s : state) : e , s =>* e' -> e' , s =>* e'' -> e , s =>* e''.
intros.
induction H.
  - exact H0.
  - apply (eval_trans _ _ _ _ H). apply IHevalo_rtc. exact H0.
Qed.

Lemma eval_plus_lhs_rtc (e1 e1' e2 : exp)(s : state) : e1 , s =>* e1' -> plus e1 e2 , s =>* plus e1' e2.
Admitted.

Lemma eval_plus_rhs_rtc (n : nat)(e2 e2' : exp)(s : state) : e2 , s =>* e2' -> 
  plus (lit n) e2 , s =>* plus (lit n) e2'.
Admitted.

Lemma operDenot (e : exp)(s : state) : e , s =>* lit (evald e s).
Admitted.

Lemma totality (e : exp)(s : state) : exists (n : nat), e , s =>* lit n.
Admitted.

Lemma determ_rtc (e : exp)(s : state)(n : nat) : e , s =>* lit n -> forall n', e , s => lit n' -> n = n'.
Admitted.

Lemma denotVsOper (e : exp)(s : state)(n : nat) : evald e s = n <-> e , s =>* lit n.
Admitted.

(* big-step operational semantics *)

Reserved Notation "e , s =v n" (at level 50).
Inductive evalb : exp -> state -> nat -> Prop :=
  | evalb_lit (n : nat)(s : state) :

    (*------------------*)
    lit n , s =v n

  | evalb_var (x : string)(s : state) :

    (*------------------*)
    var x , s =v s x

  | evalb_plus (n1 n2 : nat)(e1 e2 : exp)(s : state) :

    e1 , s =v n1  ->  e2 , s =v n2 ->
    (*---------------------------*)
    plus e1 e2 , s =v (n1 + n2)

  where "e , s =v n" := (evalb e s n).
(*
Fixpoint evald (e : exp) : state -> nat := fun s => match e with
  | lit n => n
  | var x => s x
  | plus e1 e2 => evald e1 s + evald e2 s
  end.
*)

Example ex1 : plus (plus (var W) (var X)) (lit 100) , update W 200 empty =v 300.
Admitted.

Example ex2 : exists (n : nat),
  plus (plus (var X) (var Y)) (plus (lit 3) (var Z)) , update X 3 (update Y 2 empty) =v n.
Admitted.

Lemma determBigstep (e : exp)(s : state)(n : nat) : e , s =v n -> forall n', e , s =v n' -> n = n'.
Admitted.

Lemma denot2bigstep (e : exp)(s : state) : forall (n : nat), evald e s = n -> e , s =v n.
Admitted.

Lemma bigstep2denot (e : exp)(s : state) : forall (n : nat), e , s =v n -> evald e s = n.
Admitted.

Lemma bigstepVsdenot (e : exp)(s : state)(n : nat) : e , s =v n <-> evald e s = n.
Admitted.

Lemma notInvertible (n : nat)(s : state) : exists (e e' : exp), e <> e' /\ e , s =v n /\ e' , s =v n.
Admitted.
