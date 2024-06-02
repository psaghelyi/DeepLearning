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

Reserved Notation "e , s => e'" (at level 50).
Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :
    var x , s => lit (s x)
  | eval_plus_lhs (e1 e2 e1' : exp)(s : state) :
    e1 , s => e1' ->
    plus e1 e2 , s => plus e1' e2
  | eval_plus_rhs (e2 e2' : exp)(s : state)(n : nat) :
    e2 , s => e2' ->
    plus (lit n) e2 , s => plus (lit n) e2'
  | eval_plus_fin (n m : nat)(s : state) :
    plus (lit m) (lit n) , s => lit (m + n)
  where "e , s => e'" := (evalo e s e').

Reserved Notation "e , s =>* e'" (at level 50).
Inductive evalo_rtc : exp -> state -> exp -> Prop :=
  | eval_refl (e : exp)(s : state) : 
    e , s =>* e
  | eval_trans (e e' e'' : exp)(s : state) :
    e , s => e'    ->    e' , s =>* e'' ->
    e , s =>* e''
  where "e , s =>* e'" := (evalo_rtc e s e').

(* haladas tetele *)
Lemma progress (e : exp)(s : state) : (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.
induction e.


Lemma determ : forall (e e0 : exp)(s : state), 
  e , s => e0 -> forall e1, e , s => e1 -> e0 = e1.
intros e e' s H. induction H.



(* reflexiv, _tranzitiv_ lezart *)
Lemma trans (e e' e'' : exp)(s : state) : e , s =>* e' -> e' , s =>* e'' -> e , s =>* e''.

Definition eval_singl (e e' : exp)(s : state) : e , s => e' -> e , s =>* e'.


Lemma eval_plus_lhs_rtc (e1 e1' e2 : exp)(s : state) : e1 , s =>* e1' ->
  plus e1 e2 , s =>* plus e1' e2.


Lemma eval_plus_rhs_rtc (n : nat)(e2 e2' : exp)(s : state) : e2 , s =>* e2' -> 
  plus (lit n) e2 , s =>* plus (lit n) e2'.


Lemma operDenot (e : exp)(s : state) : e , s =>* lit (eval e s).


Lemma totality (e : exp)(s : state) : exists (n : nat), e , s =>* lit n.


Lemma determ_rtc (e e0 : exp)(s : state) : 
  e , s =>* e0 /\ (exists n0, e0 = lit n0) -> 
  forall e1, e , s =>* e1 /\ (exists n1, e1 = lit n1) -> e0 = e1.


Lemma denotVsOper (e : exp)(s : state)(n : nat) : eval e s = n <-> e , s =>* lit n.

