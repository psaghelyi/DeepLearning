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

Example steps1 : plus (var X) (plus (var X) (lit 3)) , (update X 4 empty) =>* lit 11.
Admitted.

Definition e3 : exp := plus (lit 5) (plus (plus (plus (lit 2) (var X)) (lit 2)) (lit 3)).

Example e3eval1step : exists (e3' : exp), e3 , (update X 4 empty) => e3'.
Admitted.

(* gondolkozz, ennek lehet tobb megoldasa is! *)
Example e3eval : exists (e3' : exp), e3 , (update X 4 empty) =>* e3'.
Admitted.

Example e3eval' : exists (n : nat), e3 , (update X 4 empty) =>* lit n.
Admitted.

Definition eval_singl (e e' : exp)(s : state) : e , s => e' -> e , s =>* e'.
Admitted.

Example notPoss1 : forall s, ~ (plus (lit 1) (lit 2) , s => plus (lit 2) (lit 1)).
Admitted.

Example notPoss2 : forall s, ~ (plus (lit 1) (lit 2) , s => lit 2).
Admitted.

Example notPoss3 : forall s e x, ~ (e , s => var x).
Admitted.

Example notPoss4 : forall s e x, ~ (e , s => plus (var x) (lit 1)).
Admitted.

(* nehezebb, itt indukciora van szukseg *)
Example notPoss5 : forall e e' s, ~ (e , s => plus e e').
intro. induction e.
Admitted.

Example notPoss6 : forall n s x, ~ (lit n , s =>* var x).
Admitted.

(* hasznald notPoss6-ot! *)
Example notPoss7 : forall s, ~ (var X , s =>* var Y).
Admitted.

(* innentol small step operacios szemantika es denotacios szemantika ekvivalenciaja, fakultativ *)

(* haladas tetele *)
Lemma progress (e : exp)(s : state) : 
  (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.
Proof.
induction e.
- left. exists n. reflexivity.
- right. exists (lit (s s0)). apply eval_var.
- right. destruct IHe1.
-- destruct H. rewrite H. destruct IHe2.
--- destruct H0. rewrite H0. exists (lit (x + x0)). apply eval_plus_fin.
--- destruct H0. exists (plus (lit x) x0). apply eval_plus_rhs. assumption.
-- destruct H. exists (plus x e2). apply eval_plus_lhs. assumption.
Qed.

Lemma determ : forall (e e0 : exp)(s : state), 
  e , s => e0 -> forall e1, e , s => e1 -> e0 = e1.
Proof.
induction e; intros.
- inversion H; inversion H0.
- inversion H; inversion H0; reflexivity.
- inversion H; inversion H0; subst.
-- assert (e1' = e1'0).
--- apply IHe1 with s; assumption.
--- rewrite H1; reflexivity.
-- inversion H5.
-- inversion H5.
--  inversion H10.
-- assert (e2' = e2'0).
--- apply IHe2 with s.
---- assumption.
---- assumption.
--- rewrite H1. rewrite H6. reflexivity.
-- inversion H. inversion H4. inversion H4.
-- inversion H9.
-- inversion H9.
-- subst. inversion H6. subst. inversion H7. reflexivity.
Qed.


(* reflexiv, tranzitiv lezart tenyleg tranzitiv: *)
Lemma trans (e e' e'' : exp)(s : state) : e , s =>* e' -> e' , s =>* e'' -> e , s =>* e''.
Admitted.

Definition eval_singl (e e' : exp)(s : state) : e , s => e' -> e , s =>* e'.
Admitted.

Lemma eval_plus_lhs_rtc (e1 e1' e2 : exp)(s : state) : e1 , s =>* e1' ->
  plus e1 e2 , s =>* plus e1' e2.
Admitted.

Lemma eval_plus_rhs_rtc (n : nat)(e2 e2' : exp)(s : state) : e2 , s =>* e2' -> 
  plus (lit n) e2 , s =>* plus (lit n) e2'.
Admitted.

Lemma operDenot (e : exp)(s : state) : e , s =>* lit (eval e s).
Admitted.

Lemma totality (e : exp)(s : state) : exists (n : nat), e , s =>* lit n.
Admitted.

Require Import Coq.Program.Equality.

Lemma determ_rtc (e : exp)(s : state)(n0 : nat) : e , s =>* lit n0 -> forall n1, e , s =>* lit n1 -> n0 = n1.
Admitted.

Lemma denotVsOper (e : exp)(s : state)(n : nat) : eval e s = n <-> e , s =>* lit n.
Admitted.

