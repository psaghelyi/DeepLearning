(*
12 pontot lehet szerezni kiszh-kbol, minden kiszh 1.2 pontos
beadando. 7 pont
0-6 : 1
7-8 : 2
9-11 : 3
12-13 : 4
14-16 : 5
*)

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
apply eval_plus_rhs. apply eval_var. Qed.

Lemma lem1 : ~ (lit 3 , empty => lit 100).
intro. inversion H. Qed.

Lemma lem2 : forall n s, 
  ~ (lit n , s => plus (lit n) (lit 0)).
intro. intro. intro. inversion H. Qed.

Lemma notrefl' (e e' : exp)(s : state) : e , s => e' -> ~ (e = e'). 
Proof. intro. induction H.
- intro. inversion H.
- intro. inversion H0. unfold not in IHevalo. apply IHevalo. assumption.
- intro. inversion H0. apply IHevalo. assumption.
- intro. inversion H.
Qed.

Lemma notrefl (e : exp)(s : state) : ~ (e , s => e).
intro. assert (~ (e = e)). apply notrefl' with (s := s). assumption.
apply H0. reflexivity. Qed.

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
(*
-----------------eval_var                                  -----------------------------eval_plus_fin  ---------------eval_refl
var X,s => lit 4                                           plus(lit 4)(lit 3),s => lit 7               lit 7,s=>*lit 7
------------------------------------------eval_plus_lhs    -----------------------------------------------------------eval_trans
plus(var X)(lit 3),s => plus(lit 4)(lit 3)                 plus(lit 4)(lit 3),s =>* lit 7
---------------------------------------------------------------------------------------- eval_trans
   plus (var X) (lit 3) , s =>* lit 7
*)

Example steps2 : plus (var X) (plus (lit 1) (var X)) , (update X 4 empty) =>* lit 9.
apply eval_trans with (plus (lit 4) (plus (lit 1) (var X))).
- apply eval_plus_lhs; apply eval_var.
- apply eval_trans with (plus (lit 4) (plus (lit 1) (lit 4))).
-- apply eval_plus_rhs; apply eval_plus_rhs; apply eval_var.
-- apply eval_trans with (plus (lit 4) (lit 5)).
--- apply eval_plus_rhs; apply eval_plus_fin.
--- apply eval_trans with (lit 9).
---- apply eval_plus_fin.
---- apply eval_refl.
Qed.

Definition e3 : exp := plus (lit 5) (plus (plus (plus (lit 2) (var X)) (lit 2)) (lit 3)).


Example e3eval : exists (e3' : exp), e3 , (update X 4 empty) =>* e3'.
exists e3. apply eval_refl. Qed.

Example e3eval' : exists (n : nat), e3 , (update X 4 empty) =>* lit n.
exists 16.
apply eval_trans with (plus (lit 5) (plus (plus (plus (lit 2) (lit 4)) (lit 2)) (lit 3))).
- apply eval_plus_rhs; apply eval_plus_lhs; apply eval_plus_lhs; apply eval_plus_rhs; apply eval_var.
- apply eval_trans with (plus (lit 5) (plus (plus (lit 6) (lit 2)) (lit 3))).
-- apply eval_plus_rhs; apply eval_plus_lhs. apply eval_plus_lhs. apply eval_plus_fin.
-- apply eval_trans with (plus (lit 5) (plus (lit 8) (lit 3))).
--- apply eval_plus_rhs. apply eval_plus_lhs. apply eval_plus_fin.
--- apply eval_trans with (plus (lit 5) (lit 11)).
---- apply eval_plus_rhs. apply eval_plus_fin.
---- apply eval_trans with (lit 16).
----- apply eval_plus_fin.
----- apply eval_refl.
Qed.

(* haladas tetele *)
Lemma progress (e : exp)(s : state) : 
  (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.
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
intros e e0 s H. induction H. (* inversion, indukcios hipotezisek *)

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
