Require Import Strings.String.

(*

kiszh megoldasa:

Example steps : exists n , 
  plus (plus (lit 2) (lit 3)) (var X) , empty =>* lit n.
(* END FIX *)
exists 5.
apply eval_trans with (e' := plus (lit 5) (var X)).
- apply eval_plus_lhs.
-- apply eval_plus_fin.
- apply eval_trans with (e' := plus (lit 5) (lit 0)).
-- apply eval_plus_rhs.
--- apply eval_var.
-- apply eval_trans with (e' := lit 5).
--- apply eval_plus_fin.
--- apply eval_refl.
Qed.

*)


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

(* big step operational semantics *)

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
    (*----------------------------*)
    plus e1 e2 , s =v (n1 + n2)

  where "e , s =v n" := (evalb e s n).

Example ex1 : eval (plus (plus (var W) (var X)) (lit 100)) 
                     (update W 200 empty) = 300.
Proof. reflexivity. Qed.


Example ex1b : plus (plus (var W) (var X)) (lit 100) ,
                     update W 200 empty =v 300.
Proof. apply evalb_plus with (n1 := 200).
- apply evalb_plus with (n1 := 200).
-- apply evalb_var.
-- apply evalb_var.
- apply evalb_lit.
Qed.

Example ex2b : exists (n : nat),
  plus (plus (var X) (var Y)) (plus (lit 3) (var Z)) , 
  update X 3 (update Y 2 empty) =v n.
Proof.
exists 8.
apply evalb_plus with (n1 := 5).
- apply evalb_plus with (n1 := 3); apply evalb_var.
- apply evalb_plus with (n1 := 3).
-- apply evalb_lit.
-- apply evalb_var.
Qed.

Lemma denot2bigstep (e : exp)(s : state) : forall (n : nat), eval e s = n -> e , s =v n.
Proof.
induction e; intros; simpl in H; rewrite <- H.
- apply evalb_lit.
- apply evalb_var.
- apply evalb_plus with (n1 := eval e1 s).
-- apply IHe1. reflexivity.
-- apply IHe2. reflexivity.
Qed.

Lemma bigstep2denot (e : exp)(s : state) : forall (n : nat), e , s =v n -> eval e s = n.
Proof.
induction e; intros; simpl.
- inversion H. reflexivity.
- inversion H. reflexivity.
- inversion H. assert (eval e1 s = n1).
-- apply IHe1. assumption.
-- assert (eval e2 s = n2).
--- apply IHe2. assumption.
--- rewrite H6. rewrite H7. reflexivity.
Qed.

(* no need for induction. just use bigstep2denot! *)
Lemma determBigstep (e : exp)(s : state)(n : nat) : e , s =v n -> forall n', e , s =v n' -> n = n'.
Proof.
intros. assert (eval e s = n).
- apply bigstep2denot. assumption.
- rewrite <- H1. assert (eval e s = n').
-- apply bigstep2denot. assumption.
-- rewrite <- H2. reflexivity.
Qed.

Lemma bigstepVsdenot (e : exp)(s : state)(n : nat) : e , s =v n <-> eval e s = n.
Proof.
split; intros.
- apply bigstep2denot. assumption.
- apply denot2bigstep. assumption.
Qed.

Lemma notInvertible (n : nat)(s : state) : 
  exists (e e' : exp), e <> e' /\ e , s =v n /\ e' , s =v n.
Proof.
exists (lit n). exists (plus (lit 0) (lit n)). split.
- intro. inversion H.
- split.
-- apply evalb_lit.
-- apply evalb_plus with (n1 := 0); apply evalb_lit.
Qed.
