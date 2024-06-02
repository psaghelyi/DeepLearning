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

(* kiszh*)

Example steps : exists n , 
  plus (plus (lit 1) (lit 2)) (var X) , empty =>* lit n.
exists 3. apply eval_trans with (plus (lit 3) (var X)).
- apply eval_plus_lhs. apply eval_plus_fin.
- apply eval_trans with (plus (lit 3) (lit 0)).
-- apply eval_plus_rhs. apply eval_var.
-- apply eval_trans with (lit 3).
--- apply eval_plus_fin.
--- apply eval_refl.
Qed.

(* (1+2)+X => 3+X => 3+0 => 3
   (1+2)+X => (1+2)+0 => 3+0 => 3

*)


(* haladas tetele: ugyanez belathato Turing-teljes programozasi nyelvekre is, amikben van vegtelen ciklus *)
Lemma progress (e : exp)(s : state) : (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.
induction e.
- (* e = lit n*) left. exists n. reflexivity.
- (* e = var s0 *) right. exists (lit (s s0)). apply eval_var.
- (* e = plus e1 e2. megnezzuk, mi az e1. *) right. destruct IHe1.
-- (* e1 = lit n *) destruct H. rewrite -> H. destruct IHe2.
--- (* e2 = lit n0 *) destruct H0. rewrite -> H0. exists (lit (x + x0)). apply eval_plus_fin.
--- (* e2 => e2' *) destruct H0 as [e2' H2]. exists (plus (lit x) e2'). apply eval_plus_rhs. assumption.
-- (* e1 => e1' *) destruct H as [e1' H1]. exists (plus e1' e2). apply eval_plus_lhs. assumption.
Qed.

(* forall (e e0 e1 : exp)(s : state), e , s => e0 /\ e , s => e1  ->   e0 = e1 *)
Lemma determ : forall (e e0 : exp)(s : state), 
  e , s => e0 -> forall e1, e , s => e1 -> e0 = e1.
intros e e' s H. induction H. (* lehet, hogy mukodik "induction e" is*)
- (* H = eval_var *) intros. inversion H. reflexivity.
- (* H = eval_plus_lhs *) intros. inversion H0.
-- (* H0 = eval_plus_lhs *) assert (e1' = e1'0). apply IHevalo. assumption. rewrite -> H6. reflexivity.
-- (* H0 = eval_plus_rhs *) rewrite <- H1 in H. inversion H.
-- (* H0 = eval_fin *) rewrite <- H2 in H. inversion H.
- (* H = eval_plus_rhs *) intros. inversion H0.
-- (* H0 = eval_plus_lhs *) inversion H5.
-- (* H0 = eval_plus_rhs *) assert (e2' = e2'0). apply IHevalo. assumption. rewrite -> H6. reflexivity.
-- (* H0 = eval_fin *) rewrite <- H3 in H. inversion H.
- (* H = eval_fin *) intros e H0. inversion H0.
-- (* H0 = eval_plus_lhs *) inversion H4.
-- (* H0 = eval_plus_rhs *) inversion H4.
-- (* H0 = eval_fin *) reflexivity.
Qed.








