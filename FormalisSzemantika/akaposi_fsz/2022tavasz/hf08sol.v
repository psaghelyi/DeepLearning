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

(* haladas tetele: ugyanez belathato Turing-teljes programozasi nyelvekre is, amikben van vegtelen ciklus *)
Lemma progress (e : exp)(s : state) : (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.
induction e.
- (* e = lit n *) left. exists n. reflexivity.
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

Definition eval_singl (e e' : exp)(s : state) : e , s => e' -> e , s =>* e'.
intro. apply eval_trans with e'. assumption. apply eval_refl. Qed.

(* reflexiv, _tranzitiv_ lezart *)
Lemma trans (e e' e'' : exp)(s : state) : e , s =>* e' -> e' , s =>* e'' -> e , s =>* e''.
intros.
induction H.
  - exact H0.
  - apply (eval_trans _ _ _ _ H). apply IHevalo_rtc. exact H0.
Qed.

Lemma eval_plus_lhs_rtc (e1 e1' e2 : exp)(s : state) : e1 , s =>* e1' ->
  plus e1 e2 , s =>* plus e1' e2.
intro. induction H.
- apply eval_refl.
- apply eval_trans with (plus e' e2).
-- apply eval_plus_lhs. assumption.
-- assumption.
Qed.

Lemma eval_plus_rhs_rtc (n : nat)(e2 e2' : exp)(s : state) : e2 , s =>* e2' -> 
  plus (lit n) e2 , s =>* plus (lit n) e2'.
intro. induction H.
- apply eval_refl.
- apply eval_trans with (plus (lit n) e').
-- apply eval_plus_rhs. assumption.
-- assumption.
Qed.

(* hasznald eval_plus_lhs_rtc-t, eval_plus_rhs_rtc-t es eval_singl-et! *)
Lemma operDenot (e : exp)(s : state) : e , s =>* lit (eval e s).
induction e.
- simpl. apply eval_refl.
- simpl. apply eval_trans with (e' := lit (s s0)). apply eval_var. apply eval_refl.
- simpl. apply trans with (e' := plus (lit (eval e1 s)) e2).
-- apply eval_plus_lhs_rtc. assumption.
-- apply trans with (e' := plus (lit (eval e1 s)) (lit (eval e2 s))).
--- apply eval_plus_rhs_rtc. assumption.
--- apply eval_singl. apply eval_plus_fin.
Qed.

(* operDenot-ot hasznald! nem kell indukcio. *)
Lemma totality (e : exp)(s : state) : exists (n : nat), e , s =>* lit n.
exists (eval e s). apply operDenot. Qed.

Lemma determ_rtc' (e e0 : exp)(s : state) : 
  e , s =>* e0 /\ (exists n0, e0 = lit n0) -> 
  forall e1, e , s =>* e1 /\ (exists n1, e1 = lit n1) -> e0 = e1.
intros H. destruct H as [H0 H0']. destruct H0' as [n H0e]. induction H0.
- intros. destruct H. rewrite -> H0e in H. inversion H.
-- assumption.
-- inversion H1.
- intros. destruct H1. destruct H2 as [n1 H1e]. inversion H1.
-- rewrite H4 in H. rewrite H1e in H. inversion H.
-- assert (e' = e'0).
--- apply determ with (e := e)(s := s). assumption. assumption.
--- apply IHevalo_rtc.
---- assumption.
---- rewrite <- H7 in H3. split.
----- assumption.
----- exists n1. assumption.
Qed.

(* Nincs szukseg indukciora, hasznald determ_rtc'-t. *)
Lemma determ_rtc (e : exp)(s : state)(n1 n2 : nat) : 
  e , s =>* lit n1 -> e , s =>* lit n2 -> n1 = n2.
intros. assert (lit n1 = lit n2). 
- apply determ_rtc' with e s.
-- split. assumption. exists n1. reflexivity.
-- split. assumption. exists n2. reflexivity.
- inversion H1. reflexivity.
Qed.

(* Nincs szukseg indukciora, hasznald operDenot-ot es determ_rtc-t. *)
Lemma denotVsOper (e : exp)(s : state)(n : nat) : 
  eval e s = n <-> e , s =>* lit n.
split.
- intros. rewrite <- H. apply operDenot.
- intros. assert (e, s =>* lit (eval e s)). apply operDenot.
  apply (determ_rtc e s (eval e s) n). assumption. assumption.
Qed.
