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

(* small-step operational semantics *)
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

(* denotational semantics *)
Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | plus e1 e2 => eval e1 s + eval e2 s
  end.

(*
halmazelmeletben: f : A -> B fuggveny, az f⊂AxB, ∀a∈A,∃b∈B,(a,b)∈f, (a,b)∈f és (a,b')∈f, akkor b = b'.

f : A -> B fuggveny (egy program, aminek a bemenete A, kimenete B)
fRel : A -> B -> Prop (a relacio karakterisztikus fuggvenye)
fRel a b := (f a = b) -- fRel az f grafja
fRel : A -> B -> Bool (eldontheto relacio)

  e || n
    v

 big-step operational semantics *)
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
simpl. reflexivity. Qed.

Example ex1b : plus (plus (var W) (var X)) (lit 100) ,
                     update W 200 empty =v 300.
simpl. apply evalb_plus with (n1 := 200). 
(* nem latja: ?M1060 + 100 = 300   -> ?M1060 = 200 
   latja:     200    + ?M10 = 300  -> ?M10 = 100     
      200 + ?M10 = S(S(S...(S ?M10)...))  = S(S(S....(S O)...))
                   ^200 db                  ^ 300 db                  *)

- apply evalb_plus with (n1 := 200).
-- apply evalb_var.
-- apply evalb_var.
- apply evalb_lit.
Qed.

Example ex2b : exists (n : nat),
  plus (plus (var X) (var Y)) (plus (lit 3) (var Z)) , 
  update X 3 (update Y 2 empty) =v n.
exists 8. apply evalb_plus with (n1 := 5).
- apply evalb_plus with (n1 := 3); apply evalb_var.
- apply evalb_plus with (n1 := 3).
-- apply evalb_lit.
-- apply evalb_var.
Qed.

Lemma denot2bigstep (e : exp)(s : state) : forall (n : nat), eval e s = n -> e , s =v n.
induction e.
- intros. simpl in H. rewrite <- H. apply evalb_lit.
- intros. simpl in H. rewrite <- H. apply evalb_var.
- intros. simpl in H. rewrite <- H. apply evalb_plus. apply IHe1. reflexivity. apply IHe2. reflexivity. Qed.

Lemma bigstep2denot (e : exp)(s : state) : forall (n : nat), e , s =v n -> eval e s = n.
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
intros. assert (eval e s = n).
- apply bigstep2denot. assumption.
- assert (eval e s = n'). 
-- apply bigstep2denot. assumption.
-- rewrite <- H1. rewrite <- H2. reflexivity.
Qed.

Lemma bigstepVsdenot (e : exp)(s : state)(n : nat) : e , s =v n <-> eval e s = n.
split.
- apply bigstep2denot.
- apply denot2bigstep.
Qed.

Lemma notInvertible (n : nat)(s : state) : 
  exists (e e' : exp), e <> e' /\ e , s =v n /\ e' , s =v n.
exists (lit n). exists (plus (lit n) (lit 0)). split.
- intro. inversion H.
- split.
-- apply evalb_lit.
-- assert (plus (lit n) (lit 0), s =v (n + 0)).
--- apply evalb_plus; apply evalb_lit.
--- assert (n = n + 0). apply plus_n_O. rewrite <- H0 in H. assumption.
Qed.
