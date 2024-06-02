(* BEGIN FIX *)
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

Lemma determ (e e' : exp)(s : state) : e , s => e' -> forall e'', e , s => e'' -> e' = e''.
intro. induction H.
 * intros. inversion H. reflexivity.
 * intros. inversion H0. 
   - rewrite -> (IHevalo e1'0 H5). reflexivity.
   - rewrite <- H1 in H. inversion H.
   - rewrite <- H2 in H. inversion H.
 * intros. inversion H0.
   - inversion H5.
   - rewrite -> (IHevalo e2'0 H5). reflexivity.
   - rewrite <- H3 in H. inversion H.
 * intros. inversion H.
   - inversion H4.
   - inversion H4.
   - reflexivity.
Qed. 

Definition eval_singl (e e' : exp)(s : state) : e , s => e' -> e , s =>* e'.
(* END FIX *)
intro. apply (eval_trans _ e'). exact H. apply eval_refl. Qed.

(* BEGIN FIX *)
Lemma trans (e e' e'' : exp)(s : state) : e , s =>* e' -> e' , s =>* e'' -> e , s =>* e''.
intros.
induction H.
  - exact H0.
  - apply (eval_trans _ _ _ _ H). apply IHevalo_rtc. exact H0.
Qed.

(* HINT: do induction on e1 , s =>* e1' *)
Lemma eval_plus_lhs_rtc (e1 e1' e2 : exp)(s : state) : e1 , s =>* e1' -> plus e1 e2 , s =>* plus e1' e2.
(* END FIX *)
intro. induction H.
 * apply eval_refl.
 * apply (eval_trans _ (plus e' e2)). apply eval_plus_lhs. exact H. exact IHevalo_rtc.
Qed.

(* BEGIN FIX *)
(* HINT: do induction on e2 , s =>* e2' *)
Lemma eval_plus_rhs_rtc (n : nat)(e2 e2' : exp)(s : state) : e2 , s =>* e2' -> 
  plus (lit n) e2 , s =>* plus (lit n) e2'.
(* END FIX *)
intros.
induction H.
 * apply eval_refl.
 * apply (eval_trans _ (plus (lit n) e')). apply eval_plus_rhs. exact H. exact IHevalo_rtc.
Qed.

(* BEGIN FIX *)
(* HINT: do induction on e *)
Lemma operDenot (e : exp)(s : state) : e , s =>* lit (evald e s).
(* END FIX *)
induction e.
 * simpl. apply eval_refl.
 * simpl. apply eval_singl. apply eval_var.
 * simpl. apply (trans _ (plus (lit (evald e1 s)) e2)). apply eval_plus_lhs_rtc. exact IHe1.
   apply (trans _ (plus (lit (evald e1 s)) (lit (evald e2 s)))). apply eval_plus_rhs_rtc. exact IHe2.
   apply eval_singl. apply eval_plus_fin.
Qed.

(* BEGIN FIX *)
Lemma totality (e : exp)(s : state) : exists (n : nat), e , s =>* lit n.
(* END FIX *)
exists (evald e s). apply operDenot. Qed.

(* BONUS EXERCISES:
Require Import Coq.Program.Equality.

Lemma determ_rtc (e : exp)(s : state)(n : nat) : e , s =>* lit n -> forall n', e , s =>* lit n' -> n = n'.
intro. dependent induction H.
 * intros. inversion H. reflexivity. inversion H0.
 * intros. inversion H1.
   - rewrite -> H4 in H. inversion H.
   - rewrite <- (determ _ _ _ H _ H2) in H3.
     apply IHevalo_rtc. reflexivity. exact H3.
Qed.

Lemma denotVsOper (e : exp)(s : state)(n : nat) : evald e s = n <-> e , s =>* lit n.
split.
 * intro. rewrite <- H. apply operDenot.
 * intro. exact (determ_rtc _ _ _ (operDenot e s) _ H).
Qed.
*)

(* BEGIN FIX *)
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

(* BEGIN FIX *)
Example ex2 : exists (n : nat),
  plus (plus (var X) (var Y)) (plus (lit 3) (var Z)) , update X 3 (update Y 2 empty) =v n.
(* END FIX *)
exists 8.
apply (evalb_plus 5 3).
 * apply (evalb_plus 3 2).
   - apply evalb_var.
   - apply evalb_var.
 * apply (evalb_plus 3 0).
   - apply evalb_lit.
   - apply evalb_var.
Qed.

(* BEGIN FIX *)
(* HINT: do induction on e , s =v n *)
Lemma determBigstep (e : exp)(s : state)(n : nat) : e , s =v n -> forall n', e , s =v n' -> n = n'.
(* END FIX *)
intro. induction H.
 * intros. inversion H. reflexivity.
 * intros. inversion H. reflexivity.
 * intros. inversion H1. rewrite -> (IHevalb1 _ H4). rewrite -> (IHevalb2 _ H7). reflexivity.
Qed.

(* BEGIN FIX *)
Lemma denot2bigstep (e : exp)(s : state) : forall (n : nat), evald e s = n -> e , s =v n.
induction e; intros; simpl in H; rewrite <- H.
 * apply evalb_lit.
 * apply evalb_var.
 * apply (evalb_plus (evald e1 s) (evald e2 s)). apply IHe1. reflexivity.  apply IHe2. reflexivity.
Qed.  

(* HINT: do induction on e *)
Lemma bigstep2denot (e : exp)(s : state) : forall (n : nat), e , s =v n -> evald e s = n.
(* END FIX *)
induction e; intros; simpl; inversion H. 
 * reflexivity.
 * reflexivity.
 * inversion H. rewrite -> (IHe1 _ H8). rewrite -> (IHe2 _ H11). rewrite -> H10. rewrite -> H4. reflexivity.
Qed.

(* BEGIN FIX *)
Lemma bigstepVsdenot (e : exp)(s : state)(n : nat) : e , s =v n <-> evald e s = n.
(* END FIX *)
split.
 * intros. apply bigstep2denot. exact H.
 * intros. apply denot2bigstep. exact H.
Qed.

(* BEGIN FIX *)
Lemma notInvertible1 (n : nat)(s : state) : exists (e e' : exp), e <> e' /\ e , s =v (1 + n) /\ e' , s =v (1 + n).
(* END FIX *)
exists (plus (lit 1) (lit n)). exists (lit (1 + n)). split.
intro. discriminate H.
split.
 * apply (evalb_plus 1 n).
   - apply evalb_lit.
   - apply evalb_lit.
 * apply evalb_lit.
Qed.
