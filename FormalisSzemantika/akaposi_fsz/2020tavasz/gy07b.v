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

Lemma ex10 (n : nat) : var X <> lit n.
intro. discriminate H. Qed.

Lemma progress (e : exp)(s : state) :
  (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.
Proof. 
  induction e.
  * (* e = lit n *) left. exists n. reflexivity.
  * (* e = var x *) right. exists (lit (s x)). apply eval_var.
  * (* e = plus e1 e2 *) right. destruct IHe1.
    - destruct H as [n1 H]. destruct IHe2.
      + destruct H0 as [n2 H0]. rewrite -> H. rewrite -> H0.
        exists (lit (n1 + n2)).
        apply eval_plus_fin.
      + destruct H0 as [e2' H0]. Check eval_plus_rhs. exists (plus (lit n1) e2').
        rewrite -> H. apply eval_plus_rhs. exact H0.
    - destruct H as [e1' H]. exists (plus e1' e2). apply eval_plus_lhs. exact H.
Qed.

(*  
eval_plus_lhs   e1 => e1'
eval_plus_rhs   e1 = lit n1, e2 => e2'     MOST
eval_plus_fin   e1 = lit n1, e2 = lit n2   PIPA
*) 


(*            bevezeto szabaly         eliminacios szabaly
==========================================================
\/            left, right              destruct
/\            split                    destruct
exists        exists                   destruct
forall        intro                    apply
A -> B        intro                    apply
induktiv def. konstruktor              indukcio, destruct 
*)


Lemma determ (e e' : exp)(s : state) : e , s => e' -> forall e'', e , s => e'' -> e' = e''.
intro.
induction e.
 * inversion H.
 * inversion H. intros. inversion H3. reflexivity.
 * destruct e1.
   - destruct e2. Admitted.

Definition eval_singl (e e' : exp)(s : state) : e , s => e' -> e , s =>* e'.
Admitted.

(* HF *)
Lemma trans (e e' e'' : exp)(s : state) : e , s =>* e' -> e' , s =>* e'' -> e , s =>* e''.
intros.
induction H.
  - exact H0.
  - apply (eval_trans _ _ _ _ H). apply IHevalo_rtc. exact H0.
Qed.

Lemma eval_plus_lhs_rtc (e1 e1' e2 : exp)(s : state) : e1 , s =>* e1' ->
  plus e1 e2 , s =>* plus e1' e2.
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

Example ex1d : evald (plus (plus (var W) (var X)) (lit 100)) (update W 200 empty) = 300.
simpl. reflexivity. Qed.

Example ex1 : plus (plus (var W) (var X)) (lit 100) , update W 200 empty =v 300.
Proof.
 apply (evalb_plus 200 100).
 * apply (evalb_plus 200 0).
   - apply evalb_var.
   - apply evalb_var.
 * apply evalb_lit.
Qed.
(*
---------evalb_var           ------evalb_var
W =v 200                     X =v 0
---------------------------------------evalb_plus    --------------evalb_lit
plus W X =v 200                                      100 =v 100
---------------------------------------------------------------evalb_plus
plus (plus W X) 100 =v 300
*)

Example ex2 : exists (n : nat),
  plus (plus (var X) (var Y)) (plus (lit 3) (var Z)) , update X 3 (update Y 2 empty) =v n.
Admitted.

Lemma determBigstep (e : exp)(s : state)(n : nat) : e , s =v n -> forall n',
  e , s =v n' -> n = n'.
Admitted.

Lemma denot2bigstep (e : exp)(s : state) : forall (n : nat), evald e s = n -> e , s =v n.
induction e; intros; simpl in H; rewrite <- H.
 * apply evalb_lit.
 * apply evalb_var.
 * apply evalb_plus. apply IHe1. reflexivity. apply IHe2. reflexivity.
Qed.

Lemma bigstep2denot (e : exp)(s : state) : forall (n : nat), e , s =v n -> evald e s = n.
Admitted.

Lemma bigstepVsdenot (e : exp)(s : state)(n : nat) : e , s =v n <-> evald e s = n.
Admitted.

Lemma notInvertible (n : nat)(s : state) : exists (e e' : exp),
   e <> e' /\ e , s =v n /\ e' , s =v n.
exists (lit n), (plus (lit 0) (lit n)).
split. intro. discriminate H. split.
 * apply evalb_lit.
 * apply (evalb_plus 0 n); apply evalb_lit.
Qed.



