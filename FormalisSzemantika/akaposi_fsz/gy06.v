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

(* ismetles *)
Definition e1 : exp := plus (var Y) (plus (var X) (var Y)).
Definition st1 : state := update Y 2 empty. (* st1-et modositsd, hogy e1 bizonyithato legyen! *)
Lemma e1test : eval e1 (update X 0 st1) = 4.
Proof. simpl. unfold update. unfold st1. simpl. reflexivity. 
Qed. 


(* ismetles *)

(* Denotacios szemantika: egy e kifejezes jelentese egy 

     eval e : state -> nat

   fuggveny.

   Operacios szemantika: egy e kifejezes jelentese egy 

      evalo e : state -> exp -> Prop

   relacio.
 *)

(* Other relations in Coq:
   ----------------------- *)

Print le.

Lemma lem1' : 3 <= 10.
Proof. do 7 apply le_S. apply le_n. Qed.

Lemma lem2' : not (3 <= 2).
Proof. intro. inversion H. inversion H1. inversion H3. Qed.

(* hasznald a lemmasokat! *)

Definition P : nat -> Prop
  := fun n => 3 <= n.

Example P3 : P 3.
Proof.
  unfold P. apply le_n. Qed.

(* hasznalj inversion-t! *)
Example notP2 : not (P 2).
Proof. intro. inversion H. inversion H1. inversion H3. Qed.

(* hasznald a lemmasokat! *) 

Definition R : nat -> nat -> Prop
  := fun a b => a + b = 10.

Example R46 : R 4 6.
Proof.
  unfold R. simpl. reflexivity. Qed.

(* hasznalj inversion-t! *)

Example notR44 : not (R 4 4).
Proof.
  intro. unfold R in H. simpl in H. inversion H. Qed.

(* hasznald a lemmasokat! *)

Definition Q : nat -> nat -> Prop :=
  fun a b => True. (* ird at ugy, hogy Q12 es notQ13 bizonyithatoak legyenek! *)

Example Q12 : Q 1 2.
Proof. unfold Q. apply I. Qed. 

Example notQ13 : not (Q 1 3).
Admitted.

(* hasznalj inversion-t! *)

Definition Even' : nat -> Prop := fun n =>
  exists m, 2*m = n.

Example even4' : Even' 4.
Admitted.

Inductive Even : nat -> Prop :=
  | evenO : Even 0
  | evenSS : forall (n : nat), Even n -> Even (S (S n)).

Example even4 : Even 4.
(* tipp *) apply evenSS. Admitted.

(* hasznald a repeat tacticle-t (meta-taktikat)! *)
Example even100 : Even 100.
Admitted.

(* hasznalj inversion-t! *)
Example notEven1 : not (Even 1).
Admitted.

Require Import Arith. (* egyszeru nat-okrol szolo egyenlosegek bizonyitasara *)
Lemma evenSound : forall n, Even n -> exists m, 2 * m = n.
(* tipp *) intro n. intro. induction H.

Admitted.

(* https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html *)

(* hasznald a Nat.add_comm es plus_n_O lemmakat! *)
Lemma evenComplete' : forall x, Even (2 * x).
Proof
  

(* hasznald evenComplete'-ot! *)
Lemma evenComplete : forall n, (exists x, 2 * x = n) -> Even n.
Admitted.

(* add meg az Odd : nat -> Prop predikatumot induktivan! *)
Inductive Odd : nat -> Prop :=
  | oddS : forall n, Even n -> Odd (S n).

(* hasznald a repeat-t! *)
.

Lemma oddProp : forall n, Odd n <-> exists m, 2 * m + 1 = n.
Admitted.

(* Most megadunk induktivan egy relaciot a kifejezeseken.

Levezetesi szabalyok:

  ----------------------eval_var
  var x , s => lit (s x)

          e1 , s => e1'
  -----------------------------eval_plus_lhs
  plus e1 e2 , s => plus e1' e2

               e2 , s => e2'
  ---------------------------------------eval_plus_rhs
  plus (lit n) e2 , s => plus (lit n) e2'

  ---------------------------------------eval_plus_fin
  plus (lit m) (lit n) , s => lit (m + n)


Ha s X = 1, vezesd le, hogy 
  plus (var X) (lit 3) , s => plus (lit 1) (lit 3)
!

Mutasd meg, hogy  
  plus (var X) (lit 3) , s => lit 4
nem levezetheto!

Vezesd le, hogy 
  plus (lit 1) (lit 3) , s => lit 4
!

Vezesd le, hogy mire irodik at (tobb lepesben)
  plus (var X) (var Y)
!

Most megcsinaljuk ezeket formalisan is:
*)

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


(* 
          ----------------------eval_var
          (var X) , s => (lit 4)
  ------------------------------------------------eval_plus_lhs
  plus (var X) (lit 3) , s => plus (lit 4) (lit 3)
*)

Example eval1 : plus (var X) (lit 3) , (update X 4 empty) => plus (lit 4) (lit 3).
(* probald meg eval_plus_rhs-t alkalmazni! *)
Proof. apply eval_plus_lhs. apply eval_var. Qed.


(*  plus (var X) (lit 3) , s => lit 4 *)

Example eval2 : forall s, plus (lit 4) (lit 3) , s => lit 7.
Proof. intro. apply eval_plus_fin. Qed.



Example eval3 :
  plus (plus (var X) (lit 3)) (var Y) , (update X 4 empty) => 
  plus (plus (lit 4) (lit 3)) (var Y).
Proof. apply eval_plus_lhs. apply eval_plus_lhs. apply eval_var. Qed.

(*  plus (lit 4) (lit 3) , s => lit 7 *)

Example eval4 :
  plus (plus (lit 4) (lit 3)) (var Y) , (update X 4 empty) => 
  plus (lit 7) (var Y).
Proof. apply eval_plus_lhs. apply eval_plus_fin. Qed.



Example eval5 :
  plus (lit 7) (var Y) , (update X 4 empty) => 
  plus (lit 7) (lit 0).
Proof. apply eval_plus_rhs. apply eval_var. Qed.


Example eval6 :
  plus (lit 7) (lit 0) , (update X 4 empty) => 
  lit 7.
Proof. apply eval_plus_fin. Qed.


Example exStep : plus (lit 5) (plus (plus (plus (lit 2) (var X)) (lit 2)) (lit 3)) , (update X 4 empty) => 
                 plus (lit 5) (plus (plus (plus (lit 2) (lit 4)) (lit 2)) (lit 3)).
Proof. apply eval_plus_rhs. apply eval_plus_lhs. apply eval_plus_lhs. apply eval_plus_rhs. apply eval_var. Qed.

Lemma lem1 : ~ (lit 3 , empty => lit 100).
Proof. intro. inversion H. Qed.

Lemma lem2 : forall n s, 
  ~ (lit n , s => plus (lit n) (lit 0)).
Proof. intros. intro. inversion H. Qed.

Lemma notrefl (e : exp)(s : state) : ~ (e , s => e).
Proof.
intro.
induction e.
 * inversion H.
 * inversion H.
 * inversion H.
   - (* eval_plus_lhs *) apply IHe1. exact H3.
   - (* eval_plus_rhs *) apply IHe2. exact H3.
Qed.

