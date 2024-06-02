(*
egyszeru kifejezesnyelv, valtozok, denotacios szemantika
exp -> (state -> nat)
operacios szemantika
exp -> RELACIO
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

(* ismetles *)
Definition e1 : exp := plus (var Y) (plus (var X) (var Y)).
Definition st1 : state := update Y 2 empty. (* st1-et modositsd, hogy e1 bizonyithato legyen! *)
Lemma e1test : eval e1 (update X 0 st1) = 4.
(*simpl. unfold update. simpl. unfold st1. unfold update. simpl.*)
reflexivity. Qed.

(* hf-bol *)
Lemma update_sound (x : string)(n : nat)(s : state) :
  (update x n s) x = n.
Proof.
simpl.
(* tipp *) unfold update. destruct (string_dec x x).
* reflexivity.
* unfold "<>" in n0. exfalso. apply n0. reflexivity.
Qed.

Lemma update_neq (x x' : string)(n : nat)(s : state)(ne : x <> x') :
  (update x n s) x' = s x'.
unfold update. destruct (string_dec x x').
* exfalso. apply ne. assumption.
* reflexivity.
Qed.

(* Denotacios szemantika: egy e kifejezes jelentese egy 

     eval e : state -> nat

   fuggveny.

   Operacios szemantika: egy e kifejezes jelentese egy 

      evalo e : state -> exp -> Prop

   relacio.
 *)

(* Other relations in Coq:
   ----------------------- *)

(*
Inductive le (n:nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m
*)

Lemma lem1' : 3 <= 10.
Proof. do 7 (apply le_S). apply le_n. Qed.

Lemma lem2' : not (3 <= 2).
Proof. intro. inversion H. inversion H1. inversion H3.
Qed.

Definition P : nat -> Prop
  := fun n => 3 <= n.

Example P3 : P 3.
Admitted.

(* hasznalj inversion-t! *)
Example notP2 : not (P 2).
Admitted.

Definition R : nat -> nat -> Prop
  := fun a b => a + b = 10.

Example R46 : R 4 6.
Admitted.

Example notR44 : not (R 4 4).
Admitted.

Definition Q : nat -> nat -> Prop :=
  fun a b => (b = 2). (* ird at ugy, hogy Q12 es notQ13 bizonyithatoak legyenek! *)

Example Q12 : Q 1 2.
unfold Q. reflexivity. Qed.
Example notQ13 : not (Q 1 3).
intro. unfold Q in H. inversion H. Qed.

(*
Inductive Eq (A : Type) (a : A) : A -> Prop :=
  | refl : Eq A a a.

*)

Definition Even' : nat -> Prop := fun n =>
  exists m, 2*m = n.

Example even4' : Even' 4.
Proof. unfold Even'. exists 2. simpl. reflexivity. Qed.

Inductive Even : nat -> Prop :=
  | evenO : Even 0
  | evenSS : forall (n : nat), Even n -> Even (S (S n)).

Example even4 : Even 4.
Proof. apply evenSS. apply evenSS. apply evenO. Qed.

(* hasznald a repeat tacticle-t (meta-taktikat)! *)
Example even100 : Even 100.
Proof. do 49 (apply evenSS). apply evenSS. apply evenO. Qed. 

(* hasznalj inversion-t! *)
Example notEven1 : not (Even 1).
intro. inversion H. Qed.
(*
Require Import Arith. (* egyszeru nat-okrol szolo egyenlosegek bizonyitasara *)
Lemma evenSound : forall n, Even n -> exists m, 2 * m = n.
(* tipp *) intro n. intro. induction H.
Admitted.

(* https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html *)

(* hasznald a Nat.add_comm es plus_n_O lemmakat! *)
Lemma evenComplete' : forall x, Even (2 * x).
Admitted.

(* hasznald evenComplete'-ot! *)
Lemma evenComplete : forall n, (exists x, 2 * x = n) -> Even n.
Admitted.

(* add meg az Odd : nat -> Prop predikatumot induktivan! *)
Inductive Odd : nat -> Prop :=
.

Lemma oddProp : forall n, Odd n <-> exists m, 2 * m + 1 = n.
Admitted.
*)

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

=========================================================
s X = 1, s Y = 0

               ------------------eval_var
               var X , s => lit 1
  ----------------------------------------------------eval_plus_lhs
  plus (var X) (var Y) , s => plus (lit 1) (var Y)


              ------------------eval_var
              var Y , s => lit 0
  --------------------------------------------------eval_plus_rhs
  plus (lit 1) (var Y) , s => plus (lit 1) (lit 0)


  ---------------------------------eval_plus_fin
  plus (lit 1) (lit 0) , s => lit 1

                 ?
  ---------------------------------
  plus (var X) (lit 3) , s => lit 4

  ----------------------------------eval_plus_fin
  plus (lit 1) (lit 3) , s => lit 4


Ha s X = 1, vezesd le, hogy 

                 ----------------------eval_var
                 (var X) , s => (lit 1)
  ------------------------------------------------eval_plus_lhs
  plus (var X) (lit 3) , s => plus (lit 1) (lit 3)








Most megcsinaljuk ezeket formalisan is:
*)

Reserved Notation "e , s => e'" (at level 50).
Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :

    (*-------------------------*)
    var x , s => lit (s x)

  | eval_plus_lhs (e1 e2 e1' : exp)(s : state) :

           e1 , s => e1'                  ->
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
apply eval_plus_lhs. apply eval_var. Qed.

Example eval2 : forall s, plus (lit 4) (lit 3) , s => lit 7.
Proof. intro. apply eval_plus_fin. Qed.

Example eval3 :
  plus (plus (var X) (lit 3)) (var Y) , (update X 4 empty) => 
  plus (plus (lit 4) (lit 3)) (var Y).
apply eval_plus_lhs.
apply eval_plus_lhs.
apply eval_var.
Qed.

Example eval4 :
  plus (plus (lit 4) (lit 3)) (var Y) , (update X 4 empty) => 
  plus (lit 7) (var Y).
apply eval_plus_lhs.
apply eval_plus_fin.
Qed.

Example eval5 :
  plus (lit 7) (var Y) , (update X 4 empty) => 
  plus (lit 7) (lit 0).
apply eval_plus_rhs.
apply eval_var.
Qed.

Example eval6 :
  plus (lit 7) (lit 0) , (update X 4 empty) => 
  lit 7.
apply eval_plus_fin.
Qed.

Example exStep : plus (lit 5) (plus (plus (plus (lit 2) (var X)) (lit 2)) (lit 3)) , (update X 4 empty) => 
                 plus (lit 5) (plus (plus (plus (lit 2) (lit 4)) (lit 2)) (lit 3)).
apply eval_plus_rhs.
apply eval_plus_lhs.
apply eval_plus_lhs.
apply eval_plus_rhs.
apply eval_var.
Qed.

Lemma lem1 : ~ (lit 3 , empty => lit 100).
intro. inversion H.
Qed.

Lemma lem2 : forall n s, 
  ~ (lit n , s => plus (lit n) (lit 0)).
intros. intro. inversion H.
Qed.

Lemma notrefl (e : exp)(s : state) : ~ (e , s => e).
(* tipp *) intro. induction e.
* inversion H.
* inversion H.
* inversion H.
** apply IHe1. assumption.
** apply IHe2. assumption.
Qed.

(* kovetkezo ora 6 perccel rovidebb *)
