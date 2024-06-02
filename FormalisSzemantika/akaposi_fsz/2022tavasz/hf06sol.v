Require Import Strings.String.

(* 1. resz: relaciok
   ----------------- *)

Definition R : nat -> nat -> Prop
  := fun a b => a + b = 10.

Example R46 : R 4 6.
reflexivity. Qed.

Example notR44 : not (R 4 4).
intro. discriminate H. Qed.

Definition Q : nat -> nat -> Prop :=
  fun a b => (b = 2). (* ugy add meg, hogy Q12 es notQ13 bizonyithatoak legyenek! *)

Example Q12 : Q 1 2.
reflexivity. Qed.
Example notQ13 : not (Q 1 3).
intro. discriminate H. Qed.

Inductive Even : nat -> Prop :=
  | evenO : Even 0
  | evenSS : forall (n : nat), Even n -> Even (S (S n)).

(*
Even 0 : Prop
evenO : Even 0
Even 1 : Prop
Even 1 = Even (S O)
*)

Example even4 : Even 4.
apply evenSS. apply evenSS. apply evenO. Qed.

(* Example even5 : Even 5.
apply evenSS. apply evenSS. apply evenO. *)

(* hasznalj sok copy-paste-et vagy a repeat tacticle-t (meta-taktikat)! *)
Example even100 : Even 100.
repeat (apply evenSS). apply evenO. Qed.

(* hasznalj inversion-t! *)
Example notEven1 : not (Even 1).
intro. inversion H. Qed.

Lemma evenSound : forall n, Even n -> exists m, 2 * m = n.
intro n. intro H. induction H.
- exists 0. simpl. reflexivity.
- destruct IHEven. exists (S x). rewrite <- H0. simpl. Require Import Arith. ring. Qed.
(*
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

P : nat -> Prop
1. P(O)
2. forall m, P(m) -> P (S m)
----------------------------
forall n, P(n)

Inductive Even : nat -> Prop :=
  | evenO : Even 0
  | evenSS : forall (n : nat), Even n -> Even (S (S n)).

P : forall n , Even n -> Prop
1. alapeset : P O evenO
2. induktivEset : forall (n : nat)(H : Even n), P n H -> P (S (S n)) (evenSS n H)
----------------------------------------------------------------------------------
forall n (H : Even n), P n H

P n H := (exists m : nat, 2 * m = n)
*)

(* fakultativ *)
(* hasznald a Nat.add_comm es plus_n_O lemmakat! *)
Lemma evenComplete' : forall x, Even (2 * x).
intros. induction x.
- apply evenO.
- simpl. Search "+". rewrite (Nat.add_comm x (S (x + 0))). simpl. apply evenSS.
  rewrite <- (plus_n_O x). simpl in IHx. rewrite <- (plus_n_O x) in IHx. assumption.
Qed.

(* fakultativ *)
(* hasznald evenComplete'-ot! *)
Lemma evenComplete : forall n, (exists x, 2 * x = n) -> Even n.
intros. destruct H. rewrite <- H. apply evenComplete'. Qed.

(* fakultativ *)
Lemma evenCorrect : forall n, Even n <-> (exists x, 2 * x = n).
intro. split. apply evenSound. apply evenComplete. Qed.

(* add meg az Odd : nat -> Prop predikatumot induktivan! *)
Inductive Odd : nat -> Prop :=
  | odd1 : Odd 1
  | oddSS : forall (n : nat), Odd n -> Odd (S (S n)).

(* fakultativ *)
Lemma oddCorrect : forall n, Odd n <-> exists m, 2 * m + 1 = n.
Admitted.

(* 2. resz: small step operational semantics
   ----------------------------------------- *)

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


(* Most megadunk induktivan egy relaciot a kifejezeseken.
R ⊂ exp x state x exp
R(e,s,e') === s allapotban az e kifejezesbol egy lepesben e' kepzodik
e,s=>e'
e',s=>e''
e'',s=>e'''
...
  

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


           ------------------eval_var
           var X , s => lit 1
  ------------------------------------------------eval_plus_lhs
  plus (var X) (lit 3) , s => plus (lit 1) (lit 3)

  plus e1      e2      , s => plus e1'     e2

!

Mutasd meg, hogy  

  --------------------------------- nincs ilyen szabaly
  plus (var X) (lit 3) , s => lit 4


nem levezetheto!

Vezesd le, hogy 

  --------------------------------- eval_plus_fin
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

    (*-------------------*)
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

    (*------------------------------------*)
    plus (lit m) (lit n) , s => lit (m + n)

  where "e , s => e'" := (evalo e s e').

Example eval3 :
  plus (plus (var X) (lit 3)) (var Y) , (update X 4 empty) => 
  plus (plus (lit 4) (lit 3)) (var Y).
apply eval_plus_lhs. apply eval_plus_lhs. apply eval_var. Qed.

Example eval4 :
  plus (plus (lit 4) (lit 3)) (var Y) , (update X 4 empty) => 
  plus (lit 7) (var Y).
apply eval_plus_lhs. apply eval_plus_fin. Qed.

Example eval5 :
  plus (lit 7) (var Y) , (update X 4 empty) => 
  plus (lit 7) (lit 0).
apply eval_plus_rhs. apply eval_var. Qed.

Example eval6 :
  plus (lit 7) (lit 0) , (update X 4 empty) => 
  lit 7.
apply eval_plus_fin. Qed.

Example exStep : plus (lit 5) (plus (plus (plus (lit 2) (var X)) (lit 2)) (lit 3)) , (update X 4 empty) => 
                 plus (lit 5) (plus (plus (plus (lit 2) (lit 4)) (lit 2)) (lit 3)).
apply eval_plus_rhs.
apply eval_plus_lhs.
apply eval_plus_lhs.
apply eval_plus_rhs.
apply eval_var.
Qed.

Definition s : state 
  := update Y 4 (update X 3 empty).
Example eval7 : plus (var X) (var Y) , s => plus (lit 3) (var Y).
apply eval_plus_lhs. apply eval_var. Qed.
Example eval8 : plus (lit 3) (var Y) , s => plus (lit 3) (lit 4).
apply eval_plus_rhs. apply eval_var. Qed.
Example eval9 : plus (lit 3) (lit 4) , s => lit 7.
apply eval_plus_fin. Qed.

Lemma lem1 : ~ (lit 3 , empty => lit 100).
unfold not. intros. inversion H. Qed.

Lemma lem2 : forall n s, 
  ~ (lit n , s => plus (lit n) (lit 0)).
intros. unfold not. intros. inversion H.
Qed.