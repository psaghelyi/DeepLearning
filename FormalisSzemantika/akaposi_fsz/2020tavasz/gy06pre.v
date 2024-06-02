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

(* Denotacios szemantika: egy e kifejezes jelentese egy 

     evald e : state -> nat

   fuggveny. *)

Fixpoint evald (e : exp) : state -> nat := fun s => match e with
  | lit n => n
  | var x => s x
  | plus e1 e2 => evald e1 s + evald e2 s
  end.

Definition e1 : exp := plus (var X) (lit 3).

Example e1evald1 : evald e1 (update X 4 empty) = 7.
reflexivity. Qed.

Definition e2 : exp := plus (plus (var X) (lit 3)) (var Y).

Example e2evald1 : evald e2 (update X 4 empty) = 7.
reflexivity. Qed.

Example e2evald2 : evald e2 (update X 4 (update Y 2 empty)) = 9.
reflexivity. Qed.

(* Kis lepeses operacios szemantika: egy e kifejezes jelentese egy

     evalo e : state -> exp -> Prop

   fuggveny (heterogen binaris relacio), ez annak felel meg, hogy

     evalo e ⊂ state × exp.

   Altalaban egy

      R ⊂ A × B 

   binaris relaciot ugy irunk le Coq-ban, hogy

     R : A -> B -> Prop

   fuggveny.
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


(* e1 = plus (var X) (lit 3) *)

Example e1evalStep1 : e1 , (update X 4 empty) => plus (lit 4) (lit 3).
unfold e1.
apply eval_plus_lhs.
apply eval_var.
Qed.

Example e1evalStep2 : plus (lit 4) (lit 3) , (update X 4 empty) => lit 7.

(* e2 = plus (plus (var X) (lit 3)) (var Y) *)

Example e2evalStep1 : e2 , (update X 4 empty) => plus (plus (lit 4) (lit 3)) (var Y).

Example e2evalStep2 : plus (plus (lit 4) (lit 3)) (var Y) , (update X 4 empty) => 
                      plus (lit 7) (var Y).

Example e2evalStep3 : plus (lit 7) (var Y) , (update X 4 empty) => 
                      plus (lit 7) (lit 0).

Example e2evalStep4 : plus (lit 7) (lit 0) , (update X 4 empty) => 
                      lit 7.

Example exStep : plus (lit 5) (plus (plus (plus (lit 2) (var X)) (lit 2)) (lit 3)) , (update X 4 empty) => 
                 plus (lit 5) (plus (plus (plus (lit 2) (lit 4)) (lit 2)) (lit 3)).

(* inversion-t kell hasznalni a _,_=>_ elemeinek a vizsgalatara *)

Lemma lem1 : ~ (lit 3 , empty => lit 100).

Lemma lem2 : forall n s, 
  ~ (lit n , s => plus (lit n) (lit 0)).

Lemma notrefl (e : exp)(s : state) : ~ (e , s => e).

(* reflexiv, tranzitiv lezart *)

Reserved Notation "e , s =>* e'" (at level 50).

Inductive evalo_rtc : exp -> state -> exp -> Prop :=
  | eval_refl (e : exp)(s : state) : 

    e , s =>* e

  | eval_trans (e e' e'' : exp)(s : state) :

    e , s => e'    ->    e' , s =>* e'' ->
    (*-------------------------------*)
    e , s =>* e''

  where "e , s =>* e'" := (evalo_rtc e s e').

Example e1eval : e1 , (update X 4 empty) =>* lit 7.

Example e2eval : e2 , (update X 4 empty) =>* lit 7.

Definition e3 : exp := plus (lit 5) (plus (plus (plus (lit 2) (var X)) (lit 2)) (lit 3)).

Example e3eval : exists (e3' : exp), e3 , (update X 4 empty) =>* e3'.

Example e3eval' : exists (n : nat), e3 , (update X 4 empty) =>* lit n.

Lemma progress (e : exp)(s : state) : (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.

Lemma determ (e e' e'' : exp)(s : state) : e , s => e' /\ e , s => e'' -> e' = e''.

Lemma totality (e : exp)(s : state) : exists (n : nat), e , s =>* lit n.

Lemma denotVsOper (e : exp)(s : state)(n : nat) : e , s =>* lit n <-> evald e s = n.


