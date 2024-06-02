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

     evalo e s e' : Prop

     p : evalo e s e', ha igaz a relacio
     nincs ilyen p, ha hamis a relaco

   fuggveny (heterogen binaris relacio), ez annak felel meg, hogy

     evalo e ⊂ state × exp.

     evalo ⊂ exp × state × exp.

     p : evalo (plus (lit 1) (lit 2)) s (lit 3)

               plus (lit 1) (lit 2) , s => lit 3

   Altalaban egy

      R ⊂ A × B 

   binaris relaciot ugy irunk le Coq-ban, hogy

     R : A -> B -> Prop

     p : R a b   <-- a R b,    a relacioban all b-vel (R szerint)

   fuggveny.
 *)

Reserved Notation "e , s => e'" (at level 50).
(*
szabalyok:

  ----------------------eval_var
  var x , s => lit (s x)

   plus       plus
    /\   =>    /\
  e1  e2    e1'  e2


          e1 , s => e1'
  -----------------------------eval_plus_lhs
  plus e1 e2 , s => plus e1' e2

     plus       plus
      /\   =>    /\
 lit n  e2  lit n  e2'


               e2 , s => e2'
  ---------------------------------------eval_plus_rhs
  plus (lit n) e2 , s => plus (lit n) e2'

  ---------------------------------------eval_plus_fin
  plus (lit m) (lit n) , s => lit (m + n)

levezetesi fa (tudom, hogy s X = 1):


                 ----------------------eval_var
                 (var X) , s => (lit 1)
  ------------------------------------------------eval_plus_lhs
  plus (var X) (lit 3) , s => plus (lit 1) (lit 3)



                 ?
  --------------------------------- nem levezetheto
  plus (var X) (lit 3) , s => lit 4


  ---------------------------------eval_plus_fin
  plus (lit 1) (lit 3) , s => lit 4
*)
(*
Inductive exp : Type :=
  | var : string -> exp
  | plus : exp -> exp -> exp
  | ...
*)
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

(* ~ := not *)

Example e1evalStep1 : e1 , (update X 4 empty) => plus (lit 4) (lit 3).
unfold e1.
Check eval_plus_lhs. apply eval_plus_lhs.
Check eval_var. apply eval_var.
Qed.

Example e1evalStep2 : plus (lit 4) (lit 3) , (update X 4 empty) => lit 7.
apply eval_plus_fin.
Qed.

(* e2 = plus (plus (var X) (lit 3)) (var Y) *)

Example e2evalStep1 : e2 , (update X 4 empty) => plus (plus (lit 4) (lit 3)) (var Y).
unfold e2.
apply eval_plus_lhs.
apply eval_plus_lhs.
apply eval_var.
Qed.

Example e2evalStep2 : plus (plus (lit 4) (lit 3)) (var Y) , (update X 4 empty) => 
                      plus (lit 7) (var Y).
apply eval_plus_lhs.
apply eval_plus_fin.
Qed.

Example e2evalStep3 : plus (lit 7) (var Y) , (update X 4 empty) => 
                      plus (lit 7) (lit 0).
apply eval_plus_rhs.
apply eval_var.
Qed.

Example e2evalStep4 : plus (lit 7) (lit 0) , (update X 4 empty) => 
                      lit 7.
apply eval_plus_fin.
Qed.

Example exStep : plus (lit 5) (plus (plus (plus (lit 2) (var X)) (lit 2)) (lit 3)) , (update X 4 empty) => 
                 plus (lit 5) (plus (plus (plus (lit 2) (lit 4)) (lit 2)) (lit 3)).
Admitted.

(* inversion-t kell hasznalni a _,_=>_ elemeinek a vizsgalatara *)

Lemma lem1 (s : state)(e : exp)(n : nat) : ~ (lit n , s => e).
unfold not. intro. inversion H. Qed.

(* Kihivas: inversion nelkul, destruct H eqn:H1 -al belatni, discriminate -et lehet hasznalni,
   vagy meg azt se. *)

Lemma lem2 : forall n s, 
  ~ (lit n , s => plus (lit n) (lit 0)).
intros. apply lem1. Qed.


Example lem2' : forall n s,
  plus (lit n) (lit 0) , s => lit n.
Admitted.

Lemma notrefl (e : exp)(s : state) : ~ (e , s => e).
intro.
induction e.
 * inversion H.
 * inversion H.
 * inversion H.
   - (* eval_plus_lhs *) apply IHe1. exact H3.
   - (* eval_plus_rhs *) apply IHe2. exact H3.
Qed.  

(* reflexiv, tranzitiv lezart *)

Reserved Notation "e , s =>* e'" (at level 50).

(*
    -----------eval_refl
    e , s =>* e


    e , s => e'        e' , s =>* e''
    ---------------------------------eval_trans
             e , s =>* e''
*)

Inductive evalo_rtc : exp -> state -> exp -> Prop :=
  | eval_refl (e : exp)(s : state) : 

    e , s =>* e

  | eval_trans (e e' e'' : exp)(s : state) :

    e , s => e'    ->    e' , s =>* e'' ->
    (*-------------------------------*)
    e , s =>* e''

  where "e , s =>* e'" := (evalo_rtc e s e').

Example e1eval : e1 , (update X 4 empty) =>* lit 7.
unfold e1.
apply (eval_trans _ (plus (lit 4) (lit 3))).
- apply eval_plus_lhs.
  -- apply eval_var.
- apply (eval_trans _ (lit 7)).
  -- apply eval_plus_fin.
  -- apply eval_refl.
Qed.
(*
 ------var               ---------plus_fin   -------refl
 x => 4                  4+3 => 7            7 =>* 7
 ----------plus_lhs      ---------------------------trans
 x+3 => 4+3                        4+3 =>* 7
 ------------------------------------------------------------trans
  x+3 =>* 7
*)

Example e2eval : e2 , (update X 4 empty) =>* lit 7.

Definition e3 : exp := plus (lit 5) (plus (plus (plus (lit 2) (var X)) (lit 2)) (lit 3)).

Example e3eval : exists (e3' : exp), e3 , (update X 4 empty) =>* e3'.

Example e3eval' : exists (n : nat), e3 , (update X 4 empty) =>* lit n.

Lemma progress (e : exp)(s : state) : (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.

Lemma determ (e e' e'' : exp)(s : state) : e , s => e' /\ e , s => e'' -> e' = e''.

Lemma totality (e : exp)(s : state) : exists (n : nat), e , s =>* lit n.

Lemma denotVsOper (e : exp)(s : state)(n : nat) : e , s =>* lit n <-> evald e s = n.


 