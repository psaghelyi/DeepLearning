(* BEGIN FIX *)
From Coq Require Import Strings.String.

Inductive exp : Type :=
  | lit : nat -> exp
  | var : string -> exp
  | sub : exp -> exp -> exp
  | plus : exp -> exp -> exp.

Definition state : Type := string -> nat.

Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | sub e1 e2 => eval e1 s - eval e2 s
  | plus e1 e2 => eval e1 s + eval e2 s
  end.

Definition empty : state := fun x => 0.

Definition update (x : string)(n : nat)(s : state)
 : state := fun x' => if eqb x x' then n else s x'.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition e1 : exp := plus (var W) (plus (var W) (lit 3)).

(* Ugy add meg s1-et, hogy e1test-et be tudd bizonyitani! *)
Definition s1 : state := 
(* END FIX *)
  update W 5 empty.

(* BEGIN FIX *)
Lemma e1test : eval e1 s1 = 13.
(* END FIX *)
reflexivity.
Qed.

(* BEGIN FIX *)
Definition s2 : state := update X 1 (update Y 10 (update Z 100 empty)).

(* Ugy add meg e2-t, hogy e2test-et be tudd bizonyitani! *)
Definition e2 : exp := 
(* END FIX *)
  plus (var Z) (plus (var X) (plus (var X) (plus (var Y) (var Y)))).
    
(* BEGIN FIX *)
Lemma e2test : eval e2 empty = 0 /\ eval e2 s2 = 122.
(* END FIX *)
split. reflexivity. reflexivity.
Qed. 

(* BEGIN FIX *)
(* replace e x e' az e-ben az x valtozok helyere e'-t helyettesitunk. *)
Fixpoint replace (e : exp)(x : string)(e' : exp) : exp :=
  match e with
  | lit n => lit n
  | var x' => if eqb x x' then e' else var x'
  | sub e1 e2 => sub (replace e1 x e') (replace e2 x e')
  | plus e1 e2 => plus (replace e1 x e') (replace e2 x e')
  end.

(* Ugy add meg e3-at, hogy e3test-et be tudd bizonyitani! *)
Definition e3 : exp := 
(* END FIX *)
  lit 5.

(* BEGIN FIX *)
Lemma e3test : eval (replace e1 W e3) empty = 13.
(* END FIX *)
reflexivity.
Qed.

(* replaceAgain-ben erdemes hasznalni a destruct ... eqn:H taktikat. *)
(* BEGIN FIX *)
Lemma replaceAgain (e e' : exp)(x : string) :
(* END FIX *)
  replace (replace e x (lit 3)) x e' = replace e x (lit 3).
  induction e.
  * simpl. reflexivity.
  * simpl. destruct (eqb x s) eqn:H.
    - simpl. reflexivity.
    - simpl. rewrite -> H. reflexivity.
  * simpl. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
  * simpl. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
Qed.

Check eqb_eq.
(* isEqb-hez hasznald eqb_eq-t! Hasznos a pose taktika. *)
(* BEGIN FIX *)
Lemma isEqb_true (x s : string)(e : eqb x s = true) : x = s.
(* END FIX *)
Check (eqb_eq x s).
pose (eqb_eq x s).
destruct i.
exact (H e).
Qed.

(* replaceId-ben erdemes hasznalni a destruct ... eqn:H taktikat. *)
(* BEGIN FIX *)
Lemma replaceId (e : exp)(x : string) : replace e x (var x) = e.
(* END FIX *)
induction e.
 * simpl. reflexivity.
 * simpl. destruct (eqb x s) eqn:H.
   - Check isEqb_true x s H. rewrite -> (isEqb_true x s H). reflexivity.
   - reflexivity.
 * simpl. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
 * simpl. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
Qed.
