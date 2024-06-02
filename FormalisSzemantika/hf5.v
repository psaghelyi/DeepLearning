Require Import Strings.String.

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
  : state := fun x' => match string_dec x x' with
  | left e  => n
  | right ne => s x'
  end.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition e1 : exp := plus (var W) (plus (var W) (lit 3)).

(* Ugy add meg s1-et, hogy e1test-et be tudd bizonyitani! *)
Definition s1 : state := empty.

Lemma e1test : eval e1 s1 = 13.
Admitted.

Definition e1' : exp := plus (var X) (sub (lit 2) (var X)).

(* Ugy add meg s1'-et, hogy e1test-et be tudd bizonyitani! *)
Definition s1' : state := empty.

Lemma e1'test : eval e1' s1' = 10.
Admitted.


Definition s2 : state := update X 1 (update Y 10 (update Z 100 empty)).

(* Ugy add meg e2-t, hogy e2test-et be tudd bizonyitani! *)
Definition e2 : exp := lit 0.

Lemma e2test : eval e2 empty = 0 /\ eval e2 s2 = 122.
Admitted.

Definition s2' : state := update X 1 (update Y 3 empty).

(* Ugy add meg e2-t, hogy e2test-et be tudd bizonyitani! *)
Definition e2' : exp := lit 0.

Lemma e2'test : eval e2' empty = 1 /\ eval e2' s2' = 9.
Admitted.

Lemma nincs : ~ (exists e, eval (sub (lit 0) e) empty = 3).
Admitted.

(* replace e x e' az e-ben az x valtozok helyere e'-t helyettesitunk. *)
Fixpoint replace (e : exp)(x : string)(e' : exp) : exp :=
  match e with
  | lit n => lit n
  | var x' => match string_dec x x' with
    | left _  => e'
    | right _ => var x'
    end
  | sub e1 e2 => sub (replace e1 x e') (replace e2 x e')
  | plus e1 e2 => plus (replace e1 x e') (replace e2 x e')
  end.

(* Ugy add meg e3-at, hogy e3test-et be tudd bizonyitani! *)
Definition e3 : exp := var X.

Lemma e3test : eval (replace e1 W e3) empty = 13.
Admitted.

Lemma replaceId (e : exp)(x : string) : replace e x (var x) = e.
Proof.
induction e.
2:{ simpl. destruct (string_dec x s).
(* eddig segitettem *)
Admitted.

Lemma replaceAgain (e e' : exp)(x : string) :
  replace (replace e x (lit 3)) x e' = replace e x (lit 3).
Proof.
induction e.
2:{ simpl. destruct (string_dec x s) eqn:H.
(* eddig segitettem *)
Admitted.
