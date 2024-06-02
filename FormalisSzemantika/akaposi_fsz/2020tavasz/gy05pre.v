From Coq Require Import Strings.String.

Inductive AExp : Type :=
  | ALit (n : nat)
  | ASub (a1 a2 : AExp)
  | APlus (a1 a2 : AExp).

Fixpoint aeval (a : AExp) : nat :=
  match a with
  | ALit n      => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | ASub  a1 a2 => aeval a1 - aeval a2
  end.

Inductive exp : Type :=
  | lit : nat -> exp
  | var : string -> exp
  | sub : exp -> exp -> exp
  | plus : exp -> exp -> exp.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(*
exExp :=
   +
  / \
  W  3
*)

Definition exExp : exp := plus (var W) (lit 3).

(*
exExp' :=
   +
  / \
  W  -
    / \
   Z   1
*)

Definition exExp' : exp := lit 1. (* change this to match the above drawing *)

Definition state : Type := string -> nat.

Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | sub e1 e2 => eval e1 s - eval e2 s
  | plus e1 e2 => eval e1 s + eval e2 s
  end.

Definition empty : state := fun x => 0.

Compute exExp empty.
Compute exExp' empty.
Compute exExp' (fun _ => 3).
Compute exExp' (fun _ => 4).

Compute eqb W X.

Definition update (x : string)(n : nat)(s : state)
 : state := fun x' => if eqb x x' then n else s x'.

(* W|-> 3, X|->5, Y,Z|->0 *)

Definition exState : state := update W 3 (update X 5 empty).

Compute exState.

Compute eval exExp empty.

Definition st : state := empty. (* <- change this so that you can prove exExp'val! *)

Lemma exExp'val : eval exExp' st = 3.


Definition exExp'' : exp := var W. (* <- change this so that you can prove exExp''indep! *)

Lemma exExp''indep : forall (s s' : state), eval exExp'' s = eval exExp'' s'.


Definition exExp''' : exp := var X. (* valami mas! *)



Lemma expExp'''notIndep : ~ (forall (s s' : state),
   eval exExp''' s = eval exExp''' s').



Lemma update_sound (x : string)(n : nat)(s : state) :
  (update x n s) x = n.


Lemma update_neq (x x' : string)(n : nat)(s : state)(ne : eqb x x' = false)  :
  (update x n s) x' = s x'.


Fixpoint emb (a : AExp) : exp := match a with
  | ALit n => lit n
  | ASub  a1 a2 => sub (emb a1) (emb a2)
  | APlus a1 a2 => plus (emb a1) (emb a2)
  end.

Lemma closed_state (a : AExp)(s s' : state) : 
  eval (emb a) s = eval (emb a) s'.
