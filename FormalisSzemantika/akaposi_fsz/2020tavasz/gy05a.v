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

Definition exExp' : exp := plus (var W) (sub (var Z) (lit 1)).
(* change this to match the above drawing *)

Definition state : Type := string -> nat.

Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | sub e1 e2 => eval e1 s - eval e2 s
  | plus e1 e2 => eval e1 s + eval e2 s
  end.

Definition empty : state := fun x => 0.

Compute eval exExp' empty.
Compute eval exExp' (fun x => 2).

Compute eqb W X.
Compute eqb W W.

Definition update (x : string)(n : nat)(s : state)
 : state := fun x' => if eqb x x' then n else s x'.

(* W|-> 3, X|->5, Y,Z|->0 *)

Definition exState : state := update W 3 (update X 5 empty).

Definition V : string := "dafhad".
Compute exState V.

Compute empty.
Compute exState.

Compute eval exExp empty.

Definition st : state := update Z 4 empty. (* <- change this so that you can prove exExp'val! *)

Lemma exExp'val : eval exExp' st = 3.
simpl. reflexivity.
Qed.

Definition exExp'' : exp := plus (lit 100) (lit 1). (* <- change this so that you can prove exExp''indep! *)

Lemma exExp''indep : forall (s s' : state), eval exExp'' s = eval exExp'' s'.
intros.
simpl.
reflexivity.
Qed.

Definition exExp''' : exp := var X. (* valami mas! *)

(*  (X |-> 3, Y |-> 4, Z |-> 22, ... |-> 0) *)
(*  (X |-> 2, Y |-> 4, Z |-> 22, ... |-> 0) *)

Lemma expExp'''notIndep : ~ (forall (s s' : state),
   eval exExp''' s = eval exExp''' s').
Proof.
(* ~ A = A -> False *)
intro.
Check (H (update X 3 empty) (update X 2 empty)).
assert (3 = 2).
exact (H (update X 3 empty) (update X 2 empty)).
discriminate H0.
Qed.
(*
pose (X := H (update X 3 empty) (update X 2 empty)).
simpl in X.
simpl in X.
unfold update in X. 
repeat (unfold update in X; simpl in X).
Check X.
discriminate X.
Qed.
*)

(* eval : exp -> (string -> nat) -> nat *)

Lemma update_sound (x : string)(n : nat)(s : state) :
  (update x n s) x = n.
Proof.
unfold update. simpl.
Check eqb_refl.
rewrite -> eqb_refl.
reflexivity.
Qed.
(* https://coq.inria.fr/library/Coq.Strings.String.html *)

(* (x |-> 3, y |-> 4) --x-> 3 *)
(* (x' |-> 5, x |-> 3, y |-> 4) --x-> 3 *)

Lemma update_neq (x x' : string)(n : nat)(s : state)
  (ne : eqb x x' = false) :
  (update x n s) x' = s x'.
unfold update.
rewrite -> ne.
(*
(if (x =? x')%string then n else s x') = s x'
(if false then n else s x') = s x'
    s x'                    = s x'
*)
reflexivity.
Qed.

Fixpoint emb (a : AExp) : exp := match a with
  | ALit n => lit n
  | ASub  a1 a2 => sub (emb a1) (emb a2)
  | APlus a1 a2 => plus (emb a1) (emb a2)
  end.

Lemma closed_state (a : AExp)(s s' : state) : 
  eval (emb a) s = eval (emb a) s'.
Proof.
induction a.
 * simpl. reflexivity.
 * simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
 * simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
Qed.

