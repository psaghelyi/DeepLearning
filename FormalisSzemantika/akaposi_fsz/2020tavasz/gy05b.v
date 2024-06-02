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

Definition exExp' : exp := plus (var W) (sub (var Z) (lit 1)). (* change this to match the above drawing *)

Definition state : Type := string -> nat.

Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | sub e1 e2 => eval e1 s - eval e2 s
  | plus e1 e2 => eval e1 s + eval e2 s
  end.

Definition empty : state := fun x => 0.

Compute eval exExp empty.
Compute eval exExp' empty.
Compute eval exExp' (fun _ => 3).
Compute eval exExp' (fun _ => 4).

Compute eqb W X.
Compute eqb W W.

Definition update (x : string)(n : nat)(s : state)
 : state := fun x' => if eqb x x' then n else s x'.

(* W|-> 3, X|->5, Y,Z|->0 *)

Definition exState : state := update W 3 (update X 5 empty).

Compute exState W.
Compute exState X.
Compute exState Z.

Compute exState.

Compute eval exExp empty.

Definition st : state := update Z 3 (update W 1 empty). (* <- change this so that you can prove exExp'val! *)

Lemma exExp'val : eval exExp' st = 3.
simpl.
reflexivity.
Qed.

Definition exExp'' : exp := lit 10. (* <- change this so that you can prove exExp''indep! *)

Lemma exExp''indep : forall (s s' : state), eval exExp'' s = eval exExp'' s'.
intros. simpl. reflexivity. Qed.

Definition exExp''' : exp := var X.

(* ~ A = A -> False *)

Lemma expExp'''notIndep : ~ (forall (s s' : state),
   eval exExp''' s = eval exExp''' s').
unfold not. intro. unfold exExp''' in H. simpl in H.
assert (2 = 3). exact (H (update X 2 empty) (update X 3 empty)).
discriminate H0.
Qed.

(*
H (update X 2 empty) (update X 3 empty)
     : update X 2 empty X =
       update X 3 empty X
     : (update X 2 empty) X =
       (update X 3 empty) X
     : 2 =
       3
  *)

(* rewrite -> ... *)
Check eqb_refl.

Lemma update_sound (x : string)(n : nat)(s : state) :
  (update x n s) x = n.
unfold update.
Check eqb_refl.
(*
(if (x =? x)%string then n else s x) = n

(if true then n else s x) = n

(n) = n
*)
rewrite -> eqb_refl.
reflexivity.
Qed.

(* = : A -> A -> Prop
  =? : string -> string -> bool
  =? : nat -> nat -> bool
*)

Lemma update_neq (x x' : string)(n : nat)(s : state)(ne : eqb x x' = false) :
  (update x n s) x' = s x'.
Proof.
  unfold update. rewrite -> ne. reflexivity. Qed.

Fixpoint emb (a : AExp) : exp := match a with
  | ALit n => lit n
  | ASub  a1 a2 => sub (emb a1) (emb a2)
  | APlus a1 a2 => plus (emb a1) (emb a2)
  end.

Compute eval (emb (APlus (ALit 3) (ALit 100))) ( st).

Lemma closed_state (a : AExp)(s s' : state) : 
  eval (emb a) s = eval (emb a) s'.
Proof.
  induction a;
  simpl;
  try (rewrite -> IHa1; rewrite -> IHa2);
  reflexivity.
Qed.
