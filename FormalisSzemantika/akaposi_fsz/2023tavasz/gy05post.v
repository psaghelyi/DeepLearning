Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

Fixpoint optim (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus e1 (ALit 0) => optim e1
  | APlus e1 e2 => APlus (optim e1) (optim e2)
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.

Compute optim (APlus (APlus (ALit 1) (ALit 0)) (ALit 0)).

Require Import Coq.Arith.Plus.
Check plus_0_r.

Lemma optim_sound (a : AExp) :
  aeval (optim a) = aeval a.
Proof. induction a.
Admitted.

Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim' e1) (optim' e2)
  | ASub  e1 e2 => ASub  (optim' e1) (optim' e2)
  end.

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.
Proof. induction a.
Admitted.

Definition optim'' a := ALit (aeval a).

Lemma optim''_sound (a : AExp) : aeval (optim'' a) = aeval a.
reflexivity. Qed.

(* bevezetjuk a valtozokat *)

Require Import Strings.String.

(* lecsereljuk AExp-et erre: *)
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
e :=
   +
  / \
  W  3
*)

Definition e : exp := plus (var W) (lit 3). (* javitsd ki, hogy ugy nezzen ki, mint a rajz! *)

(*
e' :=
   +
  / \
  W  -
    / \
   Z   1
*)

Definition e' : exp := plus (var W) (sub (var Z) (lit 1)).
(* javitsd ki, hogy ugy nezzen ki, mint a rajz! *)

Definition state : Type := string -> nat.

(* exp jelentese egy state -> nat *)
Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | sub e1 e2 => eval e1 s - eval e2 s
  | plus e1 e2 => eval e1 s + eval e2 s
  end.

Definition empty : state := fun x => 0.

Compute eval e' empty.
Compute eval e' (fun x => 2).

Check string_dec.

(*  update x n s =   s[x|->n] felulirjuk az x valtozo erteket n-el *)
Definition update (x : string)(n : nat)(s : state)
  : state := fun x' => match string_dec x x' with
  | left e  => n
  | right ne => s x'
  end.

(* W|-> 3, X|->5, Y,Z|->0 *)
Definition exState : state := update W 3 (update X 5 empty).

Check empty. (* state = (string -> nat) *)
Compute (exState "W"%string).
Compute (exState X).

Definition st : state := update Z 4 empty. (* <- change this so that you can prove e'val! *)

Lemma e'val : eval e' st = 3.
Proof. simpl. reflexivity. Qed.

Definition e'' : exp := lit 3. (* <- change this so that you can prove e''indep! *)

Lemma e''indep : forall (s s' : state), eval e'' s = eval e'' s'.
Proof. intros. simpl. reflexivity. Qed.

Definition e''' : exp := var X. (* valami mas! *)

(*  (X |-> 3, Y |-> 4, Z |-> 22, ... |-> 0) *)
(*  (X |-> 2, Y |-> 4, Z |-> 22, ... |-> 0) *)

Lemma e'''notIndep : ~ (forall (s s' : state),
   eval e''' s = eval e''' s').
Proof. intro. 
Compute (eval e''' empty).
Compute (eval e''' (update X 1 empty)).
assert (eval e''' empty = eval e''' (update X 1 empty)).
* apply H.
* simpl in H0. unfold empty in H0. simpl in H0. unfold update in H0. simpl in H0.
  discriminate H0.
Qed.

About "=".
Check eq_refl.

(*
  ~ (forall n, P n) <-> (exists n, ~ P n)

   (forall (b : Bool), P b) <-> (P true /\ P false)
   (exists (b : Bool), P b) <-> (P true \/ P false)

*)

(*Lemma seged : forall (x : string), string_dec x x = inl eq_refl.*)

Lemma update_sound (x : string)(n : nat)(s : state) :
  (update x n s) x = n.
unfold update. Check (string_dec x x). destruct (string_dec x x).
* reflexivity.
* (* unfold "~" in n0. *) unfold "<>" in n0. assert False. apply n0. reflexivity.
  destruct H.
Qed.

Lemma update_neq (x x' : string)(n : nat)(s : state)
  (ne : x <> x') :
  (update x n s) x' = s x'.
Proof. unfold update. destruct (string_dec x x').
2: { reflexivity. }
1: { exfalso. unfold "<>" in ne. apply ne. assumption. }
Qed.
(* admit. atmenetileg nem oldjuk meg az aktualis fokuszt *)
(* fokuszalas *)

Fixpoint emb (a : AExp) : exp := match a with
  | ALit n => lit n
  | ASub  a1 a2 => sub (emb a1) (emb a2)
  | APlus a1 a2 => plus (emb a1) (emb a2)
  end.

Lemma closed_state (a : AExp)(s s' : state) : 
  eval (emb a) s = eval (emb a) s'.
Proof. induction a.
1: { simpl. reflexivity. }
2: { simpl. rewrite IHa1; rewrite IHa2; reflexivity. }
* simpl. rewrite IHa1; rewrite IHa2; reflexivity.
Qed.

(*eval (emb (APlus a1 a2)) s = 
  eval (plus (emb a1) (emb a2)) s =
  eval (emb a1) s + eval (emb a2) s
*)

(* kovetkezo gyakorlat 4 perccel rovidebb *)