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

Require Import Coq.Arith.Plus.

Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim' e1) (optim' e2)
  | ASub  e1 e2 => ASub  (optim' e1) (optim' e2)
  end.

Compute optim' (APlus (APlus (ALit 1) (ALit 2)) (APlus (ALit 0) (ALit 3))).

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.
Proof. induction a.
- simpl. reflexivity.
- destruct a1, a2; 
  simpl in IHa1; simpl in IHa2; simpl; try(rewrite -> IHa1); try(rewrite -> IHa2); reflexivity.
- simpl in IHa1; simpl in IHa2; simpl; try(rewrite -> IHa1); try(rewrite -> IHa2); reflexivity.
Qed.


Fixpoint optim (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | ASub (ALit x) (ALit y) => ALit (x - y)
  | APlus e1 e2 => APlus (optim e1) (optim e2)
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.

Lemma optim_sound (a : AExp) : aeval (optim a) = aeval a.
Proof. induction a.
- simpl. reflexivity.
- destruct a1, a2.
  + simpl. reflexivity.
  + simpl. simpl in IHa2. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa2. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa1. rewrite IHa1. reflexivity.
  + simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa1. rewrite IHa1. reflexivity.
  + simpl. simpl in IHa1. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa1. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
- destruct a1, a2. 
  + simpl. reflexivity.
  + simpl. simpl in IHa2. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa2. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa1. rewrite IHa1. reflexivity.
  + simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa1. rewrite IHa1. reflexivity.
  + simpl. simpl in IHa1. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
  + simpl. simpl in IHa1. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
Qed.

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

Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | sub e1 e2 => eval e1 s - eval e2 s
  | plus e1 e2 => eval e1 s + eval e2 s
  end.

Definition empty : state := fun x => 0.

Compute eval e' empty.
Compute eval e empty.
Compute eval e' (fun x => 2).

Definition update (x : string)(n : nat)(s : state)
  : state := fun x' => match string_dec x x' with
  | left e  => n
  | right ne => s x'
  end.

Check string_dec.

(* W|-> 3, X|->5, Y,Z|->0 *)
Definition exState : state := update W 3 (update X 5 empty).

Definition st : state := (update W 3 empty). (* <- change this so that you can prove e'val! *)

Lemma e'val : eval e' st = 3.
Proof. unfold e'. unfold st. simpl. reflexivity. Qed.

Definition e'' : exp := sub (lit 0) (var W). (* <- change this so that you can prove e''indep! *)

Lemma e''indep : forall (s s' : state), eval e'' s = eval e'' s'.
intros. unfold e''. Compute 0 - (s "adaffad"%string). simpl. reflexivity. Qed.

Definition e''' : exp := var X. (* valami mas! *)

(*  (X |-> 3, Y |-> 4, Z |-> 22, ... |-> 0) *)
(*  (X |-> 2, Y |-> 4, Z |-> 22, ... |-> 0) *)

Lemma e'''notIndep : ~ (forall (s s' : state),
   eval e''' s = eval e''' s').
intro. assert (eval e''' empty = eval e''' (update X 1 empty)). apply H.
simpl in H0. unfold empty in H0. unfold update in H0. simpl in H0. discriminate H0.
Qed.
(*            bevezetes          eliminalas
              (ha ez a Goal)     (ha ez a feltetel)
->            intro              apply
forall        intro              apply
/\            split              destruct
\/            left,right         destruct
exists        exists             destruct
False                            destruct
True          split              
=             reflexivity        rewrite
              symmetry

induktiv                         destruct, induction

Roviditesek: ~ A = A -> False, (a <> b) = (a = b -> False)
*)


Lemma update_sound (x : string)(n : nat)(s : state) :
  (update x n s) x = n.
unfold update. destruct (string_dec x x).
- reflexivity.
- assert False. unfold "<>" in n0. apply n0. reflexivity. destruct H.
Qed.

Lemma update_neq (x x' : string)(n : nat)(s : state)
  (ne : x <> x') :
  (update x n s) x' = s x'.
Proof. unfold update. destruct (string_dec x x').
- assert False. apply ne. exact e0. destruct H.
- reflexivity.
Qed.

Fixpoint emb (a : AExp) : exp := match a with
  | ALit n => lit n
  | ASub  a1 a2 => sub (emb a1) (emb a2)
  | APlus a1 a2 => plus (emb a1) (emb a2)
  end.

Lemma closed_state (a : AExp)(s s' : state) : 
  eval (emb a) s = eval (emb a) s'.
Proof. induction a.
- simpl. reflexivity.
- simpl; simpl in IHa1; simpl in IHa2. rewrite IHa1; rewrite IHa2. reflexivity.
- simpl; simpl in IHa1; simpl in IHa2. rewrite IHa1; rewrite IHa2. reflexivity.
Qed.

Lemma nemMindAExpbolJon : exists (a : exp), 
  ~ (exists (a' : AExp), emb a' = a) /\ forall (s s' : state), eval a s = eval a s'.
Proof. exists (sub (lit 0) (var W)). split.
- intro. destruct H. destruct x.
-- simpl in H. discriminate H.
-- simpl in H. discriminate H.
-- simpl in H. destruct x2; simpl in H; inversion H.
- intros. reflexivity.
Qed. 
