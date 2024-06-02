Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.
Fixpoint height (a : AExp) : nat := match a with
  | ALit n => 0
  | APlus a1 a2 => 1 + max (height a1) (height a2)
  | ASub  a1 a2 => 1 + max (height a1) (height a2)
  end.
(*
forall a, a + 0 = a
forall a, 0 + a = a

0 + a = 
match 0 with
  | O => a
  | S b => S (b + a)
end =
a

a + 0 =
match a with
  | O => 0
  | S b => S (b + 0)
end
*)

Example test_lem (x : nat) : True.
Compute x + 3.
trivial. Qed.

(* egyik hazi: *)
Example notPoss : 
  not (exists (a : AExp), leaves a = 2 /\ height a = 0).
Proof. unfold "~". intro. destruct H. destruct x; simpl in H; destruct H.
- discriminate H.
- discriminate H0.
- discriminate H0.
Qed.

Require Import Coq.Setoids.Setoid.

Example ex (a b c : nat) : a = b -> a + a + c = b + a + c.
intro. rewrite -> H at 2 3. (* IDE NEZZ! *)
rewrite H. reflexivity. Qed.

(*            bevezetes          eliminalas
              (ha ez a Goal)     (ha ez a feltetel)
->            intro              apply
forall        intro              apply
/\            split              destruct
\/            left, right        destruct
exists        exists             destruct
False         -                  destruct
True          trivial            -
=             reflexivity        rewrite
barmi                            assumption
Inductive     (konstruktorok)    destruct, induction
*)

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
(*
Fixpoint optim (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus e1 e2 => match e2 with
    | ALit n => match n with
      | O => optim e1
      | _ => APlus (optim e1) (optim e2)
      end
    | _ => APlus (optim e1) (optim e2)
    end
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.
*)
(*
   +
   /\
  +  0   -> 1
  /\
 1  0

*)
Compute optim (APlus (APlus (ALit 1) (ALit 0)) (ALit 0)).
Compute optim (APlus (APlus (ALit 0) (ALit 1)) (ALit 2)).

Require Import Coq.Arith.Plus.
Check plus_0_r.

Lemma optim_sound (a : AExp) :
  aeval (optim a) = aeval a.
Proof. induction a.
1:{ simpl; reflexivity. }
2:{ simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity. } 
1:{ simpl; destruct a2; try (destruct n); simpl; simpl in IHa1; simpl in IHa2; 
    try (rewrite -> IHa1); try (rewrite -> IHa2); try (symmetry; apply plus_0_r); reflexivity.
  } Qed.

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

Definition optim'' a := ALit (aeval a). (* leghatekonyabb optim, es legegyszerubb bizonyitani, hogy helyes *)

Lemma optim''_sound (a : AExp) : aeval (optim'' a) = aeval a.
Admitted.

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
Compute eval e' (fun x => 2).

Definition update (x : string)(n : nat)(s : state)
  : state := fun x' => match string_dec x x' with
  | left e  => n
  | right ne => s x'
  end.

Check string_dec.

(* W|-> 3, X|->5, Y,Z,_|->0 *)
Definition exState : state := update W 3 (update X 5 empty).

Compute eval e' exState.

Definition st : state := update W 3 empty. (* <- change this so that you can prove e'val! *)

Lemma e'val : eval e' st = 3. reflexivity. Qed.

Definition e'' : exp := lit 0. (* <- change this so that you can prove e''indep! *)

Lemma e''indep : forall (s s' : state), eval e'' s = eval e'' s'. intros. reflexivity. Qed.

Definition e''' : exp := var X. (* valami mas! *)

(*  (X |-> 3, Y |-> 4, Z |-> 22, ... |-> 0) *)
(*  (X |-> 2, Y |-> 4, Z |-> 22, ... |-> 0) *)

Lemma e'''notIndep : ~ (forall (s s' : state),
   eval e''' s = eval e''' s').
intro. assert (eval e''' empty = eval e''' (update X 1 empty)).
apply H. discriminate H0. Qed.
