Require Import Strings.String.

Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim' e1) (optim' e2)
  | ASub  e1 e2 => ASub  (optim' e1) (optim' e2)
  end.

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.
Proof. induction a.
- simpl. reflexivity.
- simpl. destruct a1; destruct a2; simpl; simpl in IHa1; simpl in IHa2; try (rewrite -> IHa1); try (rewrite -> IHa2); reflexivity.
- simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
Qed.

Definition optim'' a := ALit (aeval a). (* leghatekonyabb optim, es legegyszerubb bizonyitani, hogy helyes *)

Lemma optim''_sound (a : AExp) : aeval (optim'' a) = aeval a.
reflexivity.
Qed.

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
Definition s1 : state := update W 5 empty.

Lemma e1test : eval e1 s1 = 13.
reflexivity. Qed.

Definition s2 : state := update X 1 (update Y 10 (update Z 100 empty)).

(* Ugy add meg e2-t, hogy e2test-et be tudd bizonyitani! *)
Definition e2 : exp := plus (var Z) (plus (var Y) (plus (var Y) (plus (var X) (var X)))).

Lemma e2test : eval e2 empty = 0 /\ eval e2 s2 = 122.
auto. Qed.

Lemma update_sound (x : string)(n : nat)(s : state) :
  (update x n s) x = n.
Proof.
(* tipp *) unfold update. destruct (string_dec x x).
reflexivity. assert (False). apply n0. reflexivity. destruct H.
Qed.

Lemma update_neq (x x' : string)(n : nat)(s : state)
  (ne : x <> x') :
  (update x n s) x' = s x'.
Proof.
(* tipp *) unfold update. destruct (string_dec x x').
assert False. apply ne. assumption. destruct H. reflexivity.
Qed.

(* beagyazzuk a zart kifejezeseket a valtozokat is tartalmazo kifejezesekbe *)
Fixpoint emb (a : AExp) : exp := match a with
  | ALit n => lit n
  | ASub  a1 a2 => sub (emb a1) (emb a2)
  | APlus a1 a2 => plus (emb a1) (emb a2)
  end.

(* egy beagyazott kifejezes erteke nem fugg az allapottol *)
Lemma closed_state (a : AExp)(s s' : state) : 
  eval (emb a) s = eval (emb a) s'.
Proof.
(* tipp *) induction a.
- simpl. reflexivity.
- simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
- simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
Qed.

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

Print e1.

(* Ugy add meg e3-at, hogy e3test-et be tudd bizonyitani! *)
Definition e3 : exp := lit 5.

Lemma e3test : eval (replace e1 W e3) empty = 13.
reflexivity. Qed.

Lemma replaceId (e : exp)(x : string) : replace e x (var x) = e.
Proof.
induction e.
2:{ simpl. destruct (string_dec x s).
(* eddig segitettem *)
- rewrite -> e. reflexivity.
- reflexivity. }
- simpl. reflexivity.
- simpl. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
- simpl. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
Qed.

Lemma replaceAgain (e e' : exp)(x : string) :
  replace (replace e x (lit 3)) x e' = replace e x (lit 3).
Proof.
induction e.
2:{ simpl. destruct (string_dec x s) eqn:H.
(* eddig segitettem *)
-- unfold replace. reflexivity.
-- unfold replace. rewrite -> H. reflexivity. }
- simpl. reflexivity.
- simpl. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
- simpl. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
Qed.
