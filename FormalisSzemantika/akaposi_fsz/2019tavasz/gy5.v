(* n | x | a1 + a2 | a1 − a2 | -a *)

From Coq Require Import Strings.String.

Inductive exp : Type :=
  | num : nat -> exp
  | var : string -> exp
  | plus : exp -> exp -> exp
  | minus : exp -> exp -> exp.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition exExp : exp := plus (var W) (num 3).

Definition state : Type := string -> nat.

Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | num n => n
  | var x => s x
  | plus e1 e2 => eval e1 s + eval e2 s
  | minus e1 e2 => eval e1 s - eval e2 s
  end.

Definition empty : state := fun x => 0.

Eval compute in eqb W X.

Definition update (x : string)(n : nat)(s : state)
 : state := fun x' => if eqb x x' then n else s x'.

(* W|-> 3, X|->5, Y,Z|->0 *)

Definition exState : state := update W 3 (update X 5 empty).

Eval compute in exState.

Eval compute in eval exExp empty.

Lemma update_sound (x : string)(n : nat)(s : state) :
  (update x n s) x = n.
unfold update. Check (eqb_refl x). rewrite -> (eqb_refl x).
reflexivity. Qed.

(* HF: update nem valtoztatja a tobbi valtozo erteket *)

Inductive clexp : Type :=
  | clnum : nat -> clexp
  | clplus : clexp -> clexp -> clexp
  | clminus : clexp -> clexp -> clexp.

Fixpoint emb (ce : clexp) : exp := match ce with
  | clnum n => num n
  | clplus ce1 ce2 => plus (emb ce1) (emb ce2)
  | clminus ce1 ce2 => minus (emb ce1) (emb ce2)
  end.

Lemma closed_state (ce : clexp)(s s' : state) : 
  eval (emb ce) s = eval (emb ce) s'.
Proof.
  induction ce.
  unfold emb. unfold eval. reflexivity.
  all: (simpl; rewrite -> IHce1; 
       rewrite -> IHce2; reflexivity).
Qed.

Inductive step1 : exp -> state -> nat -> Prop :=
  | snum (n : nat)(s : state) : step1 (num n) s n
  | svar (x : string)(s : state) : step1 (var x) s (s x)
  | splus (n : nat)(a2 : exp)(s : state)(i : nat) :
          step1 a2 s i -> 
          step1 (plus (num n) a2) s (n + i).
(* HF: sminus *)

Inductive step2 : exp -> state -> exp -> state -> Prop :=
  | splus2 (a1 a2 a1' : exp)(s : state) :
           step2 a1 s a1' s -> 
           step2 (plus a1 a2) s (plus a1' a2) s.
(* HF: tobbi eset *)






