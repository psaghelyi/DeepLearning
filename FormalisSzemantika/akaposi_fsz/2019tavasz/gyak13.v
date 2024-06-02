Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

(*
a,a1,a2,... ::= n | x | a1 + a2 | a1 - a2 | a1 * a2
b,b1,b2,... ::= true | false | a1 = a2 | a1 <= a2 | ~ b | b1 && b2
  *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x ≤ y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.
Definition example_aexp := (3 + (X * 2)) : aexp.
(* APlus (ANum 3) (AMul (AVar X) (ANum 2)) *)
Definition example_bexp := (true && ~(X ≤ 4)) : bexp.
Definition example_bexp' := BAnd BTrue (BNot (BLe (AId X) (ANum 4))).
Example bexpEq : example_bexp = example_bexp'. reflexivity. Qed.

(*
a,a1,a2,... ::= n | x | a1 + a2 | a1 - a2 | a1 * a2
b,b1,b2,... ::= true | false | a1 = a2 | a1 <= a2 | ~ b | b1 && b2
c,c1,c2 ::= SKIP | x ::= a | c1 ;; c2 | WHILE b DO c END | 
            TEST b THEN c1 ELSE c2
*)
Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity) : imp_scope.

Definition state : Type := string -> nat.
Definition empty : state := fun x => 0.
Definition update (x : string)(n : nat)(s : state)
 : state := fun x' => if eqb x x' then n else s x'.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Fixpoint ceval (f : nat)(st : state)(c : com) : state := 
  match f with
  | O => st
  | S n =>
    match c with
    | CSkip => st
    | CAss x a => update x (aeval st a) st
    | CSeq c1 c2 => ceval n (ceval n st c1) c2  (* c1 ;; c2 *)
    | CIf b c1 c2 => if beval st b then
                       ceval n st c1
                     else
                       ceval n st c2
    | CWhile b c => 
        if beval st b then
          ceval n (ceval n st c) (CWhile b c)
        else
          st
    end
  end.

Reserved Notation "st '=[' c ']⇒' st'"
                  (at level 40).
Inductive cevalr : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]⇒ st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]⇒ (update x n st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]⇒ st' ->
      st' =[ c2 ]⇒ st'' ->
      st =[ c1 ;; c2 ]⇒ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]⇒ st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]⇒ st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]⇒ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]⇒ st' ->
      st' =[ WHILE b DO c END ]⇒ st'' ->
      st =[ WHILE b DO c END ]⇒ st''

  where "st =[ c ]⇒ st'" := (cevalr c st st').

(* some properties of evaluation *)

Example skip_skip : forall s s', s =[ SKIP ;; SKIP ]⇒ s' -> s = s'.
intros.
inversion H. inversion H2. inversion H5. reflexivity. Qed.

Example ceval_skip : forall s s' c, s =[ c ]⇒ s' ->
  s =[ SKIP ;; c ;; SKIP ]⇒ s'.
Proof.
  intros.
  apply E_Seq with s.
  - apply E_Skip.
  - apply E_Seq with s'.
    + exact H.
    + apply E_Skip.
Qed.

Example inc : forall s s', s =[ X ::= X + 1 ]⇒ s' ->
  s X + 1 = s' X.
Admitted.

Example dec : forall s s', s =[ X ::= X - 1 ]⇒ s' ->
  s X - 1 = s' X.
Admitted.

Lemma if_never : forall c1 c2 c3 s s',
  s =[ TEST true THEN c1 ELSE c2 FI ]⇒ s' ->
  s =[ TEST true THEN c1 ELSE c3 FI ]⇒ s'.
Admitted.

Definition c1 : com := X ::= 1.
Definition c2 : com := X ::= 2.
Lemma no_swap : forall s,
  empty =[ c1 ;; c2 ]⇒ s ->
  empty =[ c2 ;; c1 ]⇒ s ->
  False.
intros.
  assert (s X = 2).
  inversion H.
  inversion H6.
  simpl in H11. rewrite <- H11. unfold update. simpl. 
    reflexivity.
  assert (s X = 1).
  inversion H0. inversion H7. simpl in H12. 
    rewrite <- H12. reflexivity.
  rewrite H1 in H2. discriminate H2.
Qed.

Example ass_swap : forall (x y : nat) s1 s2,
  empty =[ X ::= x ;; Y ::= y ]⇒ s1 -> 
  empty =[ Y ::= y ;; X ::= x ]⇒ s2 ->
  s1 X = s2 X. (* /\ s1 Y = s2 Y. *)
intros.
  assert (s2 X = x).
    inversion H0.
    inversion H6.
    simpl in H11.
    rewrite <- H11.
    unfold update. simpl. reflexivity.
  assert (s1 X = x).
    inversion H.
    assert (st' X = x).
      inversion H4.
      simpl in H12. rewrite <- H12. reflexivity.
    inversion H7.
    unfold update. simpl. exact H8.
  rewrite <- H1 in H2.
  exact H2.
Qed.


Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]⇒ st1 ->
     st =[ c ]⇒ st2 ->
     st1 = st2.
Admitted.