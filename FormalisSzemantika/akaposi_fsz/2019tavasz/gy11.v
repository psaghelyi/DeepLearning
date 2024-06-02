(* BEGIN FIX *)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

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

(*
a,a1,a2,... ::= n | x | a1 + a2 | a1 - a2 | a1 * a2
b,b1,b2,... ::= true | false | a1 = a2 | a1 <= a2 | ~ b | b1 && b2
c,c1,c2 ::= SKIP | x ::= a | c1 ;; c2 | WHILE b DO c END | 
            TEST b THEN c1 ELSE c2 |
            FOR x IN0TO n DO c END
*)
Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CFor (x : string)(n : nat)(c : com).

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
Notation "'FOR' x 'IN0TO' n 'DO' c 'END'" :=
  (CFor x n c) (at level 80, right associativity) : imp_scope.

Definition exFor : com := FOR X IN0TO 10 DO SKIP END.

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
(* 0..k-1 *)

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
    | CFor x k c =>
        foreval n st c x 0 k
    end
  end
  with
  foreval (f : nat)(st : state)(c : com)
    (x : string)(i k : nat) : state
    := match f with
       | O => st
       | S f' =>
         match k with
         | O => st
         | S k' => foreval f' (ceval f' (update x i st) c) c x (i+1) k'
         end
       end.

Definition exFor1 : com :=
  Y ::= 0 ;;
  FOR X IN0TO 10 DO
    Y ::= Y + X
  END.

Compute (ceval 100 empty exFor1 Y).

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
  | E_ForO : forall st c x,
      st =[ FOR x IN0TO 0 DO c END ]⇒ st
  | E_ForS : forall st st' st'' x c n,
      st =[ FOR x IN0TO n DO c END ]⇒ st' ->
      update x n st' =[ c ]⇒ st'' ->
      st =[ FOR x IN0TO S n DO c END ]⇒ st''

  where "st =[ c ]⇒ st'" := (cevalr c st st').

Definition FOR' (x : string)(a1 a2 : aexp)(c : com) : com
  := x ::= a1 ;;
     WHILE x ≤ a2 DO
       c ;;
       x ::= x + 1
     END.
