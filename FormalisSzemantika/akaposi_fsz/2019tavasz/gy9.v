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

Definition prog  : com := X ::= 1 ;; X ::= 2.
Definition prog' : com := CSeq (CAss X (ANum 1)) (CAss X (ANum 2)).
Definition inf : com := WHILE true DO SKIP END.
Definition fac : com :=
  X ::= 1 ;;
  Y ::= 1 ;;
  WHILE Y ≤ Z DO
    X ::= X * Y ;;
    Y ::= Y + 1
  END.

(* kiszamolja a 1000!-t *)

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

Compute ceval 1000 empty inf.
Compute ceval 12 (update Z 100 empty) fac X.

(*
Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
*)

