From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(*
BNF syntax

a,a1,a2,... ::= n | x | a1 + a2 | a1 - a2 | a1 * a2
b,b1,b2,... ::= true | false | b1 && b2 | ~b | a1 = a2 | a1 <= a2
c,c1,c2,... ::= SKIP | IF b THEN c1 ELSE c2 FI | WHILE b DO c END | x ::= a | c1 ;; c2
*)

(* Syntax in Coq: *)

(* arith expressions *)
Inductive aexp : Type :=
| alit (n : nat)
| avar (x : string)
| aplus (a1 a2 : aexp)
| aminus (a1 a2 : aexp)
| amult (a1 a2 : aexp).

(* boolean expression *)
Inductive bexp : Type :=
| btrue
| bfalse
| band (b1 b2 : bexp)
| bnot (b : bexp)
| beq (a1 a2 : aexp)
| bleq (a1 a2 : aexp).

(* commands *)
Inductive cmd : Type :=
| cskip (* skip *)
| cif (b : bexp) (c1 c2 : cmd)
| cwhile (b : bexp) (c : cmd)
| cassign (x : string) (a : aexp)
| cseq (c1 c2 : cmd).

(* Notations: *)
Coercion avar : string >-> aexp.
Coercion alit : nat >-> aexp.
Notation "x + y"     := (aplus x y) (at level 50, left associativity).
Notation "x - y"     := (aminus x y) (at level 50, left associativity).
Notation "x * y"     := (amult x y) (at level 40, left associativity).
Definition bool2bexp (b : bool) : bexp := if b then btrue else bfalse.
Coercion bool2bexp : bool >-> bexp.
Notation "x & y" := (band x y) (at level 81, left associativity).
Notation "'~' b" := (bnot b) (at level 75, right associativity).
Notation "x == y" := (beq x y) (at level 70, no associativity).
Notation "x <= y" := (bleq x y) (at level 70, no associativity).
Notation "'SKIP'"    := cskip.
Notation "'IF' b 'THEN' c1 'ELSE' c2 'FI'" := (cif b c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := (cwhile b c) (at level 80, right associativity).
Notation "x '::=' a" := (cassign x a) (at level 60).
Notation "c1 ;; c2"  := (cseq c1 c2) (at level 80, right associativity).

Definition X : string := "X"%string.
Definition Y : string := "Y"%string.
Definition Z : string := "Z"%string.

(* Example programs: *)

(* X := 5; Y := X + 1 *)
Definition stmt1 : cmd := 
  cseq (cassign X (alit 5)) (cassign Y (aplus (avar X) (alit 1))).
Print stmt1.
Definition stmt1' : cmd := X ::= 5;; Y ::= X + 1.

(*
  X := 0;
  Y := 1;
  while (Y <= 10) and (not (Y = 10)) do
    X := X + Y;
    Y := Y + 1
  end
*)
Definition stmt2 : cmd :=
  X ::= 0 ;;
  Y ::= 1 ;;
  WHILE (Y <= 10) & (~ (Y == 10)) DO
    X ::= X + Y ;;
    Y ::= Y + 1
  END.

(* vegtelen ciklus *)
Definition inf_iter : cmd := WHILE true DO X ::= X + 1 END.

Definition state : Type := string -> nat.
Definition empty : state := fun x => 0.

Definition update (x:string)(n:nat)(s:state) : state :=
  fun x' => match string_dec x x' with
  | left  e => n
  | right e => s x'
  end.

Fixpoint aeval (a : aexp)(s : state) : nat :=
match a with
| alit n => n
| avar x => s x
| aplus a1 a2 => (aeval a1 s) + (aeval a2 s)
| aminus a1 a2 => (aeval a1 s) - (aeval a2 s)
| amult a1 a2 => (aeval a1 s) * (aeval a2 s)
end.

(* Define the denotational semantics for boolean expressions! *)
(* && = andb *)
(* =? = Nat.eqb *)
(* <=? = Nat.leb *)
Fixpoint beval (b : bexp)(s : state) : bool := match b with
  | btrue => true
  | bfalse => false
  | band b1 b2 => beval b1 s && beval b2 s
  | bnot b => negb (beval b s)
  | beq a1 a2 => aeval a1 s =? aeval a2 s
  | bleq a1 a2 => aeval a1 s <=? aeval a2 s
  end.

(*
Fixpoint f (n : nat) : nat := match n with
  | O => 3
  | S n => 1 + f (S n)
  end.
(* f (S (S O)) = 1 + f (S (S O)) = 1 + 1 + f (S (S O)) = ... *)
*)

Inductive result : Type := 
  | final     : state -> result
  | outoffuel : state -> result.


(* Can we also define denotational semantics for programs? *)
Fixpoint ceval (c : cmd)(s : state) (fuel : nat) : result := match fuel with
  | O => outoffuel s
  | S fuel => match c with
    | cskip => final s
    | cif b c1 c2 => if beval b s then ceval c1 s fuel else ceval c2 s fuel
    | cwhile b c => if beval b s
        then 
          match ceval c s fuel with
          | outoffuel s => outoffuel s
          | final s => ceval (cwhile b c) s fuel
          end
        else final s
    | cassign x a => final (update x (aeval a s) s)
    | cseq c1 c2 => match ceval c1 s fuel with
      | outoffuel s => outoffuel s
      | final s => ceval c2 s fuel
      end
    end
  end.

Inductive result' : Type :=
  | outoffuel' : nat -> result'
  | final'     : nat -> result'.

Definition ceval' (c : cmd)(s : state) (fuel : nat)(x : string) : result' :=
  match ceval c s fuel with
  | outoffuel s => outoffuel' (s x)
  | final s     => final' (s x)
  end.

(* X := 5; Y := X + 1 *)
Compute ceval' (X ::= 5) empty 1 X.
Compute ceval' stmt1 empty 1 Y.
Compute ceval' stmt1 empty 2 Y.
Compute ceval' stmt1 empty 3 Z.
Compute ceval' stmt1 empty 100 Y.
Compute ceval' (X ::= X) empty 100 X.
Compute ceval' (X ::= X + 3) empty 100 X.
Compute ceval' (X ::= X + 3 ;; IF X <= 2 THEN Y ::= 1 ELSE Y ::= 2 FI) empty 100 Y.
Compute ceval' inf_iter empty 1009 X.
Compute ceval' stmt2 empty 13 X.

(* Letezik olyan program, ami nem csinal semmit. *)
Lemma l1 : exists (c : cmd), forall n s, ceval c s (S n) = final s.
Proof. exists SKIP. intros. simpl. reflexivity. Qed.

(* Letezik olyan program, amely X helyere Y erteket teszi *)
Example prog1 : exists c , exists f, forall s, ceval' c s f X = final' (s Y).
exists (X ::= Y). exists 1. intros. unfold ceval'. simpl. unfold update. simpl. reflexivity.
Qed.

(* Letezik vegtelen ciklus. *)
Lemma l2 : exists (c : cmd), forall n s, exists s', ceval c s n = outoffuel s'.

(* WHILE kibontasanak ugyanaz a szemantikaja *)
Theorem while_unfolding : forall b S0 s fuel,
  ceval fuel (cwhile b S0) s = ceval (S fuel) (cif b (cseq S0 (SWhile b S0)) SSkip) s.

.(* Letezik vegtelen ciklus, ami nem csinal semmit. *)
Lemma l3 : exists (c : cmd), forall s, forall n, ceval c s n = outoffuel s.


