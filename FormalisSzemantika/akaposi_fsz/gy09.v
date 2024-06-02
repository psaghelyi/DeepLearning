From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(*
BNF syntax

a,a1,a2,... ::= n | x | a1 + a2 | a1 - a2 | a1 * a2
b,b1,b2,... ::= true | false | b1 && b2 | ~b | a1 = a2 | a1 <= a2
c,c1,c2 ::= SKIP | IF b THEN c1 ELSE c2 | WHILE b DO c END | x ::= a | c1 ;; c2

SKIP ;; SKIP     !=     SKIP
(SKIP ;; SKIP) ;; SKIP   !=   SKIP ;; (SKIP ;; SKIP)
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
Definition stmt1 : cmd := X ::= 5 ;; Y ::= X + 1.


Lemma notAssoc : ((SKIP ;; SKIP) ;; SKIP)  <>  (SKIP ;; (SKIP ;; SKIP)).
Proof. intro. discriminate H.
Qed.

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
  WHILE Y <= 10 & ~ Y == 10 DO
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
(* =? = Nat.leb *)
Fixpoint beval (b : bexp)(s : state) : bool := match b with
  | btrue      => true
  | bfalse     => false
  | band b1 b2 => andb (beval b1 s) (beval b2 s)
  | bnot b     => negb (beval b s)
  | beq a1 a2  => Nat.eqb (aeval a1 s) (aeval a2 s)
  | bleq a1 a2 => Nat.leb (aeval a1 s) (aeval a2 s)
end.

Inductive result : Type := 
  | final     : state -> result
  | outoffuel : state -> result.

(* Can we also define denotational semantics for programs? *)
Fixpoint ceval (f : nat)(c : cmd)(s : state) : result := match f with
  | O => outoffuel s
  | S f' => match c with
    | cskip       => final s
    | cif b c1 c2 => if beval b s then ceval f' c1 s else ceval f' c2 s
    | cwhile b c  => if beval b s then
                       match ceval f' c s with
                       | final s'     => ceval f' (cwhile b c) s'
                       | outoffuel s' => outoffuel s'
                       end
                     else final s
    | cassign x a => final (update x (aeval a s) s)
    | cseq c1 c2  => match ceval f' c1 s with
                     | final s'     => ceval f' c2 s'
                     | outoffuel s' => outoffuel s'
                     end
    end
end.

(*
Compute ceval stmt1 empty X.
Compute ceval stmt1 empty Y.
Compute ceval stmt2 (update X 100 empty) X.
Compute ceval stmt2 empty Y.
Compute ceval inf_iter empty X.
*)

Definition unresult (r : result) : state := match r with
  | outoffuel s => s
  | final s => s
  end.
Definition isfinal (r : result) : bool := match r with
  | outoffuel s => false
  | final s => true
  end.

Compute isfinal  (ceval 100 stmt1 empty).
Compute unresult (ceval 100 stmt1 empty) X.
Compute unresult (ceval 100 stmt1 empty) Y.
Compute isfinal  (ceval 15 stmt2 empty).
Compute unresult  (ceval 15 stmt2 empty) X.
Compute unresult  (ceval 15 stmt2 empty) Y.
Compute isfinal  (ceval 200 inf_iter empty).
Compute unresult  (ceval 200 inf_iter empty) X.
Compute unresult  (ceval 2000 inf_iter empty) X.


(* Letezik olyan program, ami nem csinal semmit. *)
Lemma l1 : exists (c : cmd), forall n s, ceval (S n) c s = final s.
Proof.
  exists cskip. intros. reflexivity.
Qed.

(* Letezik olyan program, amely X helyere Y erteket teszi *)
Example prog1 : exists c , exists f, forall s, unresult (ceval f c s) X = s Y.
Proof.
  exists (X ::= Y). exists 1. intros. simpl. reflexivity.
Qed.


(* Letezik vegtelen ciklus. *)
Lemma l2 : exists (c : cmd), forall f s, exists s', ceval f c s = outoffuel s'.
Proof.
  exists (WHILE true DO X ::= X + 1 END).
  intro f.
  induction f.
  all: intro s.
  - simpl.
    exists s.
    reflexivity.
  - simpl.
    destruct (ceval f (X ::= X + 1) s).
    * apply IHf.
    * exists s0. reflexivity.
Qed.



(* WHILE kibontasanak ugyanaz a szemantikaja *)
Theorem while_unfolding : forall b S0 s fuel,
  ceval fuel (cwhile b S0) s = ceval (S fuel) (cif b (cseq S0 (SWhile b S0)) SSkip) s.

(* Letezik vegtelen ciklus, ami nem csinal semmit. *)
Lemma l3 : exists (c : cmd), forall s, forall n, ceval c s n = outoffuel s.
  exists (WHILE true DO SKIP END). intro. induction f. intros.
  - simpl. exists s. reflexivity.
  - simpl. destruct f; simpl.
  -- simpl in IHf. assumption.
  -- 
  
Qed.


