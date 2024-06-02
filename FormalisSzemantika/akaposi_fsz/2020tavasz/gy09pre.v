From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(*
BNF szintaxis:

a,a1,a2,... ::= n | x | a1 + a2 | a1 - a2 | a1 * a2
b,b1,b2,... ::= true | false | b1 && b2 | ~b | a1 = a2 | a1 <= a2
c,c1,c2 ::= SKIP | IF b THEN c1 ELSE c2 | WHILE b DO c END | x ::= a | c1 ;; c2
*)

(* Coq szintaxis: *)

Inductive aexp : Type :=
  | alit (n : nat)
  | avar (x : string)
  | aplus (a1 a2 : aexp)
  | aminus (a1 a2 : aexp)
  | amult (a1 a2 : aexp).

Inductive bexp : Type :=
| btrue
| bfalse
| band (b1 b2 : bexp)
| bnot (b : bexp)
| beq (a1 a2 : aexp)
| bleq (a1 a2 : aexp).

Inductive cmd : Type :=
| cskip (* skip *)
| cif (b : bexp) (c1 c2 : cmd)
| cwhile (b : bexp) (c : cmd)
| cassign (x : string) (a : aexp)
| cseq (c1 c2 : cmd).
(* szep jelolesek: *)
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

(* Pelda kifejezesek: *)
Definition ex1 : bexp := beq (alit 3) (alit 4).
Definition ex1' : bexp := (3 == 4).
Example ex1vsEx1' : ex1 = ex1'. reflexivity. Qed.

Definition ex2 : bexp :=
  band (band (bleq (avar X) (alit 4)) (bnot (beq (alit 1) (avar Y)))) btrue.
(* Ird at ex2'-t ugy, hogy ex2-vel megegyezzen, de szep jelolessel! *)
Definition ex2' : bexp :=
  band (band (bleq (avar X) (alit 4)) (bnot (beq (alit 1) (avar Y)))) btrue.
Example ex2vsEx2' : ex2 = ex2'. reflexivity. Qed.

Definition ex3 : bexp :=
  ~ true & (3 <= 4 & X == Y).
(* Ird at ex3'-t ugy, hogy ex3-al megegyezzen, de a csunya jelolessel! *)
Definition ex3' : bexp :=
  ~ true & (3 <= 4 & X == Y).
Example ex3vsEx3' : ex3 = ex3'. reflexivity. Qed.

(* Fontos kulonbseg a Coq (metaelmeleti) kifejezesek es az
targyprogramunk (objektumeletunk) kifejezesei kozott. *)

Definition ex4 := 1. Check ex4.
Definition ex5 : aexp := 1. Check ex5.
Definition ex6 : nat := 1 + 3 * 2.
Definition ex7 : aexp := 1 + 3 * 2.
Definition ex8 : aexp := 1 + 3 * 2 + X.
(* Definition ex9 : nat := 1 + 3 * 2 + X. *)

(* Peldaprogramok: *)

Definition prog1 : cmd := X ::= 1 ;; X ::= 2.
(* Ird at prog1'-t ugy, hogy prog1-el megegyezzen, de a csunya jelolessel! *)
Definition prog1' : cmd := X ::= 1 ;; X ::= 2.
Example prog1VsProg1' : prog1 = prog1'.
reflexivity. Qed.

Definition inf : cmd := WHILE true DO SKIP END.

Definition fac : cmd :=
  X ::= 1 ;;
  Y ::= 1 ;;
  WHILE Y <= Z DO
    X ::= X * Y ;;
    Y ::= Y + 1
  END.

(* Ird at fac'-t ugy, hogy fac-al megegyezzen, de a csunya jelolessel! *)
Definition fac' : cmd :=
  X ::= 1 ;;
  Y ::= 1 ;;
  WHILE Y <= Z DO
    X ::= X * Y ;;
    Y ::= Y + 1
  END.
Example facVsFac' : ex3 = ex3'. reflexivity. Qed.

(* denotacios szemantika *)

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

Example bevalTip1 : (3 =? 2) = false.
reflexivity. Qed.

Example bevalTip2 : (3 <=? 2) = false.
reflexivity. Qed.

(* Ird meg ezt ugy, hogy be tudjad bizonyitani bevalTest1--bevalTest3-at! *)
Fixpoint beval (b : bexp)(s : state) : bool :=

Example bevalTest1 : beval (true && true) empty = true.

Example bevalTest2 : beval (3 == 4) empty = false.

Example bevalTest3 : beval (X <= (1 + 2 - 3)) empty = true.

(* Mi lenne, ha bool tipusu valtozoink is lennenek? *)

Fixpoint ceval (c : cmd)(s : state) : state :=

Compute ceval prog1 empty 1 X.
Compute ceval prog1 empty 2 X.
Compute ceval prog1 empty 3 X.
Compute ceval prog1 empty 4 X.
Compute ceval fac (update Z 1 empty) 10 X.
Compute ceval fac (update Z 2 empty) 10 X.
Compute ceval fac (update Z 3 empty) 10 X.
Compute ceval fac (update Z 4 empty) 10 X.

Compute ceval inf empty 1 X.
Compute ceval inf empty 2 X.
Compute ceval inf empty 3 X.
Compute ceval inf empty 4 X.

Example prog1eval10 : ceval prog1 empty 10 X = 2.

Example prog1eval1 : exists n : nat, (ceval prog1 empty n X) = 0.

(* Irj programot, mely X erteket megnvoeli eggyel!*)
Example prog2 : exists (c : cmd), forall (n : nat),
  ceval c (update X n empty) 10 X = (n + 1)%nat.
Admitted.

(* Irj programot, mely Y-ba beteszi X ketszereset! *)
Example prog3 : exists (c : cmd), forall (n : nat),
  ceval c (update X n empty) 10 Y = (2 * n)%nat.
Admitted.
