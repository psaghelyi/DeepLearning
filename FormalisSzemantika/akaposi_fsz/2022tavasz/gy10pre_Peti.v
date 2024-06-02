From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(*
BNF syntax

a,a1,a2,... ::= n | x | a1 + a2 | a1 - a2 | a1 * a2
b,b1,b2,... ::= true | false | b1 && b2 | ~b | a1 = a2 | a1 <= a2
c,c1,c2 ::= SKIP | IF b THEN c1 ELSE c2 | WHILE b DO c END | x ::= a | c1 ;; c2
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

Definition stmt1 : cmd :=
Definition stmt2 : cmd :=
Definition inf_iter : cmd :=

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
Fixpoint beval (b : bexp)(s : state) : bool :=
match b with
 | btrue => true
 | bfalse => false
 | band b1 b2 => beval b1 s && beval b2 s  (* && = andb *)
 | bnot b => negb (beval b s)
 | beq a1 a2 => aeval a1 s =? aeval a2 s   (* =? = Nat.eqb *)
 | bleq a1 a2 => aeval a1 s <=? aeval a2 s  (* =? = Nat.leb *)
end.

(* Can we also define denotational semantics for programs? *)
Fixpoint ceval (c : cmd)(s : state) : state :=



Compute ceval 0 stmt1 empty X.
Compute ceval 100 stmt1 empty X.
Compute ceval 100 stmt1 astate.
Compute ceval 100 stmt2 empty.
Compute ceval 100 stmt2 astate.

Theorem while_unfolding : forall b S0 s fuel,
  ceval fuel (cwhile b S0) s = ceval (S fuel) (cif b (cseq S0 (SWhile b S0)) SSkip) s.
Proof.

Admitted.

(** A következő tételt be lehetne látni, ha a szemantika `option state`-et
   rendelne egy kifejezéshez. Ha a `fuel` elfogy, akkor az eredmény `None`.*)
(*
Theorem inf_diverges :
  forall fuel st, ~exists st', eval fuel inf_iter st = Some st'.
Proof.

Admitted. *)

Reserved Notation "| s , st | -=> st' " (at level 50).
Inductive eval_bigstep : cmd -> state -> state -> Prop :=

where "| s , st | -=> st' " := (eval_bigstep s st st').

Goal exists st, | stmt1, empty | -=> st.
Proof.

Admitted.

Goal exists st, | stmt2, empty | -=> st.
Proof.

Admitted.