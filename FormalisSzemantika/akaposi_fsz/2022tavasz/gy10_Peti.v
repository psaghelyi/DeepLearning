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
| cassign (x : string) (a : aexp) (* x := a *)
| cseq (c1 c2 : cmd) (* c1; c2 *)
| cif (b : bexp) (c1 c2 : cmd) (* IF b THEN c1 ELSE c2 FI *)
| cwhile (b : bexp) (c : cmd). (* WHILE b DO c END *)

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

Definition W := "W"%string. Check W.
Definition X : string := "X".
Definition Y : string := "Y"%string.
Definition Z : string := "Z"%string.

(* Example programs: *)
(* X := 5; Y := X + 1 *)
Definition stmt1 : cmd :=
  cseq (cassign X (alit 5)) (cassign Y (aplus (avar X) (alit 1))).
(*
  X := 0;
  Y := 1;
  while (Y <= 10) and (not (Y = 10)) do
    X := X + Y;
    Y := Y + 1
  end
*)
Definition stmt2 : cmd :=
  cseq (cassign X (alit 0))
       (cseq (cassign Y (alit 1))
             (cwhile (band (bleq (avar Y) (alit 10))
                           (bnot (beq (avar Y) (alit 10)))
                     )
                     (cseq (cassign X (aplus (avar X) (avar Y)))
                           (cassign Y (aplus (avar Y) (alit 1)))
                     )
             )
       ).

Definition inf_iter : cmd :=
  cwhile btrue cskip.

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

Locate "<=". Check le.
Locate "<=?". Check leb.

(* Can we also define denotational semantics for programs? *)
(* functional big-step semantics *)
(* Ha fuel elfogy, lehet hibr jelezni:
 Haskell: Maybe x = Nothing | Just x 
 Coq:     option x := None | Some x
*)
Fixpoint ceval (fuel : nat)(c : cmd)(s : state) : state :=
match fuel with
| 0 => s
| S fuel' =>
  match c with
   | cskip => s
   | cassign x a => update x (aeval a s) s
   | cseq c1 c2 => ceval fuel' c2 (ceval fuel' c1 s)
                  (* let s' := ceval c1 s in ceval c2 s' *)
   | cif b c1 c2 => match beval b s with
                    | true  => ceval fuel' c1 s
                    | false => ceval fuel' c2 s
                    end
                    (* if beval b s then ceval c1 s else ceval c2 s *)
   (* while b do c end ≡ if b then c; while b do c end else skip fi *)
   | cwhile b c => match beval b s with
                   | true  => ceval fuel' (cwhile b c) (ceval fuel' c s)
                   | false => s
                   end
  end
end.
(* FIX F
   F g := cond(⟦b⟧, g ∘ ⟦S⟧, id) *)

Compute ceval 0 stmt1 empty X.
Compute ceval 100 stmt1 empty X.
Compute ceval 100 stmt1 empty Y.
Compute ceval 100 stmt2 empty X.
Compute ceval 100 stmt2 empty Y.

Theorem while_unfolding : forall b S0 s fuel,
  ceval fuel (cwhile b S0) s = ceval (S fuel) (cif b (cseq S0 (cwhile b S0)) cskip) s.
Proof.
  intros. simpl. destruct fuel.
  * simpl. destruct (beval b s) eqn:Eq; reflexivity.
  * simpl. reflexivity.
Qed.

(** A következő tételt be lehetne látni, ha a szemantika `option state`-et
   rendelne egy kifejezéshez. Ha a `fuel` elfogy, akkor az eredmény `None`.*)
(*
Theorem inf_diverges :
  forall fuel st, ~exists st', eval fuel inf_iter st = Some st'.
Proof.

Admitted. *)

Reserved Notation "| s , st | -=> st' " (at level 60).
Inductive eval_bigstep : cmd -> state -> state -> Prop :=

| eval_skip s :
  | cskip , s | -=> s

| eval_assign x a s :
(*  aeval helyett big-steppel:  
      | a, s | -=> n -> | cassign x a, s | -=> update x n s *)
(*______________________________________________  *)
  | cassign x a, s | -=> update x (aeval a s) s

| eval_seq c1 c2 s s' s'' :
  | c1, s | -=> s' -> | c2, s' | -=> s''
->
  | cseq c1 c2, s | -=> s''

| eval_if_true b c1 c2 s s':
  beval b s = true -> | c1, s | -=> s'
->
  | cif b c1 c2, s | -=> s'

| eval_if_false b c1 c2 s s':
  beval b s = false -> | c2, s | -=> s'
->
  | cif b c1 c2, s | -=> s'

| eval_while_true b c s s' s'' :
  beval b s = true ->
  | c, s | -=> s' -> | cwhile b c , s' | -=> s''
->
  | cwhile b c, s | -=> s''

| eval_while_false b c s :
  beval b s = false
->
  | cwhile b c, s | -=> s
where "| s , st | -=> st' " := (eval_bigstep s st st').

Goal exists st, | stmt1, empty | -=> st.
Proof.

Admitted.

Goal exists st, | stmt2, empty | -=> st.
Proof.

Admitted.













