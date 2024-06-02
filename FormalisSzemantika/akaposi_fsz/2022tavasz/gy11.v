From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

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
| cassign (x : string) (a : aexp) (* x := a *)
| cseq (c1 c2 : cmd) (* c1; c2 *)
| cif (b : bexp) (c1 c2 : cmd) (* IF b THEN c1 ELSE c2 FI *)
| cwhile (b : bexp) (c : cmd). (* WHILE b DO c END *)
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
Fixpoint beval (b : bexp)(s : state) : bool :=
match b with
 | btrue => true
 | bfalse => false
 | band b1 b2 => beval b1 s && beval b2 s  (* && = andb *)
 | bnot b => negb (beval b s)
 | beq a1 a2 => aeval a1 s =? aeval a2 s   (* =? = Nat.eqb *)
 | bleq a1 a2 => aeval a1 s <=? aeval a2 s  (* =? = Nat.leb *)
end.
Inductive result : Type :=
  | final : state -> result
  | outoffuel : state -> result.
Definition fromResult (r : result) : state := match r with
  | final s => s
  | outoffuel s => s
  end.
Fixpoint ceval (c : cmd)(s : state)(n : nat) : result := match n with
  | O => outoffuel s
  | S n' => match c with
    | cskip       => final s
    | cif b c1 c2 => if beval b s then ceval c1 s n' else ceval c2 s n'
    | cwhile b c  => if beval b s then match ceval c s n' with
                                  | final s' => ceval (cwhile b c) s' n'
                                  | r => r
                                  end
                                  else final s
    | cassign x a => final (update x (aeval a s) s)
    | cseq c1 c2  => match ceval c1 s n' with
                     | final s' => ceval c2 s' n'
                     | r => r
                     end
    end
 end.

Reserved Notation "| s , st | -=> st' " (at level 60).
Inductive eval_bigstep : cmd -> state -> state -> Prop :=
| eval_skip s :
  | cskip , s | -=> s
| eval_assign x a s :
  | cassign x a, s | -=> update x (aeval a s) s
| eval_seq c1 c2 s s' s'' :
  | c1, s | -=> s' -> | c2, s' | -=> s'' ->
  | cseq c1 c2, s | -=> s''
| eval_if_true b c1 c2 s s':
  beval b s = true -> | c1, s | -=> s' ->
  | cif b c1 c2, s | -=> s'
| eval_if_false b c1 c2 s s':
  beval b s = false -> | c2, s | -=> s' ->
  | cif b c1 c2, s | -=> s'
| eval_while_true b c s s' s'' :
  beval b s = true ->
  | c, s | -=> s' -> | cwhile b c , s' | -=> s'' ->
  | cwhile b c, s | -=> s''
| eval_while_false b c s :
  beval b s = false ->
  | cwhile b c, s | -=> s
where "| s , st | -=> st' " := (eval_bigstep s st st').

(* eval_bigstep (WHILE btrue DO SKIP END) : state -> state -> Prop
   := fun s s' => False
  *)

Example prog1 : exists c , exists f, forall s, fromResult (ceval c s f) X = s Y.
exists (X ::= Y). exists 1. intros. compute. reflexivity.
Qed.

Definition statefun1 : state -> state := fun s => 
  fromResult (ceval (X ::= Y) s 1)
 . (* ugy add meg, hogy statefunProp bizonyithato legyen! *)

Definition statefun2 : state -> state := fun s => update X (s Y) s. (* ugy add meg, hogy statefunProp bizonyithato legyen! *)

Example statefunProp : forall s, statefun1 s X = s Y /\ statefun2 s X = s Y.
intros. split; reflexivity.
Qed.

(* Letezik olyan program, ami nem csinal semmit. *)
Lemma l1 : exists (c : cmd), forall n s, ceval c s (S n) = final s.
exists SKIP. intros. reflexivity. Qed.

(* Letezik vegtelen ciklus. *)
Lemma l2 : exists (c : cmd), forall n s, exists s', ceval c s n = outoffuel s'.
exists (WHILE 1 == 1 DO X ::= 1 END). intro n. induction n. 
- intros. exists s. simpl. reflexivity.
- intros. simpl. destruct (ceval (X ::= 1) s n).
-- apply IHn.
-- exists s0. reflexivity.
Qed.

(*
ceval(WHILE 1 == 1 DO X ::= 1 END) (update X 1 s) n = outoffuel (update X 1 s)
*)

(* Letezik vegtelen ciklus, ami nem csinal semmit. *)
Lemma l3 : exists (c : cmd), forall s, forall n, ceval c s n = outoffuel s.
exists (WHILE btrue DO SKIP END). intros. induction n.
- reflexivity.
- simpl. destruct n.
-- simpl. reflexivity.
-- apply IHn.
Qed. 

Example ex2 : exists c s, | c , empty | -=> s /\ s X = 4.
exists (X ::= 4). exists (update X 4 empty). split.
- apply eval_assign.
- compute. reflexivity.
Qed.

Definition progif : cmd := (SKIP ;; IF X <= Y THEN SKIP ELSE SKIP FI).
Example ex5 : forall s, | progif , s | -=> s.
intro. unfold progif. apply eval_seq with (s' := s).
- apply eval_skip.
- destruct (beval (X <= Y) s) eqn:H.
-- apply eval_if_true.
--- assumption.
--- apply eval_skip.
-- apply eval_if_false.
--- assumption.
--- apply eval_skip.
Qed.
