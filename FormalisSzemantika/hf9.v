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
| cif (b : bexp) (c1 c2 : cmd)
| cwhile (b : bexp) (c : cmd)
| cassign (x : string) (a : aexp)
| cseq (c1 c2 : cmd).
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
Fixpoint beval (b : bexp)(s : state) : bool := match b with
  | btrue => true
  | bfalse => false
  | band b1 b2 => beval b1 s && beval b2 s
  | bnot b => negb (beval b s)
  | beq a1 a2 => aeval a1 s =? aeval a2 s
  | bleq a1 a2 => aeval a1 s <=? aeval a2 s
  end.
Inductive result : Type := 
  | final     : state -> result
  | outoffuel : state -> result.
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

(* egy pelda state *)
Definition aState : state := fun x =>
  match x with
  | "X"%string => 1
  | "Y"%string => 2
  | "Z"%string => 42
  | _ => 0
  end.

(* Add meg azt a programot, amely a parameter `n`-tol kezdve osszegzi a szamokat 0-ig lefele! *)
(* END FIX *)
Definition stmt3 (n : nat) : cmd := SKIP.

Goal ceval' (stmt3 5) empty 20 X = final' 0. Proof. simpl. reflexivity. Qed.
Goal ceval' (stmt3 10) empty 200 Y = final' 55. Proof. simpl. reflexivity. Qed.
Goal ceval' (stmt3 1) empty 200 X = final' 0. Proof. simpl. reflexivity. Qed.
Goal ceval' (stmt3 1) empty 200 Y = final' 1. Proof. simpl. reflexivity. Qed.

(* egy program, ami pontosan harom lepest tesz, de nem csinal semmit. *)
Lemma l1 : exists (c : cmd), forall s, ceval c s 3 = final s /\ ceval c s 2 = outoffuel s.
Admitted.

(* X ++ program *)
Example plusplus : exists c , exists f, forall s, ceval' c s f X = final' (s X + 1).
Admitted.

(* X es Y valtozok csereje *)
Example swap : exists c , exists f, forall s, 
  ceval' c s f X = final' (s Y) /\ ceval' c s f Y = final' (s X).
Admitted.

(* nem kell indukcio, csak destruct a fuel-on, es cevl c s (S fuel)-on. *)
Theorem seq_skip : forall c s fuel,
  ceval (c ;; SKIP) s (S fuel) = ceval c s fuel.
Admitted.

(* Letezik vegtelen ciklus, ami nem csinal semmit. *)
(* indukcio n-en *)
Lemma l3 : exists (c : cmd), forall s, forall n, ceval c s n = outoffuel s.
Admitted.

(* az alabbi program soha sem er veget. *)
(* indukcio n-en *)
Lemma l2 : forall n s, exists s', ceval (WHILE 1 == 1 DO X ::= 1 END) s n = outoffuel s'.
Admitted.

(* WHILE kibontasanak ugyanaz a szemantikaja *)
(* nem kell indukcio, csak destruct. *)
Theorem while_unfolding : forall b c s fuel,
  ceval (WHILE b DO c END) s fuel = ceval (IF b THEN c ;; WHILE b DO c END ELSE SKIP FI) s (S fuel).
Admitted.

(* fakultativ *)
Lemma l4 : exists c, forall n,
  exists s s' f, ceval c s f = final s' /\ s' X = n.
Admitted.

(* fakultativ *)
Lemma l5 : exists c,
  (exists s s', ceval c s 3 = final s') /\
  (exists s s', ceval c s 4 = outoffuel s').
Admitted.

(* nehez fakultativ: a fuel novelheto *)
Theorem refuel :
  forall fuel s c result, ceval c s fuel = final result
  ->
  ceval c s (S fuel) = final result.
Admitted.

(* nehez fakultativ: szekvencia asszociativ *)
Theorem seq_assoc :
  forall fuel s c1 c2 c3 result,
    ceval ((c1 ;; c2) ;; c3) s fuel = final result ->
    exists fuel', ceval (c1 ;; (c2 ;; c3)) s fuel' = final result.
Admitted.

