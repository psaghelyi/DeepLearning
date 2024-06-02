(*
12 pontot lehet szerezni kiszh-kbol, minden kiszh 1.2 pontos
beadando. 7 pont
0-6 : 1
6.001-8 : 2
8.001-11 : 3
11.001-13 : 4
13.001-16 : 5
*)

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
| cwhile (b : bexp) (c : cmd) (* WHILE b DO c END *)
| csimassign (x1 x2 : string) (a1 a2 : aexp).
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
    | csimassign x1 x2 a1 a2 => final (update x1 (aeval a1 s) (update x2 (aeval a2 s) s))
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
| eval_simassign x1 x2 a1 a2 s :
  | csimassign x1 x2 a1 a2 , s | -=> update x1 (aeval a1 s) (update x2 (aeval a2 s) s)
where "| s , st | -=> st' " := (eval_bigstep s st st').

Theorem determinism : forall S0 st st', |S0, st| -=> st' -> (forall st'', |S0, st| -=> st'' -> st' = st'').
intros S0 st st' H. induction H; intros.
* inversion H. subst. reflexivity.
* inversion H. subst. reflexivity.
* inversion H1. subst. assert (s' = s'0). apply IHeval_bigstep1.
  assumption. subst. apply IHeval_bigstep2. assumption.
* inversion H1; subst.
** apply IHeval_bigstep. assumption.
** rewrite H in H7. inversion H7.
* inversion H1; subst.
** rewrite H in H7. inversion H7.
** apply IHeval_bigstep. assumption.
* inversion H2; subst.
** assert (s' = s'0). apply IHeval_bigstep1. assumption.
   apply IHeval_bigstep2. subst. assumption.
** rewrite H in H7. inversion H7.
* inversion H0; subst.
** rewrite H in H3. inversion H3.
** reflexivity.
* inversion H; subst. reflexivity.
Qed.

(* FELADAT: add meg a parhuzamos ertekadast szintaktikus cukorkakent (naivan)! Csereld le a SKIP-et! *)
Definition simassign_sugar (x1 x2 : string) (a1 a2 : aexp) : cmd := 
  x1 ::= a1 ;; x2 ::= a2.
(*   x2 ::= a2 ;; x1 ::= a1. *)

(*
egeszitsd ki a nyelvet 

| csimassign (x1 x2 : string) (a1 a2 : aexp).

paranccsal!

modositsd ennek megfeleloen ceval-t es -=> -t!
 *)

(* programok ekvivalenciaja: *)
Definition Equiv (c1 c2 : cmd) : Prop := forall st st',
  | c1 , st | -=> st' <-> | c2 , st | -=> st'.

Theorem skip_c (c : cmd) : Equiv c (cseq cskip c).
(* FELADAT *)
split.
- intro. eapply eval_seq. apply eval_skip. assumption.
- intro. inversion H. inversion H2. subst. assumption.
Qed.

Theorem if_swap c1 c2 b : Equiv (IF b THEN c1 ELSE c2 FI) (IF ~ b THEN c2 ELSE c1 FI).
Admitted.

Theorem while_unfold b c : Equiv 
  (WHILE b DO c END) 
  (IF b THEN c ;; WHILE b DO c END ELSE SKIP FI).
(* FELADAT *)
split.
- intro. inversion H; subst.
2:{ apply eval_if_false. assumption. apply eval_skip. }
1:{ apply eval_if_true. assumption. eapply eval_seq. exact H3. assumption. }
-  intro. inversion H; subst.
2:{ inversion H6. subst. apply eval_while_false. assumption. }
1:{ inversion H6; subst. eapply eval_while_true. assumption. exact H2. assumption. }
Qed.
(* szimultan ertekadas nem ekvivalens a szintaktikus cukorkaval *)
Theorem not_sugar :
  ~ forall x1 x2 a1 a2, Equiv (csimassign x1 x2 a1 a2) (simassign_sugar x1 x2 a1 a2).
(* FELADAT *)
intro. Check (H X Y 1 X). assert (Equiv (csimassign X Y 1 X) (simassign_sugar X Y 1 X)). apply H.
destruct (H0 empty (update X (aeval 1 empty) (update Y (aeval X empty) empty))).
assert (| simassign_sugar X Y 1 X, empty | -=> update X (aeval 1 empty) (update Y (aeval X empty) empty)).
apply H1. apply eval_simassign.
assert (| simassign_sugar X Y 1 X, empty | -=> update Y 1 (update X 1 empty)).
eapply eval_seq. apply eval_assign. apply eval_assign.
assert (update X (aeval 1 empty) (update Y (aeval X empty) empty) = update Y 1 (update X 1 empty)) .
apply determinism with (S0 := simassign_sugar X Y 1 X)(st := empty); assumption.
assert (update X (aeval 1 empty) (update Y (aeval X empty) empty) Y = update Y 1 (update X 1 empty) Y).
rewrite H5. reflexivity. cbv in H6. inversion H6. Qed.

Theorem sugar_restricted :
  forall x1 x2 n1 n2, Equiv (csimassign x1 x2 (alit n1) (alit n2))
                            (simassign_sugar x1 x2 (alit n1) (alit n2)).
(* FELADAT *)
Admitted.

(* altalanosithato *)