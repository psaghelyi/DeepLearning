(*
12 pontot lehet szerezni kiszh-kbol, minden kiszh 1.2 pontos
beadando. 7 pont
0-6 : 1
7-8 : 2
9-11 : 3
12-13 : 4
14-16 : 5
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
(*
     ----------------------eval_skip
      | SKIP , st | -=> st

      --------------------------------------------eval_assign
       | x ::= a , s | -=> update x (aeval a s) s

      
       | c1 , s | -=> s'            | c2 , s' | -=> s''
      --------------------------------------------------eval_seq
       | c1 ;; c2 , s | -=> s''

               beval b s = false
      ----------------------------------eval_while_false
       | WHILE b DO c END , s | -=> s

       beval b s = true
       | c , s | -=> s'
       | WHILE b DO c END , s' | -=> s''
      ----------------------------------eval_while_true
       | WHILE b DO c END , s | -=> s''
*)
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

Example ex2 : exists c s, | c , empty | -=> s /\ s X = 4.
exists (X ::= X + 4). exists (update X 4 empty).
split.
2:{ cbv. reflexivity. }
1:{ apply eval_assign. }
Qed.

Definition progif : cmd := (SKIP ;; IF X <= Y THEN SKIP ELSE SKIP FI).
Example ex5 : forall s, | progif , s | -=> s.
intro. apply eval_seq with (s' := s).
- apply eval_skip.
- destruct (beval (X <= Y) s) eqn:H.
-- apply eval_if_true.
--- assumption.
--- apply eval_skip.
-- apply eval_if_false.
--- assumption.
--- apply eval_skip.
Qed.
(*
                               beval (X<=Y) s = true   | SKIP , s | -=> s
-------------------eval_skip   ----------------------------------------------eval_if_true
| SKIP , s | -=> s             | IF X <= Y THEN SKIP ELSE SKIP FI , s | -=> s
-----------------------------------------------------------------------------eval_seq
  | cmd , s | -=> s

*)

Definition astate : state := 
fun x =>
  match x with
  | "X"%string => 1
  | "Y"%string => 2
  | "Z"%string => 42
  | _ => 0
  end.

Goal exists st,
  | IF X <= Y THEN X ::= Y ELSE Y ::= X FI , astate | -=> st.
Admitted.

Definition ciklus : cmd :=
  X ::= 0 ;;
  Y ::= 0 ;;
  WHILE X <= 2 DO
    Y ::= Y + X ;;
    X ::= X + 1
  END.

Definition finalState : state := 
  update X 3 (update Y 3 (update X 2 (update Y 1 (update X 1 (update Y 0 (update Y 0 (update X 0 astate))))))).

Goal exists st,
| ciklus , astate | -=> st.
exists finalState.
apply eval_seq with (s' := update X 0 astate). (*eapply eval_seq.*)
- apply eval_assign.
- eapply eval_seq.
-- apply eval_assign.
-- simpl. eapply eval_while_true.
--- simpl. reflexivity.
--- eapply eval_seq.
---- apply eval_assign.
---- apply eval_assign.
--- simpl. eapply eval_while_true.
---- simpl. reflexivity.
---- eapply eval_seq.
----- apply eval_assign.
----- simpl. apply eval_assign.
---- simpl. eapply eval_while_true.
----- simpl. reflexivity.
----- simpl. eapply eval_seq.
------ apply eval_assign.
------ apply eval_assign.
----- simpl. apply eval_while_false.
------ simpl. reflexivity.
Qed.

Goal exists st,
| ciklus , astate | -=> st.
eexists.
eapply eval_seq.
- apply eval_assign.
- eapply eval_seq.
-- apply eval_assign.
-- simpl. eapply eval_while_true.
--- simpl. reflexivity.
--- eapply eval_seq.
---- apply eval_assign.
---- apply eval_assign.
--- simpl. eapply eval_while_true.
---- simpl. reflexivity.
---- eapply eval_seq.
----- apply eval_assign.
----- simpl. apply eval_assign.
---- simpl. eapply eval_while_true.
----- simpl. reflexivity.
----- simpl. eapply eval_seq.
------ apply eval_assign.
------ apply eval_assign.
----- simpl. apply eval_while_false.
------ simpl. reflexivity.
Qed.

Inductive FuraNat : Type := 
  | S : FuraNat -> FuraNat.

Theorem nincsFuraNat : forall (n : FuraNat), False.
intro. induction n. assumption. Qed.

Goal forall s s' c, (c = WHILE true DO SKIP END) /\ | c , s | -=> s' -> False.
intros. destruct H. induction H0; inversion H.
2 :{ rewrite H2 in H0. simpl in H0. inversion H0. }
1 :{ rewrite H2 in IHeval_bigstep2. 
     rewrite H3 in IHeval_bigstep2. apply IHeval_bigstep2.
     reflexivity. }
Qed.

Theorem determinism : forall S0 st st', |S0, st| -=> st' -> (forall st'', |S0, st| -=> st'' -> st' = st'').
intros S0 st st' H. induction H; intros.
Admitted.

(*
egeszitsd ki a nyelvet 

| csimassign (x1 x2 : string) (a1 a2 : aexp).

paranccsal!

modositsd ennek megfeleloen ceval-t es -=> -t!
 *)

(* FELADAT: add meg a parhuzamos ertekadast szintaktikus cukorkakent (naivan)! Csereld le a SKIP-et! *)
Definition simassign_sugar (x1 x2 : string) (a1 a2 : aexp) : cmd := SKIP.

(* programok ekvivalenciaja: *)
Definition Equiv (c1 c2 : cmd) : Prop := forall st st',
  | c1 , st | -=> st' <-> | c2 , st | -=> st'.

Theorem skip_c (c : cmd) : Equiv c (cseq cskip c).
(* FELADAT *)
Admitted.

Theorem while_unfold b c : Equiv 
  (WHILE b DO c END) 
  (IF b THEN c ;; WHILE b DO c END ELSE SKIP FI).
(* FELADAT *)
Admitted.

(* simultan ertekadas nem ekvivalens a szintaktikus cukorkaval *)
Theorem not_sugar :
  ~ forall x1 x2 a1 a2, Equiv (csimassign x1 x2 a1 a2) (simassign_sugar x1 x2 a1 a2).
(* FELADAT *)
Admitted.

Theorem sugar_restricted :
  forall x1 x2 n1 n2, Equiv (csimassign x1 x2 (alit n1) (alit n2))
                            (simassign_sugar x1 x2 (alit n1) (alit n2)).
(* FELADAT *)
Admitted.
