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

Example swap : exists c, forall s, exists s',
  ceval c s 10 = final s' /\ s' X = s Y /\ s' Y = s X.
exists (Z ::= Y ;; Y ::= X ;; X ::= Z). intro.
exists (update X
     (update Y (update Z (s Y) s X)
        (update Z (s Y) s) Z)
     (update Y (update Z (s Y) s X)
        (update Z (s Y) s))).
split.
- simpl. reflexivity.
- split.
-- compute. reflexivity.
-- reflexivity.
Qed.

Lemma l4 : exists c, forall n,
  exists s s' f, ceval c s f = final s' /\ s' X = n.
exists SKIP. intro. exists (update X n empty), (update X n empty), 1.
split; reflexivity.
Qed.

Lemma l5 : exists c,
  (exists s s', ceval c s 3 = final s') /\
  (exists s s', ceval c s 4 = outoffuel s').
exists (WHILE X <= 5 DO X ::= X + 1 END). split.
- exists (update X 4 empty).
  exists (update X 6 (update X 5 (update X 4 empty))).
  simpl. reflexivity.
- exists (update X 2 empty).
  exists (update X 5 (update X 4 (update X 3 (update X 2 empty)))).
  simpl. reflexivity.
Qed.

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
exists (update X 2 astate).
apply eval_if_true.
- reflexivity.
- apply eval_assign.
Qed.

Theorem determinism : forall c s s',
  | c , s | -=> s' -> (forall s'', | c , s | -=> s'' -> s' = s'').
intros S0 st st' H. induction H; intros.
- inversion H. reflexivity.
- inversion H. reflexivity.
- inversion H1. subst. apply IHeval_bigstep1 in H4; subst.
  apply IHeval_bigstep2 in H7. assumption.
- inversion H1; subst.
-- apply IHeval_bigstep in H8. assumption.
-- rewrite H in H7. discriminate H7.
- inversion H1; subst.
-- rewrite H in H7. discriminate.
-- apply IHeval_bigstep in H8. assumption.
- inversion H2; subst.
-- apply IHeval_bigstep1 in H6. subst. apply IHeval_bigstep2 in H9. assumption.
-- rewrite H in H7. discriminate.
- inversion H0; subst.
-- rewrite H in H3. discriminate.
-- reflexivity.
Qed.
