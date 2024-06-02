(* BEGIN FIX *)
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
| cskip
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
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" := (cif b c1 c2) (at level 80, right associativity).
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

Fixpoint beval (b : bexp)(s : state) : bool :=
match b with
 | btrue => true
 | bfalse => false
 | band b1 b2 => (beval b1 s) && (beval b2 s)
 | bnot b => negb (beval b s)
 | beq a1 a2 => aeval a1 s =? aeval a2 s
 | bleq a1 a2 => aeval a1 s <=? aeval a2 s
end.

Inductive result : Type :=
  | final : state -> result
  | outoffuel : state -> result.

Fixpoint ceval (c : cmd)(s : state)(n : nat) : result :=
match n with
| O => outoffuel s
| S n' =>
  match c with
   | SKIP => final s
   | TEST b THEN c1 ELSE c2 FI => if beval b s
                    then (ceval c1 s n')
                    else (ceval c2 s n')
   | x ::= a => final (update x (aeval a s) s)
   | c1 ;; c2 => match ceval c1 s n' with
     | final s' => ceval c2 s' n'
     | r => r
     end
   | WHILE b DO c END => if beval b s
                   then match ceval c s n' with
                   | final s' => ceval (cwhile b c) s' n'
                   | r => r
                   end
                   else final s
  end
end.

Lemma l1 : exists (c : cmd), forall s, exists s', forall n, ceval c s n = outoffuel s'.
(* END FIX *)
exists (WHILE true DO SKIP END). intros. exists s. intros.
induction n.
 * simpl. reflexivity.
 * simpl. destruct n.
   - simpl. reflexivity.
   - simpl. simpl in IHn. exact IHn.
Qed.

(* Tipp: az n lepest tevo program legyen n db SKIP! *)
(* BEGIN FIX *)
Lemma l2 : forall n, exists c,
  (exists s, ceval c empty n = outoffuel s) /\
  (exists s, ceval c empty (1 + n) = final s).
(* END FIX *)
intro n. induction n.
- exists SKIP. split.
-- exists empty. simpl. reflexivity.
-- exists empty. simpl. reflexivity.
- destruct IHn as [c IHn]. destruct IHn. destruct H. destruct H0. exists (c ;; SKIP). split.
-- exists x. simpl. rewrite -> H. reflexivity.
-- exists x0. simpl in H0. simpl. rewrite -> H0. reflexivity.
Qed.

(* BEGIN FIX *)
Reserved Notation "| s , st |=> st'" (at level 50).
Inductive cevalb : cmd -> state -> state -> Prop :=
  | cevalb_skip (s : state) :

       (*-------------*)
       | SKIP , s |=> s

  | cevalb_assign (x : string)(a : aexp)(s : state) :

       (*------------------------------------*)
       | x ::= a , s |=> update x (aeval a s) s

 
  | cevalb_seq (c1 c2 : cmd)(s s' s'' : state) :

       | c1 , s |=> s' -> | c2 , s' |=> s'' ->
       (*---------------------------------*)
       | c1 ;; c2 , s |=> s''

  | cevalb_if_true (b : bexp)(c1 c2 : cmd)(s s' : state) :

       beval b s = true -> | c1 , s |=> s' ->
       (*------------------------------------*)
       | TEST b THEN c1 ELSE c2 FI , s |=> s'

  | cevalb_if_false (b : bexp)(c1 c2 : cmd)(s s' : state) :

       beval b s = false -> | c2 , s |=> s' ->
       (*------------------------------------*)
       | TEST b THEN c1 ELSE c2 FI , s |=> s'

  | cevalb_while_false (b : bexp)(c : cmd)(s : state) :

       beval b s = false ->
       (*------------------------------------*)
       | WHILE b DO c END , s |=> s

  | cevalb_while_true (b : bexp)(c : cmd)(s s' s'' : state) :

       beval b s = true ->
       | c , s |=> s' ->
       | WHILE b DO c END , s' |=> s'' ->
       (*------------------------------------*)
       | WHILE b DO c END , s |=> s''

where "| c , s |=> s'" := (cevalb c s s').

Example l3 : exists (c : cmd), forall (n : nat), exists s,
  | c , update X n empty |=> s /\ s X = (n + 1)%nat.
(* END FIX *)
exists (X ::= X + 1). intro n. exists (update X (n + 1) (update X n empty)).
split. apply cevalb_assign. reflexivity. Qed.

(* BEGIN FIX *)
Example l4 : exists (c : cmd), forall (n : nat), exists s,
  | c , update X n empty |=> s /\ s Y = (2 * n)%nat.
(* END FIX *)
exists (Y ::= 2 * X). intro n. exists (update Y (2 * n) (update X n empty)).
split. apply cevalb_assign. reflexivity. Qed.

(* BEGIN FIX *)
Definition progif : cmd := (SKIP ;; TEST X <= Y THEN SKIP ;; SKIP ELSE X ::= 1 FI).

Example l5 : | progif , empty |=> empty.
(* END FIX *)
apply cevalb_seq with (s' := empty).
- apply cevalb_skip.
- apply cevalb_if_true.
-- reflexivity.
-- apply cevalb_seq with (s' := empty).
--- apply cevalb_skip.
--- apply cevalb_skip.
Qed.

(* BEGIN FIX *)
Definition prog6 : cmd :=
  X ::= 0 ;;
  WHILE X <= 2 DO
    X ::= X + 1
  END.

Example l6 : exists s, | prog6 , empty |=> s /\ s X = 3.
(* END FIX *)
exists (update X 3 (update X 2 (update X 1 (update X 0 empty)))).
split.
-  apply cevalb_seq with (s' := update X 0 empty).
-- apply cevalb_assign.
-- apply cevalb_while_true with (s' :=  update X 1 (update X 0 empty)).
--- simpl. reflexivity.
--- apply cevalb_assign.
--- apply cevalb_while_true with (s' := update X 2 (update X 1 (update X 0 empty))).
---- reflexivity.
---- apply cevalb_assign.
---- apply cevalb_while_true with (s' := update X 3 (update X 2 (update X 1 (update X 0 empty)))).
----- simpl. reflexivity.
----- apply cevalb_assign.
----- apply cevalb_while_false.
------ simpl. reflexivity.
- reflexivity.
Qed.

(* BEGIN FIX *)
Require Import Coq.Program.Equality.
(* Do dependent induction on the big-step derivation! *)
Example ex7 : ~ (exists s, | WHILE true DO SKIP END , s |=> s).
(* END FIX *)
intro. destruct H.
dependent induction H.
inversion H0. apply IHcevalb2. reflexivity. exact H4. Qed.
