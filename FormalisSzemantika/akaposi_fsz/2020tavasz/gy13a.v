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
| cseq (c1 c2 : cmd)
| cfor (x : string)(a1 a2 : aexp)(c : cmd)
| cif1 (b : bexp)(c : cmd).

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
Notation "'FOR' x 'FROM' a1 'TO' a2 'DO' c 'END'" := (cfor x a1 a2 c) (at level 80, right associativity).
Notation "'TEST' b 'THEN' c 'FI'" := (cif1 b c) (at level 80, right associativity).

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

Fixpoint ceval (c : cmd)(s : state)(n : nat) : state := match n with
  | O => s
  | S n' => match c with
    | cskip       => s
    | cif b c1 c2 => if beval b s then ceval c1 s n' else ceval c2 s n'
    | cwhile b c  => if beval b s then ceval (cwhile b c) (ceval c s n') n' else s
    | cassign x a => update x (aeval a s) s
    | cseq c1 c2  => ceval c2 (ceval c1 s n') n'
    | FOR x FROM a1 TO a2 DO c END => let 
        s' := update x (aeval a1 s) s in
        ceval_for x a2 c s' n'
    | TEST b THEN c FI => if beval b s then ceval c s n' else s
    end
  end
with ceval_for (x : string)(a2 : aexp)(c : cmd)(s : state)(n : nat) : state := 
  match n with
  | O => s
  | S n' => if beval (x <= a2) s
            then
              let s'  := ceval c s n' in
              let s'' := update x (s' x + 1) s' in
              ceval_for x a2 c s'' n'
            else
              s
  end.

Definition prog1 :=
  X ::= 0 ;;
  Z ::= 1 ;;
  FOR Y FROM 0 TO 20 DO
    TEST Z == 1 THEN
      X ::= X + Y ;;
      Z ::= 0
    FI ;;
    TEST Z == 0 THEN
      Z ::= 1
    FI
  END.

Compute ceval prog1 empty 60 X.

Reserved Notation "| s , st |=> st'" (at level 50).
Inductive cevalb : cmd -> state -> state -> Prop :=

  | cevalb_skip (s : state) :

       (*------------*)
       | SKIP , s |=> s

  | cevalb_assign (x : string)(a : aexp)(s : state) :

       (*------------------------------------*)
       | x ::= a , s |=> update x (aeval a s) s

  | cevalb_seq (c1 c2 : cmd)(s s' s'' : state) : 

       | c1 , s |=> s'  ->  | c2 , s' |=> s''  ->
       (*------------------------------------*)
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

           beval b s = false       ->
       (*------------------------*)
       | WHILE b DO c END , s |=> s

  | cevalb_while_true (b : bexp)(c : cmd)(s s' s'' : state) :

       beval b s = true                  ->
       | c , s |=> s'                    ->
       | WHILE b DO c END , s' |=> s''   ->
       (*---------------------------*)
       | WHILE b DO c END , s |=> s''

  | cevalb_for (x : string)(a1 a2 : aexp)(c : cmd)(s s' : state) :

       foreval x a2 c (update x (aeval a1 s) s) s' ->
       (*-------------------------------------------*)
       | FOR x FROM a1 TO a2 DO c END , s |=> s'

  | cevalb_if1_true (b : bexp)(c : cmd)(s s' : state) :

       beval b s = true -> | c , s |=> s' ->
       (*------------------------------------*)
       | TEST b THEN c FI , s |=> s'

  | cevalb_if1_false (b : bexp)(c : cmd)(s : state) :

       beval b s = false ->
       (*------------------------------------*)
       | TEST b THEN c FI , s |=> s


where "| c , s |=> s'" := (cevalb c s s')
with foreval : string -> aexp -> cmd -> state -> state -> Prop :=
  | foreval_false (x : string)(a2 : aexp)(c : cmd)(s : state) :

       beval (x <= a2) s = false   ->
       (*-----------------------*)
       foreval x a2 c s s

  | foreval_true (x : string)(a2 : aexp)(c : cmd)(s s' s'' : state) :

       beval (x <= a2) s = true   ->
       | c , s |=> s'             ->
       foreval x a2 c (update x (aeval x s' + 1) s') s''  ->
       (*-----------------------*)
       foreval x a2 c s s''.

Definition Equiv1 (c1 c2 : cmd) : Prop := forall s,
  ((exists s1, | c1 , s |=> s1) <-> (exists s2, | c2 , s |=> s2)) /\ 
  (forall s1 s2, | c1 , s |=> s1 /\ | c2 , s |=> s2 -> forall x, s1 x = s2 x).

Lemma eq6 : ~ (forall a, ~ Equiv1 (X ::= a) (X ::= 0 ;; X ::= a)).
intro.
apply (H 0).
intro.
split.
- split.
-- exists (update X 0 (update X 0 s)). 
   apply cevalb_seq with (s' := update X 0 s); apply cevalb_assign.
-- exists (update X 0 s). apply cevalb_assign.
- intros. destruct H0. inversion H0. simpl.
  inversion H1. inversion H8. rewrite <- H15 in H11. inversion H11.
  simpl. unfold update. destruct (string_dec X x); reflexivity.
Qed.

Definition prog := FOR X FROM 3 TO 4 DO Y ::= Y + X END.
Definition s1 := update Y 1 empty.

Compute ceval prog s1 10.

Lemma l1 : exists s2, ceval prog s1 10 = s2.
exists (update X 5 (update Y 8 (update X 4 (update Y 4 (update X 3 (update Y 1 empty)))))).
reflexivity.
Qed.

Lemma l2 : exists s2, | prog , s1 |=> s2.
exists (update X 5 (update Y 8 (update X 4 (update Y 4 (update X 3 (update Y 1 empty)))))).
unfold prog. apply cevalb_for.
(*  |FOR X TO 4 DO Y ::= Y + X END , update X (aeval 3 s1) s1) |=> s2 *)
apply foreval_true with (s' := update Y 4 (update X 3 (update Y 1 empty))).
- simpl. reflexivity.
- apply cevalb_assign.
- simpl. apply foreval_true with (s' := update Y 8 (update X 4 (update Y 4 (update X 3 (update Y 1 empty))))).
-- simpl. reflexivity.
-- apply cevalb_assign.
-- simpl. apply foreval_false.
--- simpl. reflexivity.
Qed.

Example ex1 : | TEST X == 0 THEN X ::= 1 FI , empty |=> update X 1 empty.
apply cevalb_if1_true.
- simpl. reflexivity.
- apply cevalb_assign.
Qed.

Definition cif1sugar (b : bexp)(c : cmd) : cmd := TEST b THEN c ELSE SKIP FI.

Notation "'TESTsugar' b 'THEN' c 'FI'" := (cif1sugar b c) (at level 80, right associativity).

Lemma ifelsel (b : bexp)(c : cmd)(s s' : state) :
  | TEST b THEN c FI , s |=> s' <-> | TESTsugar b THEN c FI , s |=> s'.
split; intro.
- inversion H.
-- unfold cif1sugar. apply cevalb_if_true.
--- exact H2.
--- exact H5.
-- unfold cif1sugar. apply cevalb_if_false.
--- exact H4.
--- apply cevalb_skip.
- unfold cif1sugar in H. inversion H.
-- apply cevalb_if1_true.
--- exact H5.
--- exact H6.
-- inversion H6. apply cevalb_if1_false.
--- rewrite <- H9. exact H5.
Qed.

Lemma ifelsel1 (b : bexp)(c : cmd)(s s' : state)(n : nat) :
  ceval (TEST b THEN c FI) s n = s' <-> ceval (TESTsugar b THEN c FI) s n = s'.
split; intro. induction n; simpl in H; simpl. 
- exact H.
- destruct (beval b s).
-- exact H.
-- rewrite -> H. destruct n; reflexivity.
- induction n; simpl in H; simpl.
-- exact H.
-- destruct (beval b s).
--- exact H.
--- destruct n; simpl in H; exact H.
Qed.

Definition cforSugar (x : string)(a1 a2 : aexp)(c : cmd) : cmd :=
  x ::= a1 ;;
  WHILE x <= a2 DO
    c ;;
    x ::= x + 1
  END.

Notation "'FORsugar' x 'FROM' a1 'TO' a2 'DO' c 'END'" := (cforSugar x a1 a2 c) (at level 80, right associativity).

Definition prog2 (loop : string -> aexp -> aexp -> cmd -> cmd) : cmd :=
  Y ::= 0 ;;
  loop X 1 10 (
    Y ::= Y + X
  ).

Compute ceval (prog2 cfor)  empty 20 Y.
Compute ceval (prog2 cforSugar) empty 20 Y.

Compute ceval (prog2 cfor)  empty 10 Y.
Compute ceval (prog2 cforSugar) empty 10 Y.

Lemma forl (x : string)(a1 a2 : aexp)(c : cmd)(s s' : state) :
  | FOR      x FROM a1 TO a2 DO c END , s |=> s' ->
  | FORsugar x FROM a1 TO a2 DO c END , s |=> s'.

(* Erdekes HF: *)
Lemma forl1 (x : string)(a1 a2 : aexp)(c : cmd)(s s' : state) :
  | FOR1 x FROM a1 TO a2 DO c END , s |=> s' ->
  | FOR  x FROM a1 TO a2 DO c END , s |=> s'.
Admitted.

(* Az alabbi nem bizonyithato, csak akkor, ha final state-re vonatkozik: *)
Lemma forl2 (x : string)(a1 a2 : aexp)(c : cmd)(s s' : state) :
  (exists n, ceval (FOR1 x FROM a1 TO a2 DO c END) s n = s') <->
  (exists n, ceval (FOR  x FROM a1 TO a2 DO c END) s n = s').
Admitted.

