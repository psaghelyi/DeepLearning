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
| cifelse (b : bexp)(c : cmd).

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

Definition cifelse1 (b : bexp)(c : cmd) : cmd := SKIP.

Notation "'TEST1' b 'THEN' c 'FI'" := (cifelse1 b c) (at level 80, right associativity).

Lemma ifelsel (b : bexp)(c : cmd)(s s' : state) :
  | TEST b THEN c FI , s |=> s' <-> | TEST1 b THEN c FI , s |=> s'.

Lemma ifelsel1 (b : bexp)(c : cmd)(s s' : state)(n : nat) :
  ceval (TEST b THEN c FI) s n = s' <-> ceval (TEST b THEN c FI) s n = s'.

Definition cfor1 (x : string)(a1 a2 : aexp)(c : cmd) : cmd :=
  x ::= a1 ;;
  WHILE x <= a2 DO
    c ;;
    x ::= x + 1
  END.


Notation "'FOR1' x 'FROM' a1 'TO' a2 'DO' c 'END'" := (cfor1 x a1 a2 c) (at level 80, right associativity).

Definition prog (loop : string -> aexp -> aexp -> cmd -> cmd) : cmd :=
  Y ::= 0 ;;
  loop X 1 10 (
    Y ::= Y + X
  ).

Compute ceval (prog cfor)  empty 10 Y.
Compute ceval (prog cfor1) empty 10 Y.

Compute ceval (prog cfor)  empty 20 Y.
Compute ceval (prog cfor1) empty 20 Y.

Lemma forl (x : string)(a1 a2 : aexp)(c : cmd)(s s' : state) :
  | FOR  x FROM a1 TO a2 DO c END , s |=> s' ->
  | FOR1 x FROM a1 TO a2 DO c END , s |=> s'.

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

