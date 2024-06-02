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

(* Ird at ceval-t, hogy result-ot adjon vissza! *)
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

Compute ceval SKIP empty 4.
Definition fromResult : result -> state := fun r => match r with
  | final s => s
  | outoffuel s => s
  end.

Compute fromResult (ceval (WHILE true DO X ::= X + 1 END) empty 10) X.

(* Letezik olyan program, ami nem csinal semmit. *)
Lemma l1 : exists (c : cmd), forall n s, ceval c s (S n) = final s.
exists SKIP. intros. simpl. reflexivity. Qed.

(* Letezik vegtelen ciklus. *)
Lemma l2 : exists (c : cmd), forall n s, exists s', ceval c s n = outoffuel s'.
exists (WHILE true DO X ::= X + 1 END).
intro n. induction n; intro s.
- simpl. exists s. reflexivity.
- simpl. destruct (ceval (X ::= X + 1) s n).
-- apply IHn.
-- exists s0. reflexivity.
Qed.
(*
(* Letezik vegtelen ciklus, ami nem csinal semmit. *)
Lemma l3 : exists (c : cmd), forall s, forall n, ceval c s n = outoffuel s.

Lemma l4 : forall n, exists c,
  (exists s, ceval c empty (S n) = final s) /\
  (exists s, ceval c empty (S n) = outoffuel s).

Lemma l5 : exists c, forall n,
  exists s, ceval c empty (S n) = final s /\ s X = n.
*)
(*
opcionalis HF-ok: egeszistd ki a nyelvet FOR ciklussal, listakkal, eljarasokkal, 
fuggvenyekkel, bool/lista tipusu valtozokkal, stb.
*)


(* Big-step operacios szemantika. 
(a denotacios szemantika grafja -- itt nem problema a nemterminalas) *)

(*
  korabbi denotacios szemantika: ceval := fun c s => match c with
   | SKIP                      => s
   | x ::= a                   => update x (aeval a s) s
   | c1 ;; c2                  => let s' = ceval c1 s in let s'' = ceval c2 s' in s''
   | TEST b THEN c1 ELSE c2 FI => if beval b s then (ceval c1 s) else (ceval c2 s)
   | WHILE b DO c END          => if beval b s then ceval (WHILE b DO c END) (ceval c s) else s
*)

(* Add hozza a hianyzo szabalyokat! *)
Reserved Notation "| s , st |=> st'" (at level 50).
Inductive cevalb : cmd -> state -> state -> Prop :=

  | cevalb_skip (s : state) : 

       | SKIP , s |=> s

  | cevalb_assign (x : string)(a : aexp)(s : state) :

       (*------------------------------------*)
       | x ::= a , s |=> update x (aeval a s) s

  | cevalb_seq (c1 c2 : cmd)(s s' s'' : state) :

       | c1 , s |=> s'    ->   | c2 , s' |=> s'' ->
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

       beval b s = false ->
       (*--------------------------------*)
       | WHILE b DO c END , s |=> s

  | cevalb_while_true (b : bexp)(c : cmd)(s s' s'' : state) :

       beval b s = true -> 
       | c , s |=> s' -> 
       | WHILE b DO c END , s' |=> s'' ->
       (*--------------------------------*)
       | WHILE b DO c END , s |=> s''

where "| c , s |=> s'" := (cevalb c s s').

Inductive NAT : Type :=
  | SUCC : NAT -> NAT.
(* ez ures:
Defintion n : NAT := SUCC (SUCC (SUCC ...
*)
Lemma emptyNAT : ~ NAT.
intro n. induction n.
exact IHn.
Qed.

Example ex1 (s : state) : | X ::= 42 , s |=> update X 42 s.
apply cevalb_assign. Qed.

Example ex2 : exists c s, | c , empty |=> s /\ s X = 4.
exists (X ::= 3 ;; X ::= 4). exists (update X 4 (update X 3 empty)).
split.
- apply cevalb_seq with (s' := update X 3 empty).
-- apply cevalb_assign.
-- apply cevalb_assign.
- simpl. unfold update. simpl. reflexivity.
Qed.
(*
Example ex3 : exists (c : cmd), forall (n : nat), exists s,
  | c , update X n empty |=> s /\ s X = (n + 1)%nat.

Example ex4 : exists (c : cmd), forall (n : nat), exists s,
  | c , update X n empty |=> s /\ s Y = (2 * n)%nat.
*)
Definition progif : cmd := (SKIP ;; TEST X <= Y THEN SKIP ELSE SKIP FI).

Example ex5 : | progif , empty |=> empty.
unfold progif.
apply cevalb_seq with (s' := empty).
- apply cevalb_skip.
- destruct (beval (X <= Y) empty) eqn:H.
-- apply cevalb_if_true.
--- exact H.
--- apply cevalb_skip.
-- apply cevalb_if_false.
--- exact H.
--- apply cevalb_skip.
Qed.
(*
Definition prog6 : cmd :=
  X ::= 0 ;;
  WHILE X <= 2 DO
    X ::= X + 1
  END.

Example ex6 : exists s, | prog6 , empty |=> s /\ s X = 3.
*)
Require Import Coq.Program.Equality.
(* Do dependent induction on the big-step derivation! *)
Example ex7 : ~ (exists s, | WHILE true DO SKIP END , empty |=> s).

Lemma determ_bigstep (s s1 s2 : state)(c : cmd) :
  | c , s |=> s1 -> | c , s |=> s2 -> s1 = s2.

Lemma bigstep2denot (s s' : state)(c : cmd) :
  | c , s |=> s' -> exists n, ceval c s n = final s'.

Lemma denot2Bigstep (s s' : state)(c : cmd) :
  exists n, ceval c s n = final s' -> | c , s |=> s'.

