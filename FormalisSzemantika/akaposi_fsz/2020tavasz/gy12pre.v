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

Fixpoint ceval (c : cmd)(s : state)(n : nat) : state := match n with
  | O => s
  | S n' => match c with
    | cskip       => s
    | cif b c1 c2 => if beval b s then ceval c1 s n' else ceval c2 s n'
    | cwhile b c  => if beval b s then ceval (cwhile b c) (ceval c s n') n' else s
    | cassign x a => update x (aeval a s) s
    | cseq c1 c2  => ceval c2 (ceval c1 s n') n'
    end
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

where "| c , s |=> s'" := (cevalb c s s').

Lemma determ_bigstep (s s1 : state)(c : cmd) :
  | c , s |=> s1 -> forall (s2 : state), | c , s |=> s2 -> s1 = s2.
intro. induction H; intros.
- inversion H. reflexivity.
- inversion H. reflexivity.
- inversion H1. rewrite <- (IHcevalb1 _ H4) in H7. apply IHcevalb2. exact H7.
- inversion H1.
-- apply IHcevalb. exact H8.
-- rewrite -> H in H7. discriminate H7.
- inversion H1.
-- rewrite -> H in H7. discriminate H7.
-- apply IHcevalb. exact H8.
- inversion H0.
-- reflexivity.
-- rewrite -> H in H3. discriminate H3.
- inversion H2.
-- rewrite <- H6 in H7. rewrite -> H in H7. discriminate H7.
-- rewrite <- (IHcevalb1 _ H6) in H9. apply IHcevalb2. exact H9.
Qed.

Inductive E : Type :=
  | step : E -> E.

Lemma noE : ~ E.
intro. induction H. exact IHE.
Qed.

Require Import Coq.Program.Equality.

Definition inf := WHILE true DO SKIP END.

Lemma noInf (s : state) : ~ exists s', | inf , s |=> s'.

Definition Equiv0 (c1 c2 : cmd) : Prop := forall s,
  exists s1 s2, | c1 , s |=> s1 /\ | c2 , s |=> s2 /\ forall x, s1 x = s2 x.

Lemma eq3 : ~ forall c, Equiv0 (SKIP ;; c) c.

Definition Equiv1 (c1 c2 : cmd) : Prop := forall s,
  ((exists s1, | c1 , s |=> s1) <-> (exists s2, | c2 , s |=> s2)) /\ 
  (forall s1 s2, | c1 , s |=> s1 /\ | c2 , s |=> s2 -> forall x, s1 x = s2 x).

Lemma eq4 (c : cmd) : Equiv1 (SKIP ;; c) c.

Lemma eq5 : Equiv1 SKIP (WHILE false DO X ::= Y END).

Lemma eq6 (a : aexp) : ~ Equiv1 (X ::= a) (X ::= 0 ;; X ::= a).

Lemma eq7 : Equiv1 inf (WHILE true DO X ::= X + 1 END).






(* determ, ekvivalencia

uj nyelvi elemek:

 * for ciklus mint szintaktikus cukorka ill. mint uj nyelvi elem

   - elobbi verzioban tobb lepesre van szukseg egy konkret for ciklus
     vegrehajtasahoz

   - elobbihez derivable rule az opszemhez

 * ifelse

while b c <-> if b then (c ;; while b c) else skip

(X ::= n ;; Y ::= m) <-> (Y ::= m ;; X ::= n)

SKIP ;; c <-> c ;; SKIP

szemantikus ekvivalencia: mutatni egy bonyolult programot, es kerni,
hogy egy vele szemantikusan ekvivalens rovidebb programot irjanak
(rovidseg: program magassaga valamekkora lehet csak)

*)