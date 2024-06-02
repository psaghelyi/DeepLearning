(* lenyegileg ugyanaz, mint a gy10pre + hf10 *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(*
Inductive exp : Bool -> Type :=
| alit : nat -> exp true
| ...
Definition aexp := exp true.
Definition bexp := exp false.


induktiv-induktiv tipus, Coq nem tamogatja:

Inductive Typ : Type := 
 | bool : Typ
 | arit : Typ
 | list : Typ -> Typ
 | union : Typ -> Typ -> Typ
 | eq : (A : Typ) -> Exp A -> Exp A -> Typ
with
Exp : Typ -> Type :=
 | true : Exp bool
 | left : forall(a b : Typ), Exp a -> Exp (union a b)
 | right : forall(a b : Typ),Exp b -> Exp (union a b)
 .
*)

Inductive aexp : Type :=
| alit (n : nat)
| avar (x : string)
| aplus (a1 a2 : aexp)
| aminus (a1 a2 : aexp)
| amult (a1 a2 : aexp)
| aif (b : bexp)(a1 a2 : aexp)
with
bexp : Type :=
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
| csimassign (x1 x2 : string) (a1 a2 : aexp)
| dowhile (c : cmd)(b : bexp).
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
| aif b a1 a2 => if beval b s then aeval a1 s else aeval a2 s
end
with
beval (b : bexp)(s : state) : bool :=
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
    | dowhile c b => match ceval c s fuel with
      | outoffuel s => outoffuel s
      | final s => if beval b s
        then ceval (dowhile c b) s fuel 
        else final s
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
  | csimassign x1 x2 a1 a2, s | -=> update x1 (aeval a1 s) (update x2 (aeval a2 s) s)
| eval_dowhile_false b c s s' :
  | c , s | -=> s' -> beval b s' = false
  -> | dowhile c b , s | -=> s'
| eval_dowhile_true b c s s' s'' :
  | c , s | -=> s' -> 
  beval b s' = true ->
  | dowhile c b , s' | -=> s'' ->
  (* ---------------------------- *)
  | dowhile c b , s | -=> s''
where "| s , st | -=> st' " := (eval_bigstep s st st').

Definition progif : cmd := (SKIP ;; IF X <= Y THEN SKIP ELSE SKIP FI).
Example ex5 : forall s, | progif , s | -=> s.
Proof.
intro. apply eval_seq with s.
- apply eval_skip.
- destruct (beval (X <= Y) s) eqn:H.
-- apply eval_if_true.
--- assumption.
--- apply eval_skip.
-- apply eval_if_false.
--- assumption.
--- apply eval_skip.
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
eexists.
eapply eval_if_true.
- simpl. reflexivity.
- eapply eval_assign.
Qed.

Definition ciklus : cmd :=
  X ::= 0 ;;
  Y ::= 0 ;;
  WHILE X <= 2 DO
    Y ::= Y + X ;;
    X ::= X + 1
  END.

Goal exists st,
| ciklus , astate | -=> st.
Proof.
eexists.
eapply eval_seq.
- apply eval_assign.
- eapply eval_seq.
-- apply eval_assign.
-- eapply eval_while_true.
--- reflexivity.
--- eapply eval_seq; apply eval_assign.
--- eapply eval_while_true.
---- reflexivity.
---- eapply eval_seq; apply eval_assign.
---- eapply eval_while_true.
----- reflexivity.
----- eapply eval_seq; apply eval_assign.
----- eapply eval_while_false.
------ reflexivity.
Qed.

Definition s1 : state :=
fun x =>
  match x with
  | "X"%string => 4
  | "Y"%string => 3
  | "Z"%string => 5
  | _ => 0
  end.

Goal exists s,
  | IF X <= Y THEN X ::= Y ELSE Y ::= X FI , s1 | -=> s.
Proof.
eexists.
eapply eval_if_false.
- reflexivity.
- apply eval_assign.
Qed.

Goal exists s,
  | Z ::= X ;; X ::= Y ;; Y ::= Z , s1 | -=> s.
Proof. eexists.
eapply eval_seq.
- apply eval_assign.
- eapply eval_seq.
-- apply eval_assign.
-- apply eval_assign.
Qed.

Goal exists s,
  | IF X <= Y THEN X ::= X + Y ELSE X ::= 0 FI ;; X ::= X + X , s1 | -=> s.
Proof. eexists.
eapply eval_seq.
- eapply eval_if_false.
-- reflexivity.
-- apply eval_assign.
- apply eval_assign.
Qed.

Goal exists c s,
  | c , s1 | -=> s /\ s X = s Y /\ s Y = s Z.
exists (Y ::= X ;; Z ::= X).
eexists.
split.
- eapply eval_seq; apply eval_assign.
- split; reflexivity.
Qed.

Goal exists s,
  exists s', | WHILE 10 <= X DO X ::= X + 1 END , s | -=> s'.
exists empty. exists empty.
apply eval_while_false; reflexivity.
Qed.

Definition s2 : state := update X 10 empty.

Definition ciklus1 : cmd :=
  X ::= 1 ;;
  WHILE X <= 10 DO
    X ::= X + X
  END.

Goal exists s,
  | ciklus1 , empty | -=> s.
eexists. eapply eval_seq. 
- apply eval_assign.
- eapply eval_while_true. reflexivity. apply eval_assign.
eapply eval_while_true. reflexivity. apply eval_assign.
eapply eval_while_true. reflexivity. apply eval_assign.
eapply eval_while_true. reflexivity. apply eval_assign.
eapply eval_while_false. reflexivity.
Qed.

Theorem determinism : forall S0 st st', |S0, st| -=> st' -> (forall st'', |S0, st| -=> st'' -> st' = st'').
intros S0 st st' H. induction H; intros; subst.
- inversion H. reflexivity.
- inversion H. reflexivity.
- inversion H1. subst. assert (s' = s'0).
-- apply IHeval_bigstep1. assumption.
-- subst. apply IHeval_bigstep2. assumption.
- inversion H1; subst.
-- apply IHeval_bigstep. assumption.
-- rewrite H in H7. inversion H7.
- inversion H1; subst.
-- rewrite H in H7. inversion H7.
-- apply IHeval_bigstep. assumption.
- inversion H2; subst.
-- assert (s' = s'0).
--- apply IHeval_bigstep1.
---- assumption.
--- subst. apply IHeval_bigstep2.
---- assumption.
-- rewrite H in H7. inversion H7.
- inversion H0; subst.
-- rewrite H in H3. inversion H3.
-- reflexivity.
- inversion H; reflexivity.
- inversion H1; subst.
-- apply IHeval_bigstep. assumption.
-- assert (s' = s'0).
--- apply IHeval_bigstep. assumption.
--- rewrite <- H2 in H5. rewrite H0 in H5. discriminate H5.
- inversion H2; subst.
-- assert (s' = st'').
--- apply IHeval_bigstep1. assumption.
--- rewrite H3 in H0. rewrite H0 in H8. discriminate H8.
-- assert (s' = s'0).
--- apply IHeval_bigstep1. assumption.
--- rewrite H3 in *; subst.
    apply IHeval_bigstep2. assumption.
Qed.

(*
a : A                      a : A
b : A        --subst-->    x : P a
e : a = b
x : P b
*)


(*
egeszitsd ki a nyelvet 

| csimassign (x1 x2 : string) (a1 a2 : aexp).

paranccsal!

modositsd ennek megfeleloen ceval-t es -=> -t!
 *)

(* FELADAT: add meg a parhuzamos ertekadast szintaktikus cukorkakent (naivan)! Csereld le a SKIP-et! *)
Definition simassign_sugar (x1 x2 : string) (a1 a2 : aexp) : cmd := 
  x1 ::= a1 ;; x2 ::= a2.

(* programok ekvivalenciaja: *)
Definition Equiv (c1 c2 : cmd) : Prop := forall st st',
  | c1 , st | -=> st' <-> | c2 , st | -=> st'.

Theorem skip_c (c : cmd) : Equiv c (cseq cskip c).
Proof. split; intro.
- apply eval_seq with st.
-- apply eval_skip.
-- assumption.
- inversion H; subst.
-- inversion H2; subst.
--- assumption.
Qed.

Theorem while_unfold b c : Equiv 
  (WHILE b DO c END) 
  (IF b THEN c ;; WHILE b DO c END ELSE SKIP FI).
Proof. split; intro.
- inversion H; subst.
-- apply eval_if_true.
--- assumption.
--- apply eval_seq with s'.
---- assumption.
---- assumption.
-- apply eval_if_false.
--- assumption.
--- apply eval_skip.
- inversion H; subst.
-- inversion H6; subst.
--- apply eval_while_true with s'; assumption.
-- inversion H6; subst. apply eval_while_false. assumption.
Qed.

(* szimultan ertekadas nem ekvivalens a szintaktikus cukorkaval *)
Theorem not_sugar :
  ~ forall x1 x2 a1 a2, Equiv (csimassign x1 x2 a1 a2) (simassign_sugar x1 x2 a1 a2).
intro.
(*  x1 := X, x2 := Y, a1 := 2, a2 := X
empty --> sugar:  X:=2,Y:=2
          rendes: X:=2,Y:=0
 *)
assert (Equiv (csimassign X Y 2 X)
      (simassign_sugar X Y 2 X)).
- apply H.
- assert (| csimassign X Y 2 X , empty | -=> update Y 2 (update X 2 empty) <-> | simassign_sugar X Y 2 X , empty | -=> update Y 2 (update X 2 empty)).
-- apply H0.
-- destruct H1.
assert (| csimassign X Y 2 X, empty | -=> update Y 2 (update X 2 empty)).
--- apply H2.
---- eapply eval_seq; apply eval_assign.
--- assert (| csimassign X Y 2 X, empty | -=> update X 2 (update Y 0 empty)).
---- apply eval_simassign.
---- assert (update Y 2 (update X 2 empty) = update X 2 (update Y 0 empty)).
----- apply determinism with (csimassign X Y 2 X)(empty); assumption.
----- assert (update Y 2 (update X 2 empty) Y = update X 2 (update Y 0 empty) Y).
------ rewrite H5. reflexivity.
------ cbv in H6. inversion H6.
Qed.

Theorem sugar_restricted :
  forall x1 x2 n1 n2, Equiv (csimassign x1 x2 (alit n1) (alit n2))
                            (simassign_sugar x1 x2 (alit n1) (alit n2)).
(* FELADAT *)
Admitted.

(*
Lemma dowhile_sugar1 : 
 forall c0 st st', | c0 , st | -=> st' 
   -> forall c b, c0 = dowhile c b ->
      | c ;; WHILE b DO c END , st | -=> st'.
Proof. intros c0 st st' H.
induction H; intros.
- discriminate H.
- discriminate H.
- discriminate H1.
- discriminate H1.
- discriminate H1.
- discriminate H2.
- discriminate H0.
- discriminate H.
- inversion H1; subst.
-- apply eval_seq with s'.
--- assumption.
--- apply eval_while_false.
---- assumption.
- inversion H2; subst.
  apply eval_seq with s'.
-- assumption.
-- 
  

Theorem dowhile_sugar : 
  forall c b, Equiv 
    (dowhile c b) 
    (c ;; WHILE b DO c END).
intros c b.
split; intro.
- (*  
  H : 
*)



inversion H; subst.
  apply eval_seq with st'.
-- assumption.
-- apply eval_while_false.
--- assumption.
-- apply eval_seq with s'.
--- assumption.
--- apply eval_while_true with .
*)

(*
fuel-os denot szemantika ekvivalencia fogalmai:
1. minden fuel-ra vagy mindket program outoffuel s, 
   vagy mindket program final s ugyanarra az s-re
2. minden fuel-ra vagy outoffuel vagy ugyanazt a final-t adja
3. vagy minden fuel-ra outoffuel vagy letezik olyan 
   fuel amire mindketto ugyanazt a final-t adja
*)



