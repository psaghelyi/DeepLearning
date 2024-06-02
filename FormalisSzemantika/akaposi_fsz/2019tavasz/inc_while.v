(* BEGIN FIX *)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x ≤ y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

(*
a,a1,a2,... ::= n | x | a1 + a2 | a1 - a2 | a1 * a2
b,b1,b2,... ::= true | false | a1 = a2 | a1 <= a2 | ~ b | b1 && b2
c,c1,c2 ::= SKIP | x ::= a | c1 ;; c2 | WHILE b DO c END |
            TEST b THEN c1 ELSE c2
*)
Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity) : imp_scope.

Definition state : Type := string -> nat.
Definition empty : state := fun x => 0.
Definition update (x : string)(n : nat)(s : state)
 : state := fun x' => if eqb x x' then n else s x'.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Reserved Notation "st '=[' c ']⇒' st'"
                  (at level 40).
Inductive cevalr : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]⇒ st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]⇒ (update x n st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]⇒ st' ->
      st' =[ c2 ]⇒ st'' ->
      st =[ c1 ;; c2 ]⇒ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]⇒ st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]⇒ st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]⇒ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]⇒ st' ->
      st' =[ WHILE b DO c END ]⇒ st'' ->
      st =[ WHILE b DO c END ]⇒ st''

  where "st =[ c ]⇒ st'" := (cevalr c st st').

(* From Coq Require Import Logic.FunctionalExtensionality. *)

Axiom functional_extensionality: forall {A B} (f g : A -> B),
  (forall x, f x = g x) -> f = g.

Lemma update_update: forall x n n' st, 
  update x n' (update x n st) = update x n' st.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
    destruct (x =? x0)%string; trivial.
Qed.

Lemma update_get: forall x n st, 
  update x n st x = n.
Proof.
  intros.
  unfold update.
  rewrite eqb_refl.
  trivial.
Qed.

Definition inc_while (X : string) (n : nat) : com :=
  WHILE X ≤ n DO 
    X ::= X + 1 
  END
.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof.
 revert m.
 induction n; destruct m; simpl.
 - now split.
 - split; trivial. intros; apply Peano.le_0_n.
 - now split.
 - rewrite IHn; split.
   + apply Peano.le_n_S.
   + apply Peano.le_S_n.
Qed.

Lemma first_step: forall (X : string) (k n : nat) (st st' : state),
  k <= n ->
  update X (S k) st =[ inc_while X n ]⇒ st' ->
  update X    k  st =[ inc_while X n ]⇒ st'.
Proof.
  intros.
  apply (E_WhileTrue (update X0 k st) (update X0 (S k) st)). 
  + simpl. rewrite update_get. apply leb_le. exact H.
  + rewrite <- (update_update X0 k (S k)).
    apply (E_Ass (update X0 k st)).
    simpl. rewrite update_get. omega.
  + exact H0.
Qed.

Theorem inc_while_post_cond_wrong: forall (X : string) (k n : nat) st,
  k <= n ->
  update X k st =[ inc_while X n ]⇒ update X (n + 1) st.
Proof.
Admitted.

From Coq Require Import Arith.Minus.

Lemma leb_Sn_n: forall n,
  S n <=? n = false.
Proof.
  intros.
  induction n.
  + trivial.
  + trivial.
Qed.

Lemma le_Sn_k_n_k: forall n k,
  S n <= k -> n <= k.
Proof.
  intros.
  inversion H.
  + omega.
  + apply (le_trans n (S n)).
    - omega.
    - rewrite <- H1 in H. exact H.   
Qed.

Theorem inc_while_post_cond: forall (X : string) (k n : nat) st,
  k <= n ->
  update X (n + 1 - k) st =[ inc_while X n ]⇒ update X (n + 1) st.
Proof.
  intros.
  induction k; rewrite plus_comm; simpl.
  + apply E_WhileFalse.
    - simpl. rewrite update_get. apply leb_Sn_n.
  + rewrite plus_comm in IHk.
    unfold plus in IHk.
    rewrite <- minus_Sn_m in IHk.
    2: { apply le_Sn_k_n_k. exact H. }
    - apply first_step.
      * omega.
      * apply IHk. apply le_Sn_k_n_k. exact H.
Qed.

Theorem inc_while_post_cond_advanced: forall (X : string) (k n : nat) st,
  k <= n + 1 ->
  update X (n + 1 - k) st =[ inc_while X n ]⇒ update X (n + 1) st.
Proof.
  intros.
  inversion H.
  + rewrite plus_comm. simpl. rewrite <- minus_n_n. 
    apply (E_WhileTrue _ (update X0 1 st) _ _ _).
    - simpl. rewrite update_get. trivial.
    - rewrite <- (update_update X0 0 1 _).
      apply (E_Ass _ (X0 + 1) _ _).
      simpl. rewrite update_get. trivial.
    - assert (trick_1: 1 = n + 1 - n); try omega.
      assert (trick_2: S n = n + 1); try omega.
      rewrite trick_2.
      replace (update X0 1 st) with (update X0 (n + 1 - n) st).
      2: { rewrite <- trick_1. trivial. }    
      apply (inc_while_post_cond X0 n n st). trivial.
  + rewrite H0. apply inc_while_post_cond. omega.        
Qed.

Definition s : state :=
(* END FIX *)
  update X 11 empty.

(* BEGIN FIX *)
Example cevalr_example3 :
  empty =[
    X ::= 0 ;;
    WHILE X ≤ 10 DO
      X ::= X + 1
    END
  ]⇒ s.
Proof.
  apply (E_Seq _ _ empty (update X 0 empty) _).
  + apply (E_Ass empty _ _ _). trivial.
  (* we have to make one step manually *)
  (* + apply (inc_while_post_cond_advanced X 11 10). trivial. *)
  + apply (E_WhileTrue _ (update X 1 empty) _ _ _).
    - trivial.
    - rewrite <- (update_update X 0 1 _).
      apply (E_Ass _ (X+1) _ _).
      trivial.
    - apply (inc_while_post_cond X 10 10).
      * trivial.
Qed.
(* END FIX *)