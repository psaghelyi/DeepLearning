(* BEGIN FIX *)
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.

Inductive aexp : Type :=
  | AVar (id : string)
  | ANum (n : nat)
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

Definition state : Type := string -> nat.

Fixpoint aeval (a : aexp) (s : state) : nat :=
  match a with
  | ANum n => n
  | AVar id => s id
  | APlus a1 a2 => (aeval a1 s) + (aeval a2 s)
  | AMinus a1 a2 => (aeval a1 s) - (aeval a2 s)
  | AMult a1 a2 => (aeval a1 s) * (aeval a2 s)
  end.

Fixpoint beval (b : bexp) (s : state) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1 s) =? (aeval a2 s)
  | BLe a1 a2 => (aeval a1 s) <=? (aeval a2 s)
  | BNot b1 => negb (beval b1 s)
  | BAnd b1 b2 => (beval b1 s) && (beval b2 s)
  end.

Inductive stm : Type :=
  | SSkip
  | SAsgn (id : string) (a : aexp)
  | SSeq (S1 S2 : stm)
  | SIf (c : bexp) (St Se : stm).

Definition update (s : state) (id : string) (n : nat) : state :=
  fun id' => if (eqb id id') then n else s id'.

Fixpoint execute (S : stm) (s : state) : state :=
  match S with
  | SSkip => s
  | SAsgn id a => update s id (aeval a s)
  | SSeq S1 S2 => execute S2 (execute S1 s)
  | SIf c St Se => execute (if beval c s then St else Se) s
  end.

(* "pure c = true" <-> c contains no assignments. *)
Fixpoint pure (S : stm) : bool := 
  match S with
  | SSkip => true
  | SAsgn id a => false
  | SSeq S1 S2 => pure S1 && pure S2
  | SIf c St Se => pure St && pure Se
  end.

(* END FIX *)

(* BEGIN FIX *)

Require Import Coq.Bool.Bool.

(*
You should use discriminate once. 

You should use
  apply (andb_true_iff) in ...
twice. You can do
   Check andb_true_iff
to check what this means.
You will also need destruct.
*)
Theorem pure_state :
  forall s S, pure S = true -> execute S s = s.
Proof.
  intros. induction S.
  - simpl. reflexivity.
  - simpl in H. discriminate H.
  - inversion H.  apply (andb_true_iff) in H1. destruct H1.
    simpl. rewrite -> (IHS1 H0). exact (IHS2 H1).
  - inversion H.  apply (andb_true_iff) in H1. destruct H1.
    simpl. destruct (beval c s).
    * exact (IHS1 H0).
    * exact (IHS2 H1).
Qed.

(* END FIX *)