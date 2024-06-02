(* BEGIN FIX *)
(** Pótold a hiányzó kódrészleteket! A BEGIN FIX és END FIX közötti részeket ne módosítsd! Akkor jó a megoldásod, ha a Coq elfogadja az egészet (zöld lesz a teljes fájl).*)
(** Fill out the missing parts! Do not modify the code between BEGIN FIX and END FIX! *)

(* Egeszitsd ki az AExp-et egy AMul (szorzas) konstruktorral! *)
Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
(* END FIX *)

(* ide ird a kiegeszitest! *)

(* BEGIN FIX *)
.

Definition getLeft : AExp -> AExp := fun a => match a with
  | ALit n => ALit n
  | APlus a1 a2 => a1
  | ASub  a1 a2 => a1
  | AMul  a1 a2 => a1
  end.
Definition getRight : AExp -> AExp := fun a => match a with
  | ALit n => ALit n
  | APlus a1 a2 => a2
  | ASub  a1 a2 => a2
  | AMul  a1 a2 => a2
  end.
Definition isPlus : AExp -> bool := fun a => match a with
  | APlus _ _ => true
  | _ => false
  end.
Definition isSub : AExp -> bool := fun a => match a with
  | ASub _ _ => true
  | _ => false
  end.
Definition isMul : AExp -> bool := fun a => match a with
  | AMul _ _ => true
  | _ => false
  end.

(*
exp1 :=
    +
   /  \
  *    -
 / \  / \
 1 2  +  3
     / \
    4   5
*)

Definition exp1 : AExp :=
(* END FIX *)



(* BEGIN FIX *)
Lemma exp1_test1 : getLeft (getLeft exp1) = ALit 1. Proof. reflexivity. Qed.
Lemma exp1_test2 : getRight (getLeft exp1) = ALit 2. Proof. reflexivity. Qed.
Lemma exp1_test3 : getRight (getRight exp1) = ALit 3. Proof. reflexivity. Qed.
Lemma exp1_test4 : getLeft (getLeft (getRight exp1)) = ALit 4. Proof. reflexivity. Qed.
Lemma exp1_test5 : getRight (getLeft (getRight exp1)) = ALit 5. Proof. reflexivity. Qed.
Lemma exp1_test6 : isPlus exp1 = true. Proof. reflexivity. Qed.
Lemma exp1_test7 : isMul (getLeft exp1) = true. Proof. reflexivity. Qed.
Lemma exp1_test8 : isSub (getRight exp1) = true. Proof. reflexivity. Qed.
Lemma exp1_test9 : isPlus (getLeft (getRight exp1)) = true. Proof. reflexivity. Qed.

(*
exp2 :=
     -
    / \
   1   +
      / \
     2   +
        / \
       3   +
          / \
         4   5
*)

Definition exp2 : AExp :=
(* END FIX *)


(* BEGIN FIX *)
Lemma exp2_test1 : getLeft exp2 = ALit 1. Proof. reflexivity. Qed.
Lemma exp2_test2 : getLeft (getRight exp2) = ALit 2. Proof. reflexivity. Qed.
Lemma exp2_test3 : getLeft (getRight (getRight (getRight exp2))) = ALit 4. Proof. reflexivity. Qed.
Lemma exp2_test4 : getRight (getRight (getRight (getRight exp2))) = ALit 5. Proof. reflexivity. Qed.
Lemma exp2_test5 : isSub exp2 = true. Proof. reflexivity. Qed.
Lemma exp2_test6 : isPlus (getRight exp2) = true. Proof. reflexivity. Qed.
Lemma exp2_test7 : isPlus (getRight (getRight exp2)) = true. Proof. reflexivity. Qed.
Lemma exp2_test8 : isPlus (getRight (getRight (getRight exp2))) = true. Proof. reflexivity. Qed.


(* egeszitsd ki az AMul kiertekelesevel! *)
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
(* END FIX *)

(* BEGIN FIX *)
end.

Example aeval_test1 : forall n : nat, aeval (ALit n) = n.
(* END FIX *)


(* BEGIN FIX *)
Example aeval_test2 : forall n m : nat, aeval (APlus (ALit n) (ALit m)) = n + m.
(* END FIX *)


(* Ugy add meg exNum-ot, hogy mulTest bizonyithato legyen! *)
(* BEGIN FIX *)
Definition exNum
  :=
(* END FIX *)


(* BEGIN FIX *)
Example mulTest : aeval (AMul (ALit exNum) (ALit 10)) = 30.
(* END FIX *)


(* BEGIN FIX *)
Fixpoint leaves_count (a : AExp) : nat :=
match a with
| ALit n => 1
| APlus a1 a2 => leaves_count a1 + leaves_count a2
| ASub  a1 a2 => leaves_count a1 + leaves_count a2
| AMul  a1 a2 => leaves_count a1 + leaves_count a2
end.

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
(* END FIX *)
(* hasznald Nat.add_comm -ot! *)
Proof. Check Nat.add_comm.

(* BEGIN FIX *)
Fixpoint vanbenneSub (a : AExp) : bool :=
(* END FIX *)



(* BEGIN FIX *)
Lemma lsub1 (a1 a2 : AExp) : vanbenneSub (ASub a1 a2) = true.
(* END FIX *)
(* Nincs szukseg indukciora. *)


(* BEGIN FIX *)
Lemma lsub2 (a1 a2 : AExp) : vanbenneSub a1 = true -> vanbenneSub (APlus a1 a2) = true.
(* END FIX *)
(* Nincs szukseg indukciora. *)


(* BEGIN FIX *)
From Coq Require Import Bool.Bool.

Lemma lsub3 (a1 a2 : AExp) : vanbenneSub a2 = true -> vanbenneSub (APlus a1 a2) = true.
(* END FIX *)
(* Hasznald az orb_true_r lemmat! Nincs szukseg indukciora. *)
Proof. Check orb_true_r.


(* BEGIN FIX *)
Lemma inverse : forall (n : nat), n - n = 0.
(* END FIX *)
(* Hasznalj indukciot n-en! *)


(* Fakultativ. *)
Lemma nullaz : forall (a : AExp), exists (a' : AExp), aeval (ASub a a') = 0.
(* Hasznald inverse-t! Az "exists ..." bizonyitasahoz az exists taktika kell. *)


(* Fakultativ, kicsit nehezebb feladat. "A /\ B" bizonyitasahoz a split taktikat hasznald! *)
Lemma nullaz' : forall (a : AExp), exists (a' : AExp), aeval (ASub a a') = 0 /\ a' <> a.


(* Fakultativ. *)
Lemma lsub4 (a1 a2 : AExp) : vanbenneSub (APlus a1 a2) = false -> vanbenneSub a1 = false /\ vanbenneSub a2 = false.
