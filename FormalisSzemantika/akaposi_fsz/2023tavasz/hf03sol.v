(* BEGIN FIX *)
(** Pótold a hiányzó kódrészleteket! A BEGIN FIX és END FIX közötti részeket ne módosítsd! Akkor jó a megoldásod, ha a Coq elfogadja az egészet (zöld lesz a teljes fájl).*)
(** Fill out the missing parts! Do not modify the code between BEGIN FIX and END FIX! *)

(* Egeszitsd ki az AExp-et egy AMul (szorzas) konstruktorral! *)
Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
(* END FIX *)
| AMul (a1 a2 : AExp)
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
  APlus
    (AMul
      (ALit 1)
      (ALit 2))
    (ASub
      (APlus
        (ALit 4)
        (ALit 5))
      (ALit 3)).

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
  ASub (ALit 1) (APlus (ALit 2) (APlus (ALit 3) (APlus (ALit 4) (ALit 5)))).

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
 | AMul a1 a2 => aeval a1 * aeval a2
(* BEGIN FIX *)
end.

Example aeval_test1 : forall n : nat, aeval (ALit n) = n.
(* END FIX *)
Proof. reflexivity. Qed.

(* BEGIN FIX *)
Example aeval_test2 : forall n m : nat, aeval (APlus (ALit n) (ALit m)) = n + m.
(* END FIX *)
Proof. reflexivity. Qed.

(* Ugy add meg exNum-ot, hogy mulTest bizonyithato legyen! *)
(* BEGIN FIX *)
Definition exNum
  :=
(* END FIX *)
  3.

(* BEGIN FIX *)
Example mulTest : aeval (AMul (ALit exNum) (ALit 10)) = 30.
(* END FIX *)
Proof. reflexivity. Qed.

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
intros. simpl. apply Nat.add_comm. Qed.

(* BEGIN FIX *)
Fixpoint vanbenneSub (a : AExp) : bool :=
(* END FIX *)
  match a with
  | ALit n => false
  | APlus a1 a2 => vanbenneSub a1 || vanbenneSub a2
  | ASub a1 a2 => true
  | AMul a1 a2 => vanbenneSub a1 || vanbenneSub a2
  end.

(* BEGIN FIX *)
Lemma lsub1 (a1 a2 : AExp) : vanbenneSub (ASub a1 a2) = true.
(* END FIX *)
(* Nincs szukseg indukciora. *)
Proof. simpl. reflexivity. Qed. 

(* BEGIN FIX *)
Lemma lsub2 (a1 a2 : AExp) : vanbenneSub a1 = true -> vanbenneSub (APlus a1 a2) = true.
(* END FIX *)
(* Nincs szukseg indukciora. *)
Proof. intro. simpl. rewrite -> H. simpl. reflexivity. Qed.

(* BEGIN FIX *)
From Coq Require Import Bool.Bool.

Lemma lsub3 (a1 a2 : AExp) : vanbenneSub a2 = true -> vanbenneSub (APlus a1 a2) = true.
(* END FIX *)
(* Hasznald az orb_true_r lemmat! Nincs szukseg indukciora. *)
Proof. Search bool. Check orb_true_r.
intro. simpl. rewrite -> H. apply orb_true_r. Qed.

(* BEGIN FIX *)
Lemma inverse : forall (n : nat), n - n = 0.
(* END FIX *)
(* Hasznalj indukciot n-en! *)
Proof. induction n. reflexivity. simpl. exact IHn. Qed.

(* Fakultativ. *)
Lemma nullaz : forall (a : AExp), exists (a' : AExp), aeval (ASub a a') = 0.
(* Hasznald inverse-t! Az "exists ..." bizonyitasahoz az exists taktika kell. *)
Proof. intros. exists a. simpl. apply inverse. Qed.


Lemma seged (n :nat) : S n <> n.
induction n.
* simpl. intro. discriminate H.
* intro. unfold "<>" in IHn. apply IHn.
  assert (pred (S (S n)) = pred (S n)).
** rewrite H. reflexivity.
** simpl in H0. assumption.
Qed.

(*
2+a = 1+b
---------
 1+a = b
*)


(* Fakultativ, kicsit nehezebb feladat. "A /\ B" bizonyitasahoz a split taktikat hasznald! *)
Lemma nullaz' : forall (a : AExp), exists (a' : AExp), aeval (ASub a a') = 0 /\ a' <> a.
Proof. intro. exists (APlus (ALit 0) a). split.
* simpl. apply inverse.
* unfold "<>". intro. 
  assert (leaves_count (APlus (ALit 0) a) = leaves_count a).
** rewrite -> H. reflexivity.
** simpl in H0. Import Arith.PeanoNat. apply (seged (leaves_count a)).
   assumption.
Qed.
(*

APlus
 / \
0  /\
  /a \
  ----

 /\
/a \
----

*)


(*
Proof. intros. destruct a.
exists (APlus (ALit 0) (ALit n)). split. simpl. apply inverse. simpl. intro. discriminate H. 
simpl. exists (ALit (aeval a1 + aeval a2)). simpl. split. apply inverse. intro. discriminate H.
simpl. exists (ALit (aeval a1 - aeval a2)). simpl. split. apply inverse. intro. discriminate H.
simpl. exists (ALit (aeval a1 * aeval a2)). simpl. split. apply inverse. intro. discriminate H.
Qed.
*)

(* Fakultativ. *)
Lemma lsub4 (a1 a2 : AExp) : vanbenneSub (APlus a1 a2) = false -> vanbenneSub a1 = false /\ vanbenneSub a2 = false.
Proof. intros. simpl in H. destruct (vanbenneSub a1).
simpl in H. discriminate H.
split. reflexivity. destruct (vanbenneSub a2).  simpl in H. discriminate H. reflexivity. Qed.
