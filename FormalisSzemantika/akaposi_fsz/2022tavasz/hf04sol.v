Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

Lemma AExp_ind' : forall P : AExp -> Prop,
       (forall n : nat, P (ALit n)) ->
       (forall a1 : AExp,
        P a1 -> forall a2 : AExp, P a2 -> P (APlus a1 a2)) ->
       (forall a1 : AExp,
        P a1 -> forall a2 : AExp, P a2 -> P (ASub a1 a2)) ->
       forall a : AExp, P a.
(* hasznalj induction a-t! *)
intros. induction a.
apply H.
apply H0. assumption. assumption. 
apply H1. assumption. assumption. 
Qed.

Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

Lemma nemInj : ~ (forall a1 a2, aeval a1 = aeval a2 -> a1 = a2).
(* adj meg ket olyan kifejezest, melyek szemantikaja ugyanaz, de kulonboznek! *)
intro. assert (ALit 0 = APlus (ALit 0) (ALit 0)).
apply H. simpl. reflexivity. discriminate H0.
Qed.

Example notSubterm : forall (a b : AExp), APlus b a <> a.
(* indukcio a-n *)
intros. induction a.
- discriminate.
- intro. inversion H. apply IHa2. rewrite H1. assumption.
- discriminate.
Qed.

Example mkExp : exists a, aeval a = 3.
(* hasznald az exists taktikat! *)
exists (ALit 3). reflexivity. Qed.

Example mkExp2 : exists a1 a2, aeval a1 = aeval a2 /\ aeval a1 = 4 /\ a1 <> a2.
(* hasznald az exists es split taktikakat! *)
exists (ALit 4). exists (APlus (ALit 0) (ALit 4)). split. reflexivity.
split. reflexivity. intro. discriminate. Qed.

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.

Example ex1 : leaves (APlus (ALit 1) (APlus (ALit 2) (ALit 3))) = 3.
reflexivity. Qed.
Example ex2 : leaves (APlus (ALit 1) (ALit 1)) = 2.
reflexivity. Qed.
Example ex3 : leaves (ALit 1) = 1.
reflexivity. Qed.

Lemma l1 : forall a1 a2, leaves (ASub a1 a2) = leaves (APlus a1 a2). 
reflexivity. Qed.

Require Import Nat.
Require Import Arith.

Check max.
Fixpoint height (a : AExp) : nat := match a with
  | ALit _ => 0
  | APlus a1 a2 => 1 + max (height a1) (height a2)
  | ASub  a1 a2 => 1 + max (height a1) (height a2)
  end.

Example ex4 : height (APlus (ALit 1) (APlus (ALit 2) (ALit 3))) = 2.
reflexivity. Qed.

Example ex5 : height (APlus (ALit 1) (ALit 1)) = 1.
reflexivity. Qed.

Lemma l2 : forall a1 a2, height (ASub a1 a2) = height (APlus a1 a2). 
reflexivity. Qed.

Example expWithProperty : exists (a : AExp), leaves a = 3 /\ height a = 2.
(* /\ bizonyitasanal hasznalj split-et *)
Proof. exists (APlus (APlus (ALit 1) (ALit 1)) (ALit 1)). split; reflexivity.
Qed.

Example notPoss : 
  not (exists (a : AExp), leaves a = 2 /\ height a = 0).
(* hasznalj destruct-ot es discriminate-t! *)
intro. destruct H. destruct H.
destruct x.
- simpl in H. discriminate H.
- simpl in H0. discriminate H0.
- simpl in H0. discriminate H0.
Qed.

(* Bizonyitsd be az inversion taktika nelkul! (hasznald a pred fuggvenyt) *)
Lemma inversionS (a b : nat) : S a = S b -> a = b.
Proof. Check pred. Compute (pred 3).
intro. assert (pred (S a) = pred (S b)).
rewrite -> H. reflexivity. simpl in H0. assumption.
Qed.

Lemma heightPlus : forall a, height (APlus (ALit 0) a) = 1 + height a.
(* nem kell indukcio *)
Proof. simpl. reflexivity.
Qed.

Lemma notPlus : forall n, 1 + n <> n.
(* indukcio n-en, hasznald: discriminate, inversion *)
intro. induction n. discriminate.
simpl. intro. inversion H. apply IHn. assumption.
Qed.

(* Innentol fakultativ feladatok. *)

Lemma differentHeight : forall a, height (APlus (ALit 0) a) <> height a.
(* hasznald a heightPlus es notPlus lemmakat! *)
Proof. intro. intro. assert (height (APlus (ALit 0) a) = 1 + height a).
apply heightPlus. rewrite -> H in H0. destruct (height a).
apply notPlus with 0. rewrite <- H0. reflexivity.
apply notPlus with (S n). rewrite <- H0. reflexivity.
Qed.

Require Import Nat.
Require Import Arith.

Check plus_0_r.
Check le_n_S.
Check Nat.le_trans.
Check le_S.
Check Nat.add_le_mono.
Lemma max_plus : forall m n, max m n <= m + n.
(* m szerinti indukcio *)
intro. induction m.
- simpl. apply Nat.le_refl.
- intro. simpl. destruct n.
-- simpl. rewrite (plus_0_r m). apply Nat.le_refl.
-- simpl. apply (Nat.le_trans _ _ _ (le_n_S _ _ (IHm n))).
   exact (Nat.add_le_mono _ _ _ _ (le_refl (S m)) (le_S _ _ (le_refl n))).
Qed.

Lemma minOne : forall a, 1 <= leaves a.

Check Nat.add_succ_r.
Check Nat.le_trans.
Check le_n_S.
Check Nat.add_le_mono.
Lemma leaves_height1 : forall (a : AExp), height a < leaves a.
(* kicsit nehez. a szerinti indukcio *)
intro. induction a.
- simpl. auto.
- simpl. unfold "<".
  apply (Nat.le_trans _ _ _ (le_n_S _ _ (le_n_S _ _ (max_plus (height a1) (height a2))))).
  unfold "<" in IHa1. unfold "<" in IHa2.
  rewrite <- (Nat.add_succ_r (height a1) (height a2)).
  assert (S (height a1 + S (height a2)) = S (height a1) + S (height a2)). reflexivity.
  rewrite H. exact (Nat.add_le_mono _ _ _ _ IHa1 IHa2).
- simpl. unfold "<".
  apply (Nat.le_trans _ _ _ (le_n_S _ _ (le_n_S _ _ (max_plus (height a1) (height a2))))).
  unfold "<" in IHa1. unfold "<" in IHa2.
  rewrite <- (Nat.add_succ_r (height a1) (height a2)).
  assert (S (height a1 + S (height a2)) = S (height a1) + S (height a2)). reflexivity.
  rewrite H. exact (Nat.add_le_mono _ _ _ _ IHa1 IHa2).
Qed.

Check Nat.le_refl.
Check Nat.le_trans.
Check Nat.le_max_l.
Check Nat.le_max_r.
Check Nat.pow_le_mono.
Check Nat.add_le_mono.
Lemma leaves_height2 (a : AExp) : leaves a <= 2 ^ height a.
(* a szerinti indukcio. erdemes eloszor papiron atgondolni. *)








