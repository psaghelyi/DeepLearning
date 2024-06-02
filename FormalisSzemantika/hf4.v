Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

Notation "x + y" := (APlus x y) (at level 50, left associativity).
Notation "x - y" := (ASub x y) (at level 50, left associativity).
Coercion ALit : nat >-> AExp.

(* Ez az AExp-hez tartozo indukcio elve. *)
Lemma AExp_ind' : forall P : AExp -> Prop,
       (forall n : nat, P (ALit n)) ->
       (forall a1 : AExp,
        P a1 -> forall a2 : AExp, P a2 -> P (APlus a1 a2)) ->
       (forall a1 : AExp,
        P a1 -> forall a2 : AExp, P a2 -> P (ASub a1 a2)) ->
       forall a : AExp, P a.
Proof.
  intros P H1 H2 H3 a.
  induction a.
  - apply H1.
  - apply H2.
    + apply IHa1.
    + apply IHa2.
  - apply H3.
    + apply IHa1.
    + apply IHa2.
Qed.  
(* hasznalj induction-t! *)

Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

(* ez egy pelda a discriminate taktika hasznalatara.
ha van egy egyenlosegunk, aminek a ket oldalan kulonbozo
konstruktorok vannak, akkor abbol be tudunk latni barmit.
*)
Lemma nemegyenlo : ~ (ALit 3 = APlus (ALit 3) (ALit 0)).
Proof. intro. discriminate H. Qed.

Lemma nemInj : ~ (forall a1 a2, aeval a1 = aeval a2 -> a1 = a2).
Proof. 
  intro. assert (ALit 0 = APlus (ALit 0) (ALit 0)).
  apply H. simpl. reflexivity. discriminate H0.
Qed.
(* adj meg ket olyan kifejezest, melyek szemantikaja ugyanaz, de kulonboznek! 
hasznald a discriminate taktikat!
*)

Example mkExp : exists a, aeval a = 3.
(* hasznald az exists taktikat! *)
Proof.
  exists (ASub (ALit 5) (ALit 2)). simpl. reflexivity.
Qed.

Example mkExp2 : exists a1 a2, aeval a1 = aeval a2 /\ aeval a1 = 4 /\ a1 <> a2.
(* hasznald az exists es split taktikakat! *)
Proof.
  exists (APlus (ALit 2) (ALit 2)). 
  exists (ALit 4). 
  split. simpl. reflexivity. split. simpl. reflexivity. intro. discriminate H.
Qed.

Example notSubterm : forall (a b : AExp), APlus b a <> a.
(* indukcio a-n, hasznald discriminate-et es inversion-t *)
Proof.
  intros. induction a.
  - discriminate.
  - intro. inversion H. rewrite <- H1 in H2. unfold not in IHa2. apply IHa2 in H2. assumption.
  - discriminate.
Qed.

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.

Example ex1 : leaves (APlus (ALit 1) (APlus (ALit 2) (ALit 3))) = 3.
Proof. simpl. reflexivity. Qed.

Example ex2 : leaves (APlus (ALit 1) (ALit 1)) = 2.
Proof. simpl. reflexivity. Qed. 

Example ex3 : leaves (ALit 1) = 1.
Proof. simpl. reflexivity. Qed.

Lemma l1 : forall a1 a2, leaves (ASub a1 a2) = leaves (APlus a1 a2). 
Proof. intros. simpl. reflexivity. Qed.

Require Import Nat.
Require Import Arith.

Check max.
Fixpoint height (a : AExp) : nat := 
  match a with
  | ALit n => 0
  | APlus a1 a2 => 1 + max (height a1) (height a2)
  | ASub a1 a2 => 1 + max (height a1) (height a2)
  end.

(* adj meg egy olyan kifejezest, melynek a magassaga 2, es a levelei szama 3! *)
(* hasznald a max fuggvenyt! *)

Example ex4 : height (APlus (ALit 1) (APlus (ALit 2) (ALit 3))) = 2.
Proof. simpl. reflexivity. Qed.


Example ex5 : height (APlus (ALit 1) (ALit 1)) = 1.
Proof. simpl. reflexivity. Qed.

Lemma l2 : forall a1 a2, height (ASub a1 a2) = height (APlus a1 a2). 
Proof. intros. simpl. reflexivity. Qed.

Example expWithProperty : exists (a : AExp), leaves a = 3 /\ height a = 2.
(* /\ bizonyitasanal hasznalj split-et *)
Proof.
  exists (APlus (ALit 1) (APlus (ALit 2) (ALit 0))).
  split.
  - reflexivity.
  - reflexivity.
Qed.

Example notPoss : 
  not (exists (a : AExp), leaves a = 2 /\ height a = 0).  
(* hasznalj destruct-ot es discriminate-t! *)
Proof. 
intro. destruct H. destruct x.
  - simpl in H. destruct H. discriminate H.
  - simpl in H. destruct H. discriminate H0.
  - simpl in H. destruct H. discriminate H0.
Qed. 
  

(* Bizonyitsd be az inversion taktika nelkul! (hasznald a pred fuggvenyt) *)
Lemma inversionS (a b : nat) : S a = S b -> a = b.
(* Bizonyitsd be az inversion taktika nelkul! (hasznald a pred fuggvenyt) *)
Proof. Check pred. Compute (pred 3).
intro. assert (pred (S a) = pred (S b)).
rewrite H. reflexivity.
simpl in H0. assumption.
Qed.


Lemma heightPlus : forall a, height (APlus (ALit 0) a) = (1 + height a)%nat.
(* nem kell indukcio *)
Proof. simpl. reflexivity. Qed.

Lemma notPlus : forall (n : nat), 1 + n <> n.
(* indukcio n-en, hasznald: discriminate, inversion *)
Proof. 
  intro. induction n.
  - discriminate.
  - intro. inversion H.
Qed.


(* oran kimaradt *)
Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim' e1) (optim' e2)
  | ASub  e1 e2 => ASub  (optim' e1) (optim' e2)
  end.

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.
(* Innentol fakultativ feladatok. *)

Definition f : nat -> Prop := fun a => match a with
  | O => True
  | S _ => False
  end.

(* a kovetkezo feladatbol latszik, hogy a 
   discriminate taktika belul hogyan mukodik *)
(* hasznald f-et, ne hasznald discriminate-et! hasznalj assert-et. *)
Lemma discriminateOS (a : nat) : O <> S a.
Proof.
  intro. assert (f O = f (S a)).
  - rewrite H. reflexivity.
  - simpl in H0. destruct a.
    + simpl in H0. rewrite <- H0. trivial.
    + discriminate H.
Qed.


Lemma differentHeight : forall a, height (APlus (ALit 0) a) <> height a.
(* hasznald a heightPlus es notPlus lemmakat! *)
Proof. intro. intro. assert (height (APlus (ALit 0) a) = 1 + height a).
apply heightPlus. rewrite -> H in H0. destruct (height a).
apply notPlus with 0. rewrite <- H0. reflexivity.
apply notPlus with (S n). rewrite <- H0. reflexivity.
Qed.
Check plus_0_r.
Check le_n_S.
Check Nat.le_trans.
Check le_S.
Check Nat.add_le_mono.
Lemma max_plus : forall m n, max m n <= m + n.
(* m szerinti indukcio *)

Lemma minOne : forall a, 1 <= leaves a.

Check Nat.add_succ_r.
Check Nat.le_trans.
Check le_n_S.
Check Nat.add_le_mono.
Lemma leaves_height1 : forall (a : AExp), height a < leaves a.
(* kicsit nehez. a szerinti indukcio *)

Check Nat.le_refl.
Check Nat.le_trans.
Check Nat.le_max_l.
Check Nat.le_max_r.
Check Nat.pow_le_mono.
Check Nat.add_le_mono.
Lemma leaves_height2 (a : AExp) : leaves a <= 2 ^ height a.
(* a szerinti indukcio. erdemes eloszor papiron atgondolni. *)
