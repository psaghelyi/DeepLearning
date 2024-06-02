(* BEGIN FIX *)
Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

(* elso parameteren rekurzio, nem ugy, mint a gyakorlaton: *)
(* BEGIN FIX *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity).

Lemma leftid (n : Nat) : O + n = n.
(* END FIX *)
reflexivity. Qed.

(* BEGIN FIX *)
Lemma rightid (n : Nat) : n + O = n.
(* END FIX *)
induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

(* BEGIN FIX *)
Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c).
(* END FIX *)
(* a szerinti indukciot erdemes! *)
induction a. reflexivity. simpl. rewrite IHa. reflexivity. Qed.

(* BEGIN FIX *)
Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.
(* END FIX *)
intros. rewrite -> H. reflexivity. Qed.

(* BEGIN FIX *)
Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
(* END FIX *)
intros. induction a. reflexivity. simpl. rewrite <- IHa. reflexivity. Qed.

(* BEGIN FIX *)
Lemma comm (a b : Nat) : a + b = b + a.
(* END FIX *)
(* Az alapesetben hasznalj egy korabban bizonyitott lemmat, az indukcios lepesben rewrite-olj (plus_r_s b a)-t! *)
induction a. simpl. rewrite (rightid b). reflexivity. simpl. rewrite <- (plus_r_s b a). simpl. rewrite IHa. reflexivity. Qed.

(* BEGIN FIX *)
Fixpoint times (a b : Nat) : Nat :=
  match a with
  | O => O
  | S a' => b + times a' b
  end.

Notation "x * y" := (times x y)
  (at level 40, left associativity).

Lemma times_leftid (a : Nat) : S O * a = a.
(* END FIX *)
simpl. exact (rightid _). Qed.

(* BEGIN FIX *)
Lemma times_rightid (a : Nat) : a * S O = a.
(* END FIX *)
induction a.
- reflexivity.
- simpl. rewrite -> IHa. reflexivity.
Qed.

(* BEGIN FIX *)
Lemma times_leftzero (a : Nat) : O * a = O.
(* END FIX *)
reflexivity. Qed.

(* BEGIN FIX *)
Lemma times_rightzero (a : Nat) : a * O = O.
(* END FIX *)
induction a.
- reflexivity.
- simpl. assumption.
Qed.

(* BEGIN FIX *)
Lemma rdistr (a b c : Nat) : (a + b) * c =  a * c + b * c.
(* END FIX *)
(* Use rewrite with assoc in the inductive step! *)
induction a.
- reflexivity.
- simpl. rewrite -> IHa. rewrite -> (assoc c (a * c) (b * c)). reflexivity.
Qed.

(* BEGIN FIX *)
Lemma times_assoc (a b c : Nat) : (a * b) * c = a * (b * c).
(* END FIX *)
(* Use rdistr in the inductive step! *)
induction a.
- simpl. reflexivity.
- simpl. rewrite <- IHa. simpl. exact (rdistr b (a * b) c).
Qed.

(* BEGIN FIX *)
Lemma comm_helper (a b : Nat) : b + b * a = b * S a.
(* END FIX *)
(* You will have to use assoc and comm in the inductive step. *)
induction b.
- reflexivity.
- simpl. rewrite <- IHb.
  rewrite <- (assoc b a (b * a)). rewrite -> (comm b a).
  rewrite -> (assoc a b (b * a)). reflexivity.
Qed.

(* BEGIN FIX *)
Lemma times_comm (a b : Nat) : a * b = b * a.
(* END FIX *)
(* Use comm_helper in the inductive step. *)
induction a.
- rewrite (times_rightzero b). reflexivity.
- simpl. rewrite -> IHa. exact (comm_helper a b).
Qed.

(* Fakultativ: *)
Definition pred (n : Nat) : Nat :=
  match n with
  | O => O
  | S n => n
  end.

Lemma S_inj (a b : Nat) : S a = S b -> a = b.
(* Use cong pred! *)
Proof.
  intros. Check (cong pred _ _ H). exact (cong pred _ _ H).
Qed.

Definition P : Nat -> Prop := fun n =>
  match n with
  | O => True
  | S _ => False
  end.

Lemma O_S_disj (a : Nat) : O <> S a.
Proof.
  intro. assert (P O = P (S a)).
  - rewrite -> H. reflexivity.
  - simpl in H0. rewrite <- H0. trivial.
Qed.
