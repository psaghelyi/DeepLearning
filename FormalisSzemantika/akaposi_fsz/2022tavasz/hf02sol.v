(* BEGIN FIX *)
(** Pótold a hiányzó kódrészleteket! A BEGIN FIX és END FIX közötti részeket ne módosítsd! Akkor jó a megoldásod, ha a Coq elfogadja az egészet (zöld lesz a teljes fájl).*)
(** Fill out the missing parts! Do not modify the code between BEGIN FIX and END FIX! *)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Fixpoint plus (n m : Nat) {struct n} : Nat := match n with
| O => m
| S n' => S (plus n' m)
end.

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

Lemma leftid (n : Nat) : O + n = n.
Proof. simpl. reflexivity. Qed.

Lemma rightid (n : Nat) : n + O = n.
Proof. simpl. induction n.
* reflexivity.
* simpl. rewrite -> IHn. reflexivity. Qed.

Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c).
(* END FIX *)
Proof. induction a. reflexivity. simpl. rewrite IHa. reflexivity. Qed.

(* BEGIN FIX *)
Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.
(* END FIX *)
Proof. intros. rewrite -> H. reflexivity. Qed.

(* BEGIN FIX *)
Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
(* END FIX *)
Proof. intros. induction a. reflexivity. simpl. rewrite <- IHa. reflexivity. Qed.

(* BEGIN FIX *)
Lemma comm (a b : Nat) : a + b = b + a.
(* END FIX *)
Proof. induction a. simpl. rewrite (rightid b). reflexivity. simpl. rewrite <- (plus_r_s b a). simpl. rewrite IHa. reflexivity. Qed.

(* BEGIN FIX *)
Fixpoint times (a b : Nat) : Nat := match a with
| O => O
| S n => b + (times n b)
end.

Notation "x * y" := (times x y)
  (at level 40, left associativity).

Lemma times_leftid (a : Nat) : S O * a = a.
(* END FIX *)
Proof.
simpl. exact (rightid _). Qed.

(* BEGIN FIX *)
Lemma times_rightid (a : Nat) : a * S O = a.
(* END FIX *)
Proof.
induction a.
- reflexivity.
- simpl. rewrite -> IHa. reflexivity.
Qed.

(* BEGIN FIX *)
Lemma times_leftzero (a : Nat) : O * a = O.
(* END FIX *)
Proof. reflexivity. Qed.

(* BEGIN FIX *)
Lemma times_rightzero (a : Nat) : a * O = O.
(* END FIX *)
Proof.
induction a.
- reflexivity.
- simpl. assumption.
Qed.

Lemma rdistr (a b c : Nat) : (a + b) * c =  a * c + b * c.
Proof.
induction a.
- reflexivity.
- simpl. rewrite -> IHa. rewrite -> (assoc c (a * c) (b * c)). reflexivity.
Qed.

(* BEGIN FIX *)
Lemma times_assoc (a b c : Nat) : (a * b) * c = a * (b * c).
(* END FIX *)
induction a.
- simpl. reflexivity.
- simpl. rewrite <- IHa. simpl. exact (rdistr b (a * b) c).
Qed.

Lemma comm_helper (a b : Nat) : b + b * a = b * S a.
Proof.
induction b.
- reflexivity.
- simpl. rewrite <- IHb.
  rewrite <- (assoc b a (b * a)). rewrite -> (comm b a).
  rewrite -> (assoc a b (b * a)). reflexivity.
Qed.


(* BEGIN FIX *)
Lemma times_comm (a b : Nat) : a * b = b * a.
(* END FIX *)
induction a.
- rewrite (times_rightzero b). reflexivity.
- simpl. rewrite -> IHa. exact (comm_helper a b).
Qed.
