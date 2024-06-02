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
Proof. induction a.
* reflexivity.
* simpl. rewrite -> IHa. reflexivity. Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.
Proof.
    intro. rewrite -> H. reflexivity.
Qed. 
(* END FIX *)

(* BEGIN FIX *)
Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
Proof.
    intros. induction a.
    - reflexivity.
    - simpl. apply cong. assumption.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma comm (a b : Nat) : a + b = b + a.
Proof.
    induction a.
    - simpl. rewrite rightid. reflexivity.
    - simpl. Search (_ + S _). rewrite <- plus_r_s. simpl. rewrite IHa. reflexivity.
Qed.
   (* END FIX *)

(* BEGIN FIX *)
Fixpoint times (a b : Nat) : Nat := match a with
| O => O
| S n => b + (times n b)
end.

Notation "x * y" := (times x y)
  (at level 40, left associativity).

Lemma times_leftid (a : Nat) : S O * a = a.
Proof.
  induction a.
  - reflexivity.
  - destruct a. 
    + simpl. reflexivity.
    + simpl. rewrite <- IHa. reflexivity.
Qed.

(* END FIX *)

(* BEGIN FIX *)
Lemma times_rightid (a : Nat) : a * S O = a.
Proof.
  induction a.
  - reflexivity.
  - simpl. rewrite -> IHa. reflexivity.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma times_leftzero (a : Nat) : O * a = O.
Proof.
  reflexivity.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma times_rightzero (a : Nat) : a * O = O.
Proof.
  induction a.
  - reflexivity.
  - simpl. assumption.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma times_assoc (a b c : Nat) : (a * b) * c = a * (b * c).
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- IHa.
  assert(H: forall a b : Nat, S a * b = b + a * b). {
    intros. induction a0.
    - reflexivity.
    - simpl. rewrite <- IHa0. reflexivity.    
  }
  destruct a, b, c.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. repeat rewrite times_rightzero. reflexivity.
  + simpl. rewrite rightid. rewrite rightid. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. repeat rewrite times_rightzero. reflexivity.
  + simpl. apply cong. 
  assert (a * S b = a + a * b). {
    induction a. 
    - simpl. reflexivity.
    - simpl. apply cong. rewrite <- H. rewrite IHa0.
      + rewrite H. repeat rewrite <- assoc. 
  }
Qed.

(* END FIX *)

(* BEGIN FIX *)
Lemma times_comm (a b : Nat) : a * b = b * a.
(* END FIX *)