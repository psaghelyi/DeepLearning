Inductive Nat : Type := O | S (n:Nat).

Definition four := S (S (S (S O))).
Definition six := S (S four).
Definition eight := S (S six).

Fixpoint plus ( n m : Nat ) {struct n} : Nat :=
  match n with 
  | O => m 
  | S n' => S (plus n' m) 
  end.

Notation "n + m" := (plus n m) (at level 50, left associativity).

Lemma plus_lid :
  forall n : Nat, O + n = n.
Proof.
  intro.
  simpl.
  reflexivity.
Qed.

Lemma plus_rid :
  forall n : Nat, n + O = n.
Proof.
  intro.
  induction n as [|n'].
    (* n = O *)  (* would also work: *)
    simpl.       (* apply plusn_lid. *)
    reflexivity.
    (* n = S n', n' + O = n' *)
    simpl.         (* would also work: *)
    rewrite IHn'.  (* apply S_cong.    *)
    reflexivity.   (* apply IHn'.      *)
Qed.

Lemma plus_l_S :
  forall n m : Nat, S n + m = S (n + m).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma plus_r_S :
  forall n m : Nat, n + S m = S (n + m).
Proof.
  intros. simpl. (* plus n (S m) *)
  induction n as [|n'].
  * simpl. reflexivity.
  * simpl. rewrite IHn'. reflexivity.
Qed.

Lemma plus_comm :
  forall n m : Nat, n + m = m + n.
Proof.
  intros. induction n.
  * simpl. Check plus_rid. rewrite plus_rid. reflexivity.
  * simpl. rewrite IHn. rewrite plus_r_S. reflexivity.
Qed.


Definition pred (n : Nat) : Nat :=
match n with
| O => O
| S n' => n'
end
.

Theorem general_cong (f : Nat -> Nat) :
  forall n m : Nat, n = m -> f n = f m.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma succ_inj :
  forall n m : Nat, S n = S m -> n = m.
Proof.
  (* intros. inversion H. reflexivity. *)
  intros. apply (general_cong pred) in H. simpl in *. assumption.
Qed.

Definition P (n : Nat) : Prop :=
match n with
| O => True
| S n' => False
end.

Theorem zero_suc (a : Nat) : O <> S a.
Proof.
  assert (P O). {  
    simpl. reflexivity.
  }
  simpl. unfold not. intro. rewrite H0 in H. simpl in H. assumption.
Qed.