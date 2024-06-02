Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).

Lemma even_not_odd : forall n, even n -> ~ even (S n).
Proof.
  intros n H1 H2.
    induction H2.
    - inversion H1.
    - inversion H1.
      + apply IHeven. apply H3.
      + apply IHeven. apply H3.
