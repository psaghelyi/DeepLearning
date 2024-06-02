(* jelszó: almafa2 *)

Lemma alma (a b : nat) : a = b \/ a <> b.
 generalize dependent a.
 generalize dependent b.
 induction a. 
 admit.
Admitted.

Lemma alma2 : forall a b : nat, b + b * a = b * S a.
Proof.
  intros. induction a.
  * simpl.