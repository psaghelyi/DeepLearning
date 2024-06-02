(* BEGIN FIX *)
(** Pótold a hiányzó kódrészleteket! A BEGIN FIX és END FIX közötti részeket ne módosítsd! Akkor jó a megoldásod, ha a Coq elfogadja az egészet (zöld lesz a teljes fájl).*)
(** Fill out the missing parts! Do not modify the code between BEGIN FIX and END FIX! *)
Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Fixpoint plus (n m : Nat) : Nat :=
  match m with
  | O => n
  | S m' => S (plus n m')
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity).

Lemma plus_r_s : forall (a b : Nat), a + S b = S a + b.
Proof. intros. induction b.
- simpl. reflexivity.
- simpl. simpl in IHb. rewrite -> IHb. reflexivity.
Qed.
(* END FIX *)


