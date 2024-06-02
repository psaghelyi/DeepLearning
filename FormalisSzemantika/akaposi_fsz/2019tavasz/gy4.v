Inductive aexp : Type :=
  | ANum (n : nat)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | APlus (a1 a2 : aexp).

Coercion ANum : nat >-> aexp.

Definition t : aexp :=
  APlus
    (AMinus
      3
      2)
    5.

Set Printing Coercions.

Eval compute in t.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum   n     => n
  | APlus  a1 a2 => aeval a1 + aeval a2
  | AMinus a1 a2 => aeval a1 - aeval a2
  | AMult  a1 a2 => aeval a1 * aeval a2
  end.

Eval compute in aeval t.
Eval compute in aeval (APlus 5000 5000).

Fixpoint optim (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus  e1 (ANum 0) => optim e1
  | APlus  e1 e2 => APlus  (optim e1) (optim e2)
  | AMinus e1 e2 => AMinus (optim e1) (optim e2)
  | AMult  e1 e2 => AMult  (optim e1) (optim e2)
  end.

Eval compute in optim (optim
   (APlus 0 (APlus 0 0))).

Lemma optim_sound (a : aexp) :
  aeval (optim a) = aeval a.
Proof.
  intros.
  induction a;
  try (simpl; reflexivity);
  try (simpl; rewrite -> IHa1; rewrite -> IHa2;
       reflexivity).
  simpl. destruct a2;
    try (destruct n; simpl; rewrite -> IHa1;
         trivial);
    try (simpl; rewrite -> IHa1;
         simpl in IHa2;
         rewrite -> IHa2; reflexivity).
Qed.

Fixpoint optim2 (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus  (ANum x) (ANum y) => ANum (x+y)
  | APlus  e1 e2 => APlus  (optim2 e1) (optim2 e2)
  | AMinus e1 e2 => AMinus (optim2 e1) (optim2 e2)
  | AMult  e1 e2 => AMult  (optim2 e1) (optim2 e2)
  end.

Lemma optim2_sound (a : aexp) :
  aeval (optim2 a) = aeval a.
Proof.
  intros a.
  induction a.
  simpl. reflexivity.
  simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity. 
  simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity. 
  simpl. destruct a1; destruct a2;
  try (simpl; reflexivity);
  try (simpl; simpl in IHa1; simpl in IHa2;
       rewrite -> IHa2; reflexivity);
  try (simpl; simpl in IHa1; simpl in IHa2;
       rewrite -> IHa1; reflexivity);
  try (simpl; simpl in IHa1; simpl in IHa2;
       rewrite -> IHa1; rewrite -> IHa2; reflexivity).
Qed.








