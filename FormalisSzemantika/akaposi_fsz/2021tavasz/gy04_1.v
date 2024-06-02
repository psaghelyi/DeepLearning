Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).

Fixpoint aeval (a : AExp) : nat :=
  match a with
  | ALit n      => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | ASub  a1 a2 => aeval a1 - aeval a2
  end.

Lemma inverse : forall (n : nat), n - n = 0.
intro. induction n. simpl. reflexivity. simpl. exact IHn. Qed.

Lemma nullaz : forall (a : AExp), exists (a' : AExp), aeval (ASub a a') = 0.
intro. exists a. simpl. apply inverse. Qed.

(* uj taktika: inversion! *)
Example notSubterm : forall (a b : AExp), APlus b a <> a.
Admitted.

Compute (APlus (ALit 0) (ALit 1)).
Compute (APlus (ALit (1 + 1)) (ALit 1)).
Compute aeval (APlus (ALit 0) (ALit 1)).
Print Nat.add.

(* hasznald notSubterm-et! *)
Example balIdErosebb : forall (a : AExp), APlus (ALit 0) a <> a.
Proof. intro. intro. simpl in H. induction a.
(*
[[ APlus (ALit 0) a ]] = 0 + [[ a ]] = [[ a ]]

- forall n, P (ALit n)
- forall a1 a2, P a1 /\ P a2 -> P (APlus a1 a2)
- forall a1 a2, P a1 /\ P a2 -> P (ASub a1 a2)
-----------------------------------------------
forall a, P a
*)
 (*  S a = S b -> a = b *)
- discriminate H.
- inversion H. apply IHa2. exact H2.
- discriminate H.
Qed.

(* Fakultativ, kicsit nehezebb feladat. "A /\ B" bizonyitasahoz a split taktikat hasznald! *)
Lemma nullaz' : forall (a : AExp), exists (a' : AExp), aeval (ASub a a') = 0 /\ a' <> a.
Proof. intro. exists (APlus (ALit 0) a). split.
- Print Nat.add. simpl. apply inverse.
(*
aeval (ASub a (APlus (ALit 0) a)) = 
aeval a - aeval (APlus (ALit 0) a) =
aeval a - (aeval (ALit 0) + aeval a) =
aeval a - (0 + aeval a) =
aeval a - aeval a
*)
- unfold not. intro. apply (balIdErosebb a). exact H. Qed.
(* ez is mukodik: apply balIdErosebb in H *)

(*
eddigi taktikak:
változókezelés, definíció feloldás: exact, unfold, simpl, assert
bevezető taktikák: intro(s), reflexivity, split, left, right, exists
eliminator taktikák: apply,  rewrite,     destruct,                  induction
legokosabb: auto, contradiction, trivial, symmetry, discriminate, inversion
*)

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.

Check max.
Compute max 2 3.

Fixpoint height (a : AExp) : nat := match a with
  | ALit _ => 0
  | APlus a1 a2 => 1 + max (height a1) (height a2)
  | ASub  a1 a2 => 1 + max (height a1) (height a2)
  end.

Example expWithProperty : exists (a : AExp), leaves a = 3 /\ height a = 2.
exists (APlus (APlus (ALit 0) (ALit 0)) (ALit 0)). split; simpl; reflexivity.
Qed.
(*
   +
  / \
 +   0
 /\
0  0

*)

(*  a + 0 = a *)
Fixpoint optim (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus e1 (ALit 0) => optim e1
  | APlus e1 e2 => APlus (optim e1) (optim e2)
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.

Compute optim (APlus (APlus (ALit 1) (ALit 0)) (ALit 0)).

Require Import Coq.Arith.Plus.
Check plus_0_r.

Lemma optim_sound (a : AExp) :
  aeval (optim a) = aeval a.
Proof. induction a.
1:{ simpl. reflexivity. }
2:{ simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity. }
(*
aeval (optim (ASub a1 a2)) =
aeval (ASub  (optim e1) (optim e2)) =
aeval (optim e1) - aeval (optim e2)
aeval (ASub a1 a2) = aeval a1 - aeval a2
*)
1:{ simpl. destruct a2.
- destruct n.
-- simpl. rewrite -> IHa1. symmetry. apply plus_0_r.
-- simpl. rewrite -> IHa1. reflexivity.
- simpl. rewrite -> IHa1. simpl in IHa2. rewrite -> IHa2. reflexivity.
- simpl. rewrite -> IHa1. simpl in IHa2. rewrite -> IHa2. reflexivity. }
Qed.
