(*            bevezetes          eliminalas
              (ha ez a Goal)     (ha ez a feltetel)
->            intro              apply
forall        intro              apply
/\            split              destruct
\/            left, right        destruct
exists        exists             destruct
False         -                  destruct
True          trivial            -
=             reflexivity        rewrite
barmi                            assumption
Inductive     (konstruktorok)    destruct, induction

= (Ind)       

Roviditesek: ~, <>
(~ (x = 3)) = (x <> 3) = ((x = 3) -> False)
*)


Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

Definition t1 : AExp := APlus (APlus (ALit 1) (ALit 2))(ALit 3).
(* +
   /\
  +  3
 /\
 1 2
*)

(* kiertekeles, evaluation, interpretation, denotional semantics, jelentes *)
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

(* - metanyelv = implementacios nyelv = metaelmelet = matematika nyelve = 
     amelyik nyelven beszelunk = Coq
   - object language = targynyelv = AExp = egyszeru aritmetikai kifejezesek nyelve
  *)

Compute aeval t1.

Fixpoint leaves_count (a : AExp) : nat := match a with
  | ALit _ => 1
  | APlus a1 a2 => leaves_count a1 + leaves_count a2
  | ASub  a1 a2 => leaves_count a1 + leaves_count a2
  end.

Compute leaves_count t1.

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
(* Search "+". *)
simpl. intros.
Search "+". rewrite (Nat.add_comm (leaves_count a1) (leaves_count a2)). reflexivity.
Qed.

Example balIdIsmert : forall (a : nat),  0 + a = a.
intro. simpl. reflexivity. Qed. 

Example balId' : not (forall (a : nat), S a = a).
(* forall (a : nat), S a = a 
~ (S O = O)
*)
Proof. unfold "~". intro. assert (S O = O). apply H. discriminate H0. Qed.

Example balId : not (forall (a : AExp), APlus (ALit 0) a = a).
Proof. unfold "~". intro. assert (APlus (ALit 0) (ALit 1) = ALit 1). apply H. discriminate H0. Qed.

(* assert, discriminate 

  +
 /\
0  /\          /\
  / a\        /a \
  ----        ----
*)

(* P egy predikatum (nat feletti unaris relacio) *)
Definition P' : nat -> Prop := fun n => n = 3.
Example exP' : P' (1+2).
Proof. simpl. unfold P'. reflexivity. Qed.

Definition P : nat -> Prop := fun a => match a with
  | O => True
  | S _ => False
  end.

Compute P 33.
Compute P 1.
Compute P 0.

Lemma exFalsoQuodlibet (A : Prop) : False -> A.
Proof. intro. destruct H. Qed.

Lemma congPred (A : Set)(P : A -> Prop)(a0 a1 : A)(e : a0 = a1) : P a0 = P a1.
Proof. rewrite e. reflexivity. Qed.

(* hasznald f-et! *)
Lemma discriminateOS (a : nat) : O <> S a.
unfold "<>". intro. assert (P 0 = P (S a)). (* ket lepesben csinalom a bizonyitast *)
(* ezt akartam belatni: False
1. lepesben belatom : P 0 = P (S a)
2. lepesben : P 0 = P (S a) -> False
*)
- rewrite -> H. reflexivity.
- unfold P in H0. (* simpl in H0. *)
  rewrite <- H0. trivial. Qed.
(*
0 = S a
  ->
True = P 0 = P (S a) = False

H0 : True = False
rewrite <- H0
new goal: True
*)
(*
          S
          |
  O       O

*)

Lemma discriminateOS' (a : nat) : O <> S a.
Proof. intro. discriminate H. Qed.


(* HF: ezt belatni ugy, hogy height (APlus (ALit 0) a) <> height a  *)
Example balIdErosebb : forall (a : AExp), APlus (ALit 0) a <> a.
(* inversion *)
Proof.
intro.   induction a.
Check AExp_ind. (* HF: bizonyitsatok be AExp_ind-et kezzel (induction taktiktat hasznalni kell). *)
- intro. discriminate H.
- intro. inversion H. unfold "<>" in IHa2. apply IHa2. assumption.
- intro. discriminate H.
Qed.

(*
nat-indukcio elve:
  P : nat -> Prop                                   P n := (n + 0 = n)
  forall n, P n
  - P O                         alapeset            0 + 0 = 0
  - forall m, P m -> P (S m)    induktiv eset       m + 0 = m -> S (m + 0) = S m

AExp-indukcio:
  P : AExp -> Prop                                  P a := APlus (ALit 0) a <> a
  - forall n, P (ALit n)        alapeset
  - forall a1 a2, P a1 -> P a2 -> P (APlus a1 a2)   egyik induktiv eset
  - forall a1 a2, P a1 -> P a2 -> P (ASub a1 a2)    masik induktiv eset
*) 

(* Fakultativ HF. Tipp: hasznald a pred fuggvenyt*)
Lemma inversionS (a b : nat) : S a = S b -> a = b.
intro. inversion H. reflexivity. Qed.


(* eddigi taktikak:
Inductive
Definition
Theorem
Lemma
Proof
Qed
Fixpoint
Admitted
Check

match
simpl
unfold (at 1, at 2)
reflexivity
destruct
assumption
rewrite
intro
induction
apply
 *)

(* ma:
Search
assert
...
simpl in
discriminate (induktiv tipus kulonbozo konstruktorai kulonbozok)
inversion (induktiv tipus konstruktorai injektivek)
*)
