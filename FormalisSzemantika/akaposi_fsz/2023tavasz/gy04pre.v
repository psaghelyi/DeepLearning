(*            bevezetes          eliminalas
              (ha ez a Goal)     (ha ez a feltetel)
->            
forall        
/\            
\/            
exists        
False         
True          
=             
barmi         
Inductive     

= (Ind)       

Roviditesek: ~, <>
*)


Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.

Definition t1 : AExp := APlus (APlus (ALit 1) (ALit 2))(ALit 3).

Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

Compute aeval t1.

Fixpoint leaves_count (a : AExp) : nat :=

Compute leaves_count t1.

From Coq Require Import Arith.PeanoNat.

Lemma leaf_l_r: forall a1 a2 : AExp, leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
(* Search "+". *)

Example balIdIsmert : forall (a : nat),  0 + a = a.


Example balId : not (forall (a : AExp), APlus (ALit 0) a = a).
(* assert, discriminate *)

Definition f : nat -> Prop := fun a => match a with
  | O => True
  | S _ => False
  end.

(* hasznald f-et! *)
Lemma discriminateOS (a : nat) : O <> S a.

Example balIdErosebb : forall (a : AExp), APlus (ALit 0) a <> a.
(* inversion *)

(* Fakultativ HF. Tipp: hasznald a pred fuggvenyt*)
Lemma inversionS (a b : nat) : S a = S b -> a = b.


Lemma nemInj : ~ (forall a1 a2, aeval a1 = aeval a2 -> a1 = a2).


Example notSubterm : forall (a b : AExp), APlus b a <> a.

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.

Check max.
Fixpoint height (a : AExp) : nat := 

Example expWithProperty : exists (a : AExp), leaves a = 3 /\ height a = 2.

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

Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim' e1) (optim' e2)
  | ASub  e1 e2 => ASub  (optim' e1) (optim' e2)
  end.

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.

Definition optim'' a := ALit (aeval a).

Lemma optim''_sound (a : AExp) : aeval (optim'' a) = aeval a.

Check Nat.le_refl.
Check Nat.le_trans.
Check Nat.le_max_l.
Check Nat.le_max_r.
Check Nat.pow_le_mono.
Check Nat.add_le_mono.
Lemma leaves_height (a : AExp) : leaves a <= 2 ^ height a.

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
discriminate (induktiv tipus kulonbozo konstruktorati kulonbozok)
*)
