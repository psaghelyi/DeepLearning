(*
Lemma times_comm (a b : Nat) : a * b = b * a.
*)

(* HF *)

(* Aritmetikai kifejezésnyelv és denotációs szemantika, példa
   kiértékelések *)

From Coq Require Import Init.Nat.

Check nat.

Check 5.

Compute 1 + 3.

(*a ::= n | a1 + a2 | a1 - a2*)
(*a ::= alit(n) | plus(a1,a2) | sub(a1,a2)*)
Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
.
(* objektumnyelv = AExp *)
(* metanyelv     = Coq*)

(*(1 + 1) + 1, mint AExp, nem egyenlo 1 + (1 + 1) *)

Example notEq : APlus (APlus (ALit 1) (ALit 1)) (ALit 1) <>
                APlus (ALit 1) (APlus (ALit 1) (ALit 1)) .
Proof. intro. discriminate. Qed.

Example notEq' : (1 + 1) + 1 = 1 + (1 + 1).
Proof. simpl. reflexivity. Qed.

Example balId' (n : nat) :  0 + n = n.
Proof. simpl. reflexivity. Qed.

Example balId : not (forall (a : AExp), APlus (ALit 0) a = a).
Proof. unfold "~". intro.
assert (APlus (ALit 0) (ALit 1) = ALit 1).
apply (H (ALit 1)).
discriminate H0.
Qed.

(* HF

forall n, not (S n = n).

Example balIdErdekes : 
  forall (a : AExp), not (APlus (ALit 0) a = a).
*)

(* balId : 0 + n = n *)


Locate "<>".
Locate "=".
Print not. (* not A = A -> False *)
(* (a <> b) = not (a = b) = (a = b) -> False *)

(*
A                     bevezeto     eliminalo   (taktikak)
                      (Goal = A)   (ha A a feltetelek kozott)
A -> B                intro(s)     apply
forall (x : A), B     intro(s)     apply
exists (x : A), B     exists       destruct
A /\ B                split        destruct
A \/ B                left,right   destruct
True                  split        NINCS
False                 NINCS        destruct

(=                    reflexivity  rewrite)

f : A -> C    exact (f a)
----------   ----->      KESZ
C
    |
   apply f
    |
    v
f : A -> C
---------
A

Goal = A -> B -> C
    |
  intros
    |
    v

x : A
y : B
------------
Goal = C
*)

(*
AExp = {ALit 0, ALit 1, ALit 2, ...
        APlus (ALit 0) (ALit 0), APlus (ALit 0) (ALit 1), ...
        ASub (ALit 0) (ALit 0), ASub (ALit 0) (ALit 1), ...,
        APlus (APlus ? ?) ?,  }

*)

(* Checkek *)
(* (5 + 7) - 42 *)
Check (ASub (APlus (ALit 5) (ALit 7)) (ALit 42)).

(*
Ird le, mint AExp elemet!
    +
   / \
  +   3
 / \
1  2
*)
Definition t1 : AExp := APlus (APlus (ALit 1) (ALit 2)) (ALit 3).

(*
Ird le, mint AExp elemet!
    +
   / \
  1   +
     / \
    2   3
*)
Definition t1' : AExp := APlus (ALit 1) (APlus (ALit 2) (ALit 3)).

(*
Ird le, mint AExp elemet!
    +
   / \
  3   +
     / \
    1  2
*)
(*Definition t1'' : AExp := *)

(*
Ird le, mint AExp elemet!
     -
   /  \
  +    +
 / \   /\
1  2  +  3
     / \
    4  5
*)
(*Definition t2 : AExp := *)


(* Rajzold le! *)
Definition t3 := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).
Definition t3' := ASub (APlus (ALit 5) (ALit 7)) (ALit 42).
(*
t3'
       -
       /\
      /  \
     +    42
    /\
   5  7
*)

Compute 5 - 15.

(* notation AExp-re is *)


(* denotacios szemantika
   [[_]] : AExp -> nat
*)
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
end.

Lemma nemInj : not (forall a1 a2, aeval a1 = aeval a2 -> a1 = a2).
Proof. intro.
assert (APlus (ALit 1) (ALit 2) = APlus (ALit 2) (ALit 1)).
apply H. simpl. reflexivity. discriminate H0. Qed.

Compute aeval t1.
