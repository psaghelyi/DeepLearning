(** Pótold a hiányzó kódrészleteket! A BEGIN FIX és END FIX közötti részeket ne módosítsd! Akkor jó a megoldásod, ha a Coq elfogadja az egészet (zöld lesz a teljes fájl).*)
(** Fill out the missing parts! Do not modify the code between BEGIN FIX and END FIX! *)
(* BEGIN FIX *)
Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).

(*
exTree :=
          +
         /\
        /  \
       -    4
      /\
     /  \
    1    +
        /\
       /  \
      2    3
*)


Definition exTree : AExp := APlus (ASub (ALit 1) (APlus (ALit 2) (ALit 3))) (ALit 4).
(* END FIX *)


(* BEGIN FIX *)
Definition getLeft : AExp -> AExp := fun a => match a with
  | ALit n => ALit n
  | APlus a1 a2 => a1
  | ASub  a1 a2 => a1
  end.
Definition getRight : AExp -> AExp := fun a => match a with
  | ALit n => ALit n
  | APlus a1 a2 => a2
  | ASub  a1 a2 => a2
  end.

Lemma l1 : getLeft (getLeft exTree) = ALit 1. reflexivity. Qed.
Lemma l2 : getLeft (getRight (getLeft exTree)) = ALit 2. reflexivity. Qed.
Lemma l3 : getRight (getRight (getLeft exTree)) = ALit 3. reflexivity. Qed.
Lemma l4 : getRight exTree = ALit 4. reflexivity. Qed.
(* END FIX *)