(* BEGIN FIX *)
(** Pótold a hiányzó kódrészleteket! A BEGIN FIX és END FIX közötti részeket ne módosítsd! Akkor jó a megoldásod, ha a Coq elfogadja az egészet (zöld lesz a teljes fájl).*)
(** Fill out the missing parts! Do not modify the code between BEGIN FIX and END FIX! *)
Inductive bool : Type :=
| true
| false.

(* Add meg a logikai "és" műveletet! *)
(* Define the logical conjunction *)
Definition andb (a b : bool) : bool :=
    match a with
    | true => b
    | false => false
    end.
(* END FIX *)

(* BEGIN FIX *)
Lemma andb_true_l (b : bool) : andb true b = b.
Proof.
    reflexivity.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma andb_true_r (b : bool) : andb b true = b.
Proof.
    destruct b.
    - reflexivity.
    - reflexivity.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma andb_false_l (b : bool) : andb false b = false.
Proof.
    destruct b.
    - reflexivity.
    - reflexivity.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma andb_false_r (b : bool) : andb b false = false.
Proof.
    destruct b.
    - reflexivity.
    - reflexivity.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma andb_comm (a b : bool) : andb a b = andb b a.
Proof.
    destruct a.
    - destruct b.
        + reflexivity.
        + reflexivity.
    - destruct b.
        + reflexivity.
        + reflexivity.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma nehez (f : bool -> bool)(x : bool) : f (f (f x)) = f x.
Proof.
  destruct x.
  - destruct (f true) eqn:H.
    + rewrite H. rewrite H. reflexivity.
    + destruct (f false) eqn:H'.
      * rewrite H'. rewrite H. reflexivity.
      * rewrite H'. rewrite H'. reflexivity.
  - destruct (f false) eqn:H.
    + destruct (f true) eqn:H'.
      * rewrite H'. rewrite H. reflexivity.
      * rewrite H'. rewrite H'. reflexivity.
    + rewrite H. rewrite H. reflexivity.
Qed.
(* END FIX *)
