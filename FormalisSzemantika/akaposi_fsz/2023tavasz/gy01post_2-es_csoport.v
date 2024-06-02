(*
Kaposi Ambrus honlap
https://people.inf.elte.hu/akaposi/
             fsz/gy01pre.v


számonkérés:
 - minden gyak után HF (Coq-ban), nincs számonkérve
 - minden gyak elején kiszh (0-1 pontért) 10 perc Canvasban
   ha 0 pontos, akkor is küldd be
 - beadandó félév közepén, 4 pont, nem kötelező
gyakorlati jegy:
0-6 : 1; 7-8 : 2; 9-11 : 3; 12-13 : 4; 14-16 : 5

C:\\"Coq platform"\\bin\coqide.exe

WHILE nyelv definicioja/szintaxisa, szemantikája(operációs(kis/nagy lépéses), denotációs)
kapcsolódik: fordítóprogramok, formális nyelvek, logika(Coq), diszkrét matek; nyelvek típusrendszere, típuselmélet

Agda, Coq, Idris, Lean (Kevin Buzzard): Martin-Löf (dependent) type theory
Haskell, ML, OCaml: System F
Java: System F_omega_<:
magasabbrendű logika csak a formulák nyelve: simple type theory
klasszikus ítéletlogika: Boole-algebra
természetes számok és magasabbrendű fgv: Gödel System T
Algol, Turbo Pascal, Ada: PCF
*)

(*
    weekday, nextday, bool, or, neg, or_left_id, or_right_id, or_comm

    Definition, match, Example, Inductive, Proof, Qed, Compute, Check

    intro, destruct, simpl, reflexivity, <goal focus */->
*)


Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition aday : day := thursday.

Compute aday.

Definition next_weekday (a : day) : day :=
  match a with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday
  end.

Compute next_weekday (next_weekday wednesday).

Theorem test_next_weekday :
  (next_weekday (next_weekday saturday)) =
    monday.
Proof. simpl. reflexivity. Qed.

(* next_weekday (next_weekday saturday) =
   next_weekday (match saturday with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday
  end) = next_weekday sunday = 
  match sunday with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday
  end = monday
*)

Lemma next7 (d : day) :
   next_weekday (next_weekday (next_weekday (
   next_weekday (next_weekday (next_weekday (
   next_weekday d)))))) = d.
Proof.
simpl. destruct d.
simpl. reflexivity.
simpl. reflexivity.
simpl. reflexivity.
simpl. reflexivity.
simpl. reflexivity.
simpl. reflexivity.
simpl. reflexivity.
Qed.

Inductive bool : Type :=
  | true
  | false.

(* orb
   notb
   orb true false = true
   (a : bool) : orb true a = true
 *)
Definition orb (a : bool)(b : bool) : bool :=
   match a with
   | true => true
   | false => b
   end.

Lemma orb_test : orb true false = true.
Proof. simpl. reflexivity. Qed.

Lemma orb_test1 (a : bool) : orb true a = true.
Proof. simpl. reflexivity. Qed.

Lemma orb_test2 (a : bool) : orb a true = true.
Proof. destruct a.
* simpl. reflexivity.
* simpl. reflexivity.
Qed.

(*Lemma orb_comm (a b : bool) : orb a b = orb b a.

Lemma orb_comm' (a b : bool) : orb a b = orb b a.


Inductive, Definition, match, Theorem, Lemma, Proof, Qed,
simpl, unfold, reflexivity, destruct
*)


(* HF 
andb
notb (andb a b) = orb (notb a) (notb b)
notb (orb a b) = andb (notb a) (notb b)
*)

(* nehez! *)
Lemma nehez (f : bool -> bool)(x : bool) :
   f (f (f x)) = f x.
Proof. destruct x.
* destruct (f true) eqn:H.
(* simpl, reflexivity, destruct (eqn:), rewrite *)
** rewrite H. rewrite H. reflexivity.
** 






















(*
Definition orb (a b : bool) : bool := 
Definition orb : bool -> bool -> bool :=
  fun a => fun b => match ...
*)
