(*
Kaposi Ambrus, akaposi@inf.elte.hu
Előadó: Horpácsi Dániel

Coq, programozási nyelv függő típusok, bizonyításokat is lehet benne írni
coqide

minden gyakorlatra HF (nem kötelező)
minden gyakorlat elején lesz kiszh

12 db kiszh Canvasban, és még lesz egy beadandó, 4 pontot ér
valószínű ponthatárok:
0-6 : 1
7-8 : 2
9-11 : 3
12-13 : 4
14-16 : 5

tárgynyelv = WHILE nyelv Nilsson: Concrete semantics
 metanyelv = magyar, matetika = Coq (típuselmélet, Agda)
                                - programozási nyelv
                                - taktikták

Coq bevezető, egyszerű kifejezésnyelv, változók, parancsok, while
- szemantika: kis lépéses, nagy lépéses operációs szemantika, denotáció szemantika

int f(int x) { return (2*x+1) }; print(f(4));

           f
          /  \
       int x  return
                 |
                 +
                / \
                *  "hello"
               / \
              2   x
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
  | monday  => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Compute next_weekday (next_weekday wednesday).

(*
next_weekday (next_weekday wednesday) =
next_weekday (match wednesday with
  | monday  => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end) =
next_weekday (thursday) =
match thursday with
  | monday  => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end =
friday

*)

Theorem test_next_weekday :
  (next_weekday (next_weekday saturday)) =
    monday.
(* taktikak: *)
simpl.
reflexivity.
Qed.

Lemma next7 (d : day) :
   next_weekday (next_weekday (next_weekday (
   next_weekday (next_weekday (next_weekday (
                                   next_weekday d)))))) = d.
Proof.
simpl.
destruct d.
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
  simpl. reflexivity.
Qed.

Lemma orb_test1 (a : bool) : orb true a = true.
simpl. reflexivity. Qed.
  
Lemma orb_test2 (a : bool) : orb a true = true.
  simpl. destruct a.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma orb_comm (a b : bool) : orb a b = orb b a.
destruct a eqn:H.
destruct b. reflexivity. reflexivity.
destruct b. reflexivity. reflexivity.
Qed.

  
(* Lemma orb_comm' (a b : bool) : orb a b = orb b a. *)

(*
Inductive, Definition, match, Theorem, Lemma, Proof, Qed,
simpl, unfold, reflexivity, destruct
*)


(* HF 
andb
notb (andb a b) = orb (notb a) (notb b)
notb (orb a b) = andb (notb a) (notb b)
*)

(* nehez! *)
Lemma nehez (f : bool -> bool)(x : bool) : f (f (f x)) = f x.
destruct (f true) eqn:Htrue.
destruct (f false) eqn:Hfalse.
destruct x. rewrite Htrue. rewrite Htrue. rewrite Htrue. reflexivity. rewrite Hfalse. rewrite Htrue. rewrite Htrue. reflexivity.
destruct x; try (rewrite Htrue); try (rewrite Hfalse); try (rewrite Htrue); try (rewrite Hfalse);try (rewrite Htrue); try (rewrite Hfalse); reflexivity.
destruct (f false) eqn:Hfalse.
destruct x; try (rewrite Htrue); try (rewrite Hfalse); try (rewrite Htrue); try (rewrite Hfalse);try (rewrite Htrue); try (rewrite Hfalse); reflexivity.
destruct x; try (rewrite Htrue); try (rewrite Hfalse); try (rewrite Htrue); try (rewrite Hfalse);try (rewrite Htrue); try (rewrite Hfalse); reflexivity.
Qed.

(*
Definition orb (a b : bool) : bool := 
Definition orb : bool -> bool -> bool :=
  fun a => fun b => match ...
*)
