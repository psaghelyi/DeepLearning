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

Theorem test_next_weekday :
  (next_weekday (next_weekday saturday)) =
    monday.
Proof.
  simpl.
  reflexivity.
Qed.

(*
HF:
Lemma next7 (d : day) :
   next_weekday (next_weekday (next_weekday (
   next_weekday (next_weekday (next_weekday (
   next_weekday d)))))) = d.
*)

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
reflexivity. Qed.

Lemma orb_test1 (a : bool) : orb true a = true.
simpl. reflexivity. Qed.

Lemma orb_test2 (a : bool) : orb a true = true.
Proof.
  simpl. destruct a.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Lemma orb_comm (a b : bool) : orb a b = orb b a.
destruct a.
- destruct b.
  + reflexivity.
  + reflexivity.
- destruct b.
  + reflexivity.
  + reflexivity.
Qed.

Lemma orb_comm' (a b : bool) : orb a b = orb b a.
(* destruct a eqn:H. *)

destruct a; destruct b; reflexivity.
Qed.

(*
Inductive, Definition, match, Theorem, Lemma, Proof, Qed,
simpl, unfold, reflexivity, destruct
*)


(* HF 
andb
notb (andb a b) = orb (notb a) (notb b)
notb (orb a b) = andb (notb a) (notb b)
*)

Lemma nehez (f : bool -> bool)(x : bool) : f (f (f x)) = f x.
destruct x.
destruct (f true) eqn:H.
rewrite -> H. rewrite -> H.

(*
Definition orb (a b : bool) : bool := 
Definition orb : bool -> bool -> bool :=
  fun a => fun b => match ...
*)
