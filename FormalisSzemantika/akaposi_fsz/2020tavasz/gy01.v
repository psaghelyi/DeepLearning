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
Proof. reflexivity. Qed.

Lemma orb_test1 (a : bool) : orb true a = true.
Proof. simpl. reflexivity. Qed.

Lemma orb_test2 (a : bool) : orb a true = true.
Proof. (*simpl. unfold orb.*) destruct a.
  * reflexivity.
  * reflexivity.
Qed.

Lemma orb_comm (a b : bool) : orb a b = orb b a.
Proof.
  destruct a.
  * destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
  * destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.
Lemma orb_comm' (a b : bool) : orb a b = orb b a.
Proof. destruct a; destruct b; simpl; reflexivity. Qed.

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
Lemma (f : bool -> bool)(x : bool) : f (f (f x)) = f x

(*
Definition orb (a b : bool) : bool := 
Definition orb : bool -> bool -> bool :=
  fun a => fun b => match ...
*)











