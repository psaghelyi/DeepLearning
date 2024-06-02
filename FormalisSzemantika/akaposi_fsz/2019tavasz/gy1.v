Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition aday : day := thursday.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | _ => monday
  end.

Eval compute in next_weekday friday.

Eval compute in (next_weekday (next_weekday friday)).

Example test_next_weekday :
  (next_weekday (next_weekday saturday)) =
    tuesday.
  simpl.
  reflexivity.
Qed.

 Inductive bool : Type :=
  | true
  | false.

 Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


Eval compute in negb (orb true false).

Example test_orb1: (orb true false) = true.
simpl.
reflexivity.
Qed.

Example left_id (b : bool) : orb false b = b.
simpl.
reflexivity.
Qed. 

Example right_id (b : bool) : orb b false = b.
simpl.
intros.
destruct b.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Example borb_comm (b1 b2 : bool) :
  orb b1 b2 = orb b2 b1.
intros b1.
destruct b1.
  (* b1 = true *)
  simpl.
  destruct b2.
    (* b2 = true *)
    simpl.
    reflexivity.
    (* b2 = false *)
    simpl.
    reflexivity.
  (* b1 = false *)
  simpl.
  destruct b2.
    (* b2 = true *)
    simpl.
    reflexivity.
    (* b2 = false *)
    simpl.
    reflexivity.
Qed.
