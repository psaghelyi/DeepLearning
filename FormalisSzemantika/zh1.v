(* BEGIN FIX *)
(** Pótold a hiányzó kódrészleteket! A BEGIN FIX és END FIX közötti részeket ne módosítsd! Akkor jó a megoldásod, ha a Coq elfogadja az egészet (zöld lesz a teljes fájl).*)
Inductive bool : Type :=
| true
| false.

(* Add meg a logikai "nem" műveletet! *)
Definition not (a : bool) : bool := 
  match a with
  | true => false
  | false => true
  end.
(* END FIX *)

(* BEGIN FIX *)
Lemma notnotnottrue : not (not (not true)) = not true.
Proof.
  simpl.
  reflexivity.
Qed.
(* END FIX *)


(* BEGIN FIX *)
Lemma notnotnot (b : bool) : not (not (not b)) = not b.
Proof.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
(* END FIX *)
