(* BEGIN FIX *)
(** Pótold a hiányzó kódrészleteket! A BEGIN FIX és END FIX közötti részeket ne módosítsd! Akkor jó a megoldásod, ha a Coq elfogadja az egészet (zöld lesz a teljes fájl).*)
(** Fill out the missing parts! Do not modify the code between BEGIN FIX and END FIX! *)
Inductive bool : Type :=
| true
| false.

(* Add meg a logikai "és" műveletet! *)
(* Define the logical conjunction *)
Definition andb (a b : bool) : bool :=
(* END FIX *)
  match a with | true => b | false => false end.

(* BEGIN FIX *)
Lemma andb_true_l (b : bool) : andb true b = b.
(* END FIX *)
Proof. reflexivity. Qed.

(* BEGIN FIX *)
Lemma andb_true_r (b : bool) : andb b true = b.
(* END FIX *)
Proof. destruct b; reflexivity. Qed.

(* BEGIN FIX *)
Lemma andb_false_l (b : bool) : andb false b = false.
(* END FIX *)
Proof. simpl. reflexivity. Qed.


(* BEGIN FIX *)
Lemma andb_false_r (b : bool) : andb b false = false.
(* END FIX *)
Proof. destruct b; reflexivity. Qed.

(* BEGIN FIX *)
Lemma andb_comm (a b : bool) : andb a b = andb b a.
(* END FIX *)
Proof. destruct a; destruct b; reflexivity. Qed.

(* BEGIN FIX *)
Lemma nehez (f : bool -> bool)(x : bool) : f (f (f x)) = f x.
(* END FIX *)
Proof.
destruct (f true) eqn:H; destruct (f false) eqn:H'; destruct x;
  try (rewrite -> H); 
  try (rewrite -> H'); 
  try (rewrite -> H); 
  try (rewrite -> H'); 
  try (rewrite -> H); 
  try (rewrite -> H'); 
  reflexivity.
Qed.
