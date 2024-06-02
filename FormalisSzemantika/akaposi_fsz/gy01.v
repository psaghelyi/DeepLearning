(*
Formális szemantika gyakorlat
gyakvez: Kaposi Ambrus, akaposi@inf.elte.hu
eloado: Horpacsi Daniel

gyakorlat anyaga: honlapomon
https://people.inf.elte.hu/akaposi/fsz

17.45-kor kezdunk, tegezodunk
sok onallo munka, lehet barmikor kerdezni

szamonkeres:
 - minden gyak utan HF (Coq-ban) Canvas rendszer, nincs szamonkerve
 - minden gyak elejen kiszh (0-1 pontert) 10 perc Canvasban
   ha 0 pontos, akkor is kuldd be
 - beadando felev kozepen, 4 pont, nem kotelezo
gyakorlati jegy (ELOZETES):
0-6 : 1; 7-8 : 2; 9-11 : 3; 12-13 : 4; 14-16 : 5

C:\\"Coq platform"\\bin\coqide.exe

Coq: programozasi nyelv / bizonyito rendszer (proof assistant)
Lean (Kevin Buzzard), Agda, Idris

programozok: bizonyitottan helyes programozas

add : Int -> (Int -> Int) -- "curry"-zve
add x y | x == 1438965986752983 && y == 348735827238735 = 0
        | otherwise = x + y
-- add : (Int, Int) -> Int
add 2 : Int -> Int

Chrome (BoringSSL), Firefox, Linux kernel
Smart Contract

C-nek CompCert bizonyitottan helyes forditoprogram
ML-nek is van ilyen biz.helyes forditoja
Java-nak is van egy kis resznyelve

formalis szemantika
- WHILE nyelv, ennek tobbfele modon megadjuk a szemantikajat
nyelv = szintaxis + szemantika
(nyelvek tipusrendszere: tobbfele nyelv)

Coq = funckionalis programozasi nyelv
  - mint Haskell, Clean, Erlang, (Java, C#, Python)
    f :: Int -> Int
    ez lehet, hogy nem ad vegerdemnyt
  - nagyon tiszta, fuggo tipusok
    ^ nincs vegtelen ciklus, nincs kivetel
      - Alan Kay's STEPS project, Viewpoint Research Institute
  - unit :: (n : Int) -> Matrix(n,n)
    (n : Nat) -> (n + 1) = (1 + n)


    weekday, nextday, bool, or, neg, or_left_id, or_right_id, or_comm

    Definition, match, Example, Inductive, Proof, Qed, Compute, Check

    (intro) destruct, simpl, reflexivity, <goal focus */->, ;
*)


Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
(* data Day = Monday | Tuesday | ... *)

Definition aday : day := thursday.

Eval compute in aday.

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

(* eletem elso Coq tetele *)
Theorem test_next_weekday :
  (next_weekday (next_weekday saturday)) =
    monday.
Proof.
  (* taktikakat irunk: intro, destruct, simpl, reflexivity *)
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
Definition orb (a : bool)(b : bool) : bool := match a with
 | true => true
 | _    => b
 end.

Lemma orb_test : orb true false = true.
Proof. simpl. reflexivity. Qed.
(* orb true false =  
match true with
 | true => true
 | _    => false
 end              = true
*)

Lemma orb_test1 (a : bool) : orb true a = true.
Proof. simpl. reflexivity. Qed.

Lemma orb_test2 (a : bool) : orb a true = true.
Proof. simpl. destruct a.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma orb_comm (a b : bool) : orb a b = orb b a.
Proof.
destruct a, b.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.  

Lemma orb_comm' (a b : bool) : orb a b = orb b a.
Proof.
destruct a, b; simpl; reflexivity. Qed.
(*
Inductive, Definition, match, Theorem, Lemma, Proof, Qed,
simpl, unfold, reflexivity, destruct
*)


Definition andb (a : bool)(b : bool) : bool := match a with
 | true => b
 | _    => false
 end.

Definition notb (a : bool) : bool := match a with
 | true => false
 | _    => true
 end.

Lemma L1 (a b : bool) : notb (andb a b) = orb (notb a) (notb b).
Proof.
destruct a, b; simpl; reflexivity.
Qed.

Lemma L2 (a b : bool) : notb (orb a b) = andb (notb a) (notb b).
Proof.
destruct a, b; simpl; reflexivity.
Qed.

(* HF 
andb
notb (andb a b) = orb (notb a) (notb b)
notb (orb a b) = andb (notb a) (notb b)
*)

(* nehez! *)
Lemma L3 (f : bool -> bool)(x : bool) : f (f (f x)) = f x.
Proof.
destruct (f x) eqn:H1.
- destruct (f true) eqn:H2.
  + rewrite H2. reflexivity.
  + destruct (f false) eqn:H3.
    * reflexivity.
    * destruct x.
      -- rewrite <- H1. rewrite <- H2. reflexivity.
      -- rewrite <- H1. rewrite H3. reflexivity.
- destruct (f false) eqn:H2.
  + destruct (f true) eqn:H3.
    * destruct x.
      -- rewrite <- H1. rewrite H3. reflexivity.
      -- rewrite <- H2. apply H1.
    * reflexivity.
  + apply H2.
Qed.
    


Lemma bool3 (f : bool -> bool)(x : bool) : f (f (f x)) = f x.
Proof.
  destruct (f true) eqn:Htrue; 
  destruct (f false) eqn:Hfalse; 
  destruct x;
  try ( rewrite Htrue  );
  try ( rewrite Hfalse );
  try ( rewrite Htrue  );
  try ( rewrite Hfalse );
  try ( rewrite Htrue  );
  try ( rewrite Hfalse );
  try ( rewrite Htrue  );
  try ( rewrite Hfalse );
  reflexivity.
Qed.


(* rewrite, destruct eqn *)

(*
Definition orb (a b : bool) : bool := 
Definition orb : bool -> bool -> bool :=
  fun a => fun b => match ...
*)
