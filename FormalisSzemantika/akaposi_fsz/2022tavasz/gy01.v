(*
Kaposi Ambrus, docens, Programozási Nyelvek és Fordítóprogramok Tanszék

17:45--19:15, egyelőre online, órarendben labor

tegeződünk.

ez interaktív gyakorlat. bármikor lehet szólni, nem kell engedélyt kérni, bekapcsolod a mikrofont, és beszélsz. lehet chatben is kérdezni, figyelni fogom. lesznek olyan részek, amikor én csak várok rátok, és ti dolgoztok.

követelmények: gyakorlati jegy, ez kell az előadás vizsgára menéshez
- minden óra után HF (Canvasban), nem kötelező megcsinálni
- minden óra elején mikrozh (Canvasban), Coq programozási nyelven program írása
- nincs automata tesztelés, de mindenki könnyen ellenőrizni tudja, hogy jó-e
nagyjából: 10 db, 0/1 pontot lehet kapni, a ketteshez 5 pont kell. 12 pontot is el lehet érni, de 5-től lesz kettes

ti is elindíthatjátok a felvételt.

technikai rész: Coq nevű programozási nyelv, coqide nevű programot használni <- fejlesztőkörnyezet a Coq-hoz

hasonló rendszert használunk: típuselmélet,Agda,nyelvek típusrendszere

Coq,Agda,Lean,Idris ezek egyszerre programozási nyelvek és számítógépes bizonyítórendszerek. ha típushelyes a program (elfogadja a fordító), akkor ha a program egy bizonyítás volt, akkor tudjuk, hogy a helyes a bizonyítás. típusellenőrzés = bizonyításellenőrzés.

ℕ→ℕ→ℕ     (∀a,b:ℕ,∃x:ℕ. c|a ∧ c|b ∧ (∀d:ℕ.(d|a) ∧ (d|b) → d|c))
típus     állítás
program   bizonyítás
          biz : (∀a,b:ℕ,∃x:ℕ. c|a ∧ c|b ∧ (∀d:ℕ.(d|a) ∧ (d|b) → d|c))

biz(145,732)=

függő típusok: _++_ : List Int → List Int → List Int
               Vec Int n az egy típus minden n integerre
               _++_ : Vec Int n → Vec Int m → Vec Int (n+m)
               xs ++ []     := xs
               xs ++ (y:ys) := 
               n+m hosszu listat varok, de egy n hosszu listat kaptam
               xs : Vec Int n      m=0    kell : Vec Int (n+0)
                                                         =n
               [] ++ ys = ys
               (x:xs) ++ ys = x : (xs ++ ys)

Coq: Google Chrome, sok ezer oldalas matematikai bizonyítások: négyszíntétel
  - külön van a bizonyításoknak egy ún. taktika (tactic), külön van a programoknak a nyelve (hasonlít az OCaml nyelv szintaxisához)
  - francia
Agda: típuselmélet kutatóknak való, több szolgáltatása van, egyszerűbb
  - egyben van a bizonyítás és a programok nyelve, Haskellhez nagyon hasonlít
  - svéd
Idris: skót, programozásra van fejlesztve, kicsit kezdetleges
  Haskellhez függő típusokat fognak adni
Lean: amerikaiak csinálják, de London (UCL) Kevin Buzzard matematikus
  mathlib, egész BSc-s matematika formalizálva van
  (klasszikus módon, kizárt harmadik elve: A ∨ ¬A)


ctrl-lefele, ctrl-felfele gombok

Haskellben ::, Coq-ban :
3 :: Int       3 : Int
*)

(* felsorolas *)

Inductive day : Type :=
  | monday (* konstruktor *)
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday. (* vegen pont *)

(* aday az egy program (rovidites), a tipusa day, es az erteke thursday *)
Definition aday : day := thursday.

(* programok vegrehajtasa *)
Compute aday.

(* 8.14.1-es verzio. *)

(* next_weekday : day -> day *)
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
Compute next_weekday (next_weekday sunday).

Theorem test_next_weekday :
  (next_weekday (next_weekday saturday)) =
    monday.
Proof.
  (* ide mar nem programot irunk, hanem bizonyitast, un. tactic-okkal*)
  simpl.
(*
next_weekday (next_weekday saturday) =
next_weekday (match saturday with
  | monday  => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end) = 
next_weekday sunday = 
match sunday with
  | monday  => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end = 
monday
*)
  reflexivity.
Qed.


Lemma next7 (d : day) :
   next_weekday (next_weekday (next_weekday (
   next_weekday (next_weekday (next_weekday (
   next_weekday d)))))) = d.
destruct d; simpl; reflexivity.
Qed.


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
 | false => match b with
   | true => true
   | false => false
   end
end.

Definition orb' (a : bool)(b : bool) : bool := match a with
 | true => true
 | false => b
end.

Lemma orb_test : orb true false = true.
Proof. simpl. reflexivity. Qed.

Lemma orb_test1 (a : bool) : orb true a = true.
Proof. simpl. reflexivity. Qed.

Lemma orb_test2 (a : bool) : orb a true = true.
Proof. simpl. unfold orb.
(* (match a with | true => true | false => true end) = true *)
  destruct a.
  - reflexivity.
  - reflexivity.
Qed.

Lemma orb'_test2 (a : bool) : orb' a true = true.
Proof. simpl. unfold orb'. destruct a. reflexivity. reflexivity. Qed.

Lemma orb_comm (a b : bool) : orb' a b = orb' b a.
Proof. simpl. destruct a.
- (* true = orb' b true *) simpl. destruct b.
-- simpl. reflexivity.
-- simpl. reflexivity.
- (* b = orb' b false *) simpl. destruct b.
-- simpl. reflexivity.
-- simpl. reflexivity.
Qed.

(*
Lemma orb_comm' (a b : bool) : orb a b = orb b a.
Proof. destruct a.
 - (* true = orb' b true *) simpl. (* hogy tudjuk ezt orb_test2-vel bizonyitani? *)
*)

Lemma orb_comm'' (a b : bool) : orb a b = orb b a.
Proof. destruct a,b.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma orb_comm''' (a b : bool) : orb a b = orb b a.
Proof. unfold orb. destruct a,b;  simpl; reflexivity. Qed.

(*
Lemma orb_comm'''' (a b : bool) : orb a b = orb b a.
unfold orb at 1.
*)

(*
Inductive, Definition, match, Theorem, Lemma, Proof, Qed,
simpl, unfold (at 1, at 2), reflexivity, destruct
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