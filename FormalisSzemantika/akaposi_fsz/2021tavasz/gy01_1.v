(*
Formális szemantika 1. gyakorlat (1-es csoport)

Kaposi Ambrus, akaposi@inf.elte.hu
docens, Programozási és Fordítóprogramok Tanszék
bead.inf.elte.hu <- emiatt kell, hogy gyakorlatot válasszatok
első 4 héten én tartom, utána Bereczky Péter

szervezési megjegyzés:
* 7.30-kor pontban kezdünk, szünet nélkül másfél óra
* figyelmeztessetek, hogy legyen felvétel; felvételt töltse valaki fel
* tegeződünk
* NAGYON FONTOS, hogy kérdezzetek gyakorlat közben
* jó, ha a kamera be van kapcsolva
* jelenlét ellenőrzés lesz (implicit módon)
* bead-ban regisztrálni, és FONTOS, hogy egyezzen azzal a gyakorlattal, amire fizikailag jössz
* chat-ben is lehet kérdezni gyakorlat közben
* órán kívül is kérdezzetek a Teams-ben, a gyakorlat chat-jében, ne emailt írjatok!
* https://akaposi.github.io
* https://people.inf.elte.hu/akaposi/fsz/   gy01pre.v

rendszerkövetelmény:
* Coq ( https://coq.inria.fr ) (online is van, pl. https://x80.org/rhino-coq )
* bead szerveren:
  The Coq Proof Assistant, version 8.9.0 (February 2019)
  compiled on Feb 6 2019 17:43:20 with OCaml 4.05.0

számonkérés:
* következő gyakorlatra házi bead-ban (automatikusan tesztelt) (pontot nem ér)
* minden gyakorlat első 10 percében kiszh-t írunk (hasonlít a házira, automata tesztelt)
  0/1 pontot lehet kapni. összeadjuk a pontokat, 50%-ot el kell érni év végére a ketteshez
  prognózis: 12 pontot lehet gyűjteni, 5 ponttól kettes, nagyjából: "5 2, 6-7 3, 8-9 4, 10-12 5"
* Coq beadandó, tavaszi szünetben lesz kiírva, szükséges a gyakorlat teljesítéséhez

Coq: programozási nyelv, bizonyos programok bizonyítások
  bizonyítás : állítás        bizonyításellenőrzés
  program    : típus          típusellenőrzés        (függő típusok, pl. sort : VecInt n -> VecInt n)
propositions as types, Curry-Howard izomorfizmus

Martin-Löf típuselmélet <- elméleti háttere a függő típusos nyelveknek
System F                <-                    Haskell, ML-nek

hasonló nyelv: Coq, Agda, Idris, Lean,                  <- proof assistant, funkcionális
               Isabelle/HOL                             <- System F-re épül
               Mizar                                    <- halmazelméletre épül
               B method                                 <- domain specific proof assistant
               Z3                                       <- automata tételbizonyító

Tematika:
1. Coq bevezető, felsorolási típusok (pl. Bool, Weekday),
   egyszerű műveletek ezekkel a típusokkal, illetve ezen
   műveletek tulajdonságai (pl. egységelem, dupla tagadás, stb.)
2. Természetes számok típusa, összeadás, rekurzió, indukció,
   kongruencia, jobb oldali egységelem, rákövetkező és az
   összeadás kapcsolata, egyéb induktív típusok (pl. bináris fák)
3. Aritmetikai kifejezésnyelv és denotációs szemantika, példa
   kiértékelések
4. Összeadás optimalizálás (0 kiegyszerűsítése)
5. Változók, állapotok, állapot frissítése, zárt kifejezés
   fogalma, zárt kifejezések kiértékelésének állapottól való
   függetlensége
6. Zárt kifejezések leírása logikai függvénnyel ekvivalens a
   predikátummal való megadással, aeval determinizmus
7. A kifejezésnyelv strukturális és természetes operációs
   szemantikája, denotációs szemantikával való ekvivalencia

TAVASZI SZÜNET

9.  Utasítások és denotációs szemantikájuk, példa kiértékelések,
    végtelen ciklus problémája
10. Utasítások big-step szemanitkája, példa kiértékelések
11. Big-step szemantika tulajdonságok (pl. determinisztikusság)
12. Programok ekvivalenciája
13. Haskell export, kivételek, állapot megadása
    adatszerkezettel (pl. listával)
*)

(* data day = monday | tuesday | wednesday | ...
   enum { monday, tuesday, ... } day  *)

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
  | _ => monday
  end.

Compute next_weekday (next_weekday aday).
(*
next_weekday (next_weekday aday) = 
next_weekday (match thursday with
  | monday  => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | _ => monday
  end) = 
next_weekday friday = 
match friday with
  | monday  => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | _ => monday
  end
= saturday
*)

Theorem test_next_weekday :
  (next_weekday (next_weekday saturday)) =
    monday.
Proof.
  simpl.
  reflexivity.
Qed.

(* tactics: simpl, reflexivity, taktika után pontot *)

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
(* Definition orb (a : bool)(b : bool) : bool :=*)
Definition orb (a b : bool) : bool := match a with
  | true => true
  | false => b
  end.

Compute orb true false.

Lemma orb_test : orb true false = true.
Proof.
  simpl.
  reflexivity.
Qed.

(* forall (a : bool), orb true a = true *)
Lemma orb_test1 (a : bool) : orb true a = true.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma orb_test2 (a : bool) : orb a true = true.
Proof.
  unfold orb.
  destruct a.
  * reflexivity.
  * reflexivity.
Qed.

Lemma orb_comm (a b : bool) : orb a b = orb b a.
Proof.
  destruct a.
  * simpl.
    symmetry. 
    exact (orb_test2 b).
  * simpl.
    destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Lemma orb_comm' (a b : bool) : orb a b = orb b a.

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


(* simpl, reflexivity, unfold, destruct, symmetry, exact *)
