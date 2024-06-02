(*
Kaposi Ambrus
docens, Prog.Nyelvek és Ford.Programok Tanszék
akaposi@inf.elte.hu

gyakorlatot Bereczky Péter veszi majd át

szervezés:
 * tegeződünk
 * felvesszük az órákat, légyszi figyelmeztessetek! és 
   valaki töltse föl!
 * 17.45--19.15 pontosan
 * kérdezzetek! nem kell kezet feltenni, be lehet kiabálni
 * ajánlott a videót bekapcsolni
 * jelenlét ellenőrzés lesz a bead-dal
 * chat-ben is lehet kérdezni
 * órán kívül is lehet kérdezni, Szemantika Teams-ben kérdezzetek, ne emailben!
 * gyakorlati anyag: https://people.inf.elte.hu/akaposi/fsz/ gy01pre.v

rendszerkövetelmény:
* Coq ( https://coq.inria.fr ) 
  (online is van, pl. https://x80.org/rhino-coq )
* bead szerveren:
  The Coq Proof Assistant, version 8.9.0 (February 2019)
  compiled on Feb 6 2019 17:43:20 with OCaml 4.05.0

követelmény:
* minden gyakorlatra házi feladat, bead-ban, autom.teszt, nem számít be
* kiszh minden gyakorlat első 10 percében, autom.teszt, hasonlít a házira
  0/1 pontot lehet rá kapni, max 12-t lehet vele összehozni
* Coq beadandó, tavaszi szünetben, meg kell lennie, +2 pontot is lehet gyűjteni
* kettes 5 ponttól,  nagyjából: "5 2, 6-7 3, 8-9 4, 10-14 5"


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


Coq: programozási nyelv, matematikai bizonyításokra
  funkcionális nyelv (mint a Haskell)
  bizonyítások

program    : típus           13 : Int     (fun x => x + 3) : Int -> Int   típusellenőrzés
bizonyítás : állítások       t  : A -> B          (x = 3) : Type          bizonyításellenőrző

  függő típusokkal rendelkező nyelv (_=3) : Int -> Type  5 = 3 : Type, 
Coq: BoringSSL, CompCert

lambda kalkulus          Lisp
System F                 Haskell, Java
Martin-Löf type theory   Coq, Agda, Idris, Lean (Kevin Buzzard)
60-as években: De Bruijn Automath
alternatív számítógépes bizonyító rendszerek: Mizar (ZFC), Isabelle/HOL (System F), B method
bizonyításellenerző <-> automata tételbizonyító (SAT solver, Z3)
*)

(* enum tipusok: data Weekday = Monday | Tuesday | Wednesday | ...
  enum { Tuesday, Wednesday, ... } Weekday;
  *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition szombat : day := saturday.

Definition next (a : day) : day :=
  match a with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Compute next (next (next friday)).
(*
next (next (next friday)) =
next (next (match friday with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end)) =
next (next saturday) =
next (match saturday with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end) =
next sunday =
match sunday with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end =
monday
*)

Theorem test_next : next (next tuesday) = thursday.
Proof.
simpl.
reflexivity.
Qed.

Inductive bool := | true | false.

Definition orb (a b : bool) : bool :=
  match a with
  | true => true
  | false => b
  end.

Compute orb false false.

Theorem test_orb : orb false true = true.
Proof.
simpl. reflexivity.
Qed.

Theorem leftid (a : bool) : orb false a = a.
Proof.
simpl. reflexivity.
Qed.

Theorem rightid (a : bool) : orb a false = a.
Proof.
simpl. (*unfold orb.*)
destruct a.
* simpl. reflexivity.
* simpl. reflexivity.
Qed.

Theorem comm (a b : bool) : orb a b = orb b a.
Proof.
destruct a.
* simpl. destruct b.
** simpl. reflexivity.
** simpl.
   reflexivity.
* simpl.
  Check (rightid b).
  symmetry.
  exact (rightid b).
Qed.

Theorem comm1 (a b : bool) : orb a b = orb b a.
Proof.
destruct a,b; simpl; reflexivity.
Qed.

Lemma nehez (f : bool -> bool)(x : bool) : f (f (f x)) = f x.


(* Thierry Coquand *)

(* simpl, reflexivity, unfold, destruct, symmetry, exact *)

