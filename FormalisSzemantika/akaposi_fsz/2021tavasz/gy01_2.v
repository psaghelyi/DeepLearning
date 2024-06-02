(*
Formális szemantika, 1. gyakorlata a 2-es csoportnak

Kaposi Ambrus, akaposi@inf.elte.hu
Programozási Nyelvek és Fordítóprogrmaok

szervezési:
 * felvétel (Varga Bence (Felhő) letölti őket)
 * tegeződünk
 * BEAD-ban beadandók, kiszh-k, fontos, hogy ott azt vegyétek fel, amire jártok
 * 4.00-5.30 pontosan
 * kötelező járni, 3 hiányzás, 4 megengedhető (13 gyakorlatból); jelenlét ellenőrzés implicit módon
 * javaslat: kamerát bekapcsolni
 * kérdezzetek! nem kell jelentkezni. cél: mindenki mindent értsen, amit elmondok; chat-ben is kérdezzetek
 * órán kívül kérdések: Teams csatornában
 * óra anyaga: https://people.inf.elte.hu/akaposi/fsz  gy01pre.v, végső fájl: gy01_2.v
                              
rendszerkövetelmények:
 * saját számítógépen Coq https://coq.inria.fr (online is van, pl. https://x80.org/rhino-coq )
 * bead szerveren:
   The Coq Proof Assistant, version 8.9.0 (February 2019)
   compiled on Feb 6 2019 17:43:20 with OCaml 4.05.0

követelmények:
 * házi feladat a következő gyakorlatra (felkészülés)
 * minden óra első 10 percében kiszh, amit 0/1 ponttal értékelünk (beszámít a jegybe)
 * jegy: 12 pont a kiszh-kból max, +2 -t a beadandóból, és 5 ponttól kettes
 * beadandó: elfogadott kell, hogy legyen
 * gyakorlati jegyhez min. 5 pont és elfogadott beadandó
 * nagyjából: "5 2, 6-7 3, 8-9 4, 10-12 5"

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


Coq: programozási nyelv, bizonyítás
  t : A -> B    t programnak a típusa A -> B
                t egy bizonyítás, ami A-ból B-t bizonyítja
60-as évek végén: Curry-Howard izomorfizmus, "propositions as types" "állítás, mint típus"
  program    : típus          típusellenőrzés
  bizonyítás : állítás        bizonyításellenőrzés
legelső ilyen nyelv: De Bruijn holland matematikus: Automath rendszer
 
Coq egy tiszta, teljes funkcionális programozási nyelv (Haskell-hez hasonló);
  lehet bizonyításokat is írni benne
Coq látszólag két nyelv: programozás nyelve (Haskell-szerű), bizonyítások nyelve (taktikák)
  polimorf:                       reverse : ∀ a . List a -> List a
  függő típusokra van szükség.    VecBool : Int -> Tipus
                                  reverse : ∀ n . VecBool n -> VecBool n
  Conor McBride
Haskell      System F (Girard-Reynolds, 80-as évek eleje)
Coq          Type theory (Per Martin-Löf, 70-es években)      BoringSSL, CompCert
      Agda, Idris, Lean (Kevin Buzzard)
      Isabelle/HOL
      Mizar
      B method
*)

(* data Day = Monday | Tuesday | Wednesday | ...
   enum { monday, tuesday, ...} day; *)

Inductive day : Type :=
  | mon
  | tue
  | wed
  | thu
  | fri
  | sat
  | sun.

Definition szombat : day := sat.

Definition next_weekday (a : day) : day :=
  match a with
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  | sun => mon
  end.

(* next_weekday (next_weekday sat) = 
next_weekday (match sat with
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  | sun => mon
  end) = 
next_weekday sun = 
match sun with
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  | sun => mon
  end =
mon
 *)
Compute next_weekday (next_weekday sat).

Theorem test_next_weekday : 
  next_weekday (next_weekday sat) = mon.
Proof.
  simpl.
  reflexivity.
Qed.

Inductive bool : Type := | true | false.

Definition orb (a b : bool) : bool := 
  match a with
  | true => true
  | false => b
  end.

Compute orb false true.

Theorem orb_test : orb false true = true.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem leftid (a : bool) : orb false a = a.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem rightid (a : bool) : orb a false = a.
Proof.
destruct a.
* simpl. reflexivity.
* simpl. reflexivity.
Qed.

Theorem comm : forall (a b : bool), orb a b = orb b a.
Proof.
intros.
destruct a.
* simpl. destruct b.
** simpl. reflexivity.
** simpl. reflexivity.
* simpl. symmetry. exact (rightid b).
Qed.

(* 
orb a false =
match a with
  | true => true
  | false => false
  end
*)

(* simpl, unfold, reflexivity, destruct, intros, symmetry, exact *)
