(*
Formális szemantika gyakorlat, 3-as
  csoport
előadás oktatója: Horpácsi Dániel
gyakorlat: Bereczky Péter
(Kaposi Ambrus honlapomon: 
   - Formális szemantika, letölteni:
     gy01_pre.v fájlt letölteni és
     coqide nevű programban megnyitni) 
C:\\Coq Platform\\bin\\coqide

COQ nevű nyelvet telepíteni

gyakorlat:
 - minden gyak után van HF, amit nem kötelező megcsinálni
 - minden gyak elején van kiszh, 0-1 pont, Canvas, Coq feladat, jelenlét ellenőrzés
 - beadandó, 0-4 pont között, félév közepén, Canvas
ponthatárok:
0-6 : 1, 7-8 : 2, 9-11 : 3, 12-13 : 4, 14-16 : 5

bevezető szöveg a tematikáról
WHILE nyelv: egyszerű imperatív nyelv, változók (Int,Bool),
  true,false,ifthenelse,+,-,*,>,=, while ciklus
szintaxis: programok, fák

int f(int x) { return (x + 2 * x)}

           function
       /    \        \ 
    int  paramlista   return
                         |
                         +
                        / \
                        x  *
                          / \
                         2   x


szemantika: hogyan fut a program, a program végeredménye
  - operációs szemantika (kis,nagy), denotációs szemantika
1. egyszerű kifejezésnyelv, mindegyik szemantika
2. kifejezésnyelv változókkal, mindegyik szemantika
3. WHILE nyelv, mindegyik szemantika
Fóthizmus = WHILE nyelv denotációs szemantikája

bevezető szöveg a Coq-ról:
- funkcionális programozási nyelv (mint Haskell, ML, Clean, OCaml, (Scheme, Lisp))
- nagyon erős típusrendszer (függő típusok) nxn-es mátrixok típusa, ahol n futási idejű érték
     map<A,B> : (A -> B) -> (Vector<A> -> Vector<B>)
     Matrix<A,n,f(n)>
- függő típusos nyelvek: Coq, Agda, Lean (Kevin Buzzard), Idris
  - Agda: típuselmélet, nyelvek típusrendszere
- nem csak programozni lehet precíz típusokkal, 
  tetszőleges matematikai állítás is kifejezhető típusokkal,
  bizonyítás ellenőrző rendszerek (proof assistant)

    weekday, nextday, bool, or, neg, or_left_id, or_right_id, or_comm

    Definition, match, Example, Inductive, Proof, Qed, Compute, Check

    intro, destruct, simpl, reflexivity, <goal focus */->
*)


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
(*
next_weekday (next_weekday wednesday) =
next_weekday (match wednesday with
  | monday  => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end) =
next_weekday thursday =
match thursday with
  | monday  => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end =
friday
*)

Theorem test_next_weekday :
  (next_weekday (next_weekday saturday)) =
    monday.
Proof. (* taktikakat irunk *)
simpl. reflexivity.
Qed.

Lemma next7 (d : day) :
   next_weekday (next_weekday (next_weekday (
   next_weekday (next_weekday (next_weekday (
   next_weekday d)))))) = d.
Proof.
destruct d; reflexivity.
Qed.


Inductive bool : Type :=
  | true
  | false.

(* orb
   notb
   orb true false = true
   (a : bool) : orb true a = true
 *)
Definition orb (a : bool)(b : bool) : bool :=
  match a with | true => true | _ => b end.
(*
Lemma orb_test : orb true false = true.

Lemma orb_test1 (a : bool) : orb true a = true.

Lemma orb_test2 (a : bool) : orb a true = true.
*)
Lemma orb_comm (a b : bool) : orb a b = orb b a.
destruct a.
- destruct b. (* a = true *)
  + simpl. reflexivity. (* b = true *)
  + simpl. reflexivity. (* b = false *)
- destruct b. (* a = false *)
  + simpl. reflexivity. (* b = true *)
  + simpl. reflexivity. (* b = false *)
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

(* nehez! *)
Lemma nehez (f : bool -> bool)(x : bool) : 
  f (f (f x)) = f x.
Proof.
destruct x.
* destruct (f true) eqn:H. 
** repeat (rewrite H).  reflexivity.

(*
ma volt: simpl, reflexivity, destruct (eqn:H), rewrite
****, ;, repeat
*)


(*
Definition orb (a b : bool) : bool := 
Definition orb : bool -> bool -> bool :=
  fun a => fun b => match ...
*)
