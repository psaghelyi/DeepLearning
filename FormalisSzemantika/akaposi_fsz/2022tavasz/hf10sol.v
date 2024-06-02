(* BEGIN FIX *)
From Coq Require Import Strings.String
                        Arith.PeanoNat
                        Arith.Plus
                        Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Definition X:string := "X"%string.
Definition Y:string := "Y"%string.
Definition Z:string := "Z"%string.

Definition state := string -> nat.

Definition empty : state := fun x => 0.

Definition update (s : state) (x : string) (n : nat) : state :=
  fun x' =>
    match string_dec x x' with
    | left _ => n
    | right _ => s x'
    end.

Definition aState : state := 
fun x =>
  match x with
  | "X"%string => 1
  | "Y"%string => 2
  | "Z"%string => 42
  | _ => 0
  end
.

Inductive AExp : Type :=
| ALit (n : nat)
| AVar (x : string)
| APlus (a1 a2 : AExp)
| AMinus (a1 a2 : AExp)
| AMult (a1 a2 : AExp).

Inductive BExp : Type :=
(* true, false, and, not, eq, le *)
| BTrue
| BFalse
| BAnd (b1 b2 : BExp)  (* true and false *)
| BNot (b : BExp)      (* not true *)
| BEq (a1 a2 : AExp)   (* 1 == 2 *)
| BLe (a1 a2 : AExp)   (* 1 <= 2 *)
.

Definition true_and_false : BExp := BAnd BTrue BFalse.

Fixpoint aeval (a : AExp) (st : state) : nat :=
match a with
| ALit n => n
| AVar x => st x
| APlus a1 a2 => (aeval a1 st) + (aeval a2 st)
| AMinus a1 a2 => (aeval a1 st) - (aeval a2 st)
| AMult a1 a2 => (aeval a1 st) * (aeval a2 st)
end.

Fixpoint beval (b : BExp) (s : state) : bool :=
(* Ha szeretnenk elagazast/ciklust, kell a logikai kifejezesek denot. szemantikaja *)
match b with
| BTrue => true
| BFalse => false
| BAnd b1 b2 => (* andb *) (beval b1 s) && (beval b2 s)
| BNot b => negb (beval b s)
| BEq a1 a2 => (* Nat.eqb *) (aeval a1 s) =? (aeval a2 s)
| BLe a1 a2 => (* Nat.leb *) (aeval a1 s) <=? (aeval a2 s)
end.

Inductive Stmt : Type :=
| SSkip (* skip *)
| SAssign (x : string) (a : AExp) (* x := a *)
| SSeq (S1 S2 : Stmt) (* S1; S2 *)
| SIf (b : BExp) (S1 S2 : Stmt) (* if b then S1 else S2 *)
| SWhile (b : BExp) (S0 : Stmt) (* while b do S0 *).

(*
  while b do S ≡ if b then S; while b do S else skip
*)

(** kompozicionalitas!! *)
Fixpoint eval (fuel : nat) (S0 : Stmt) (st : state) : state :=
match fuel with
| 0 => st
| S fuel' =>
  match S0 with
  | SSkip => st
  | SAssign x a => update st x (aeval a st)
  | SSeq S1 S2 => eval fuel' S2 (eval fuel' S1 st)
  | SIf b S1 S2 => if beval b st
                   then eval fuel' S1 st
                   else eval fuel' S2 st
  | SWhile b S0 => if beval b st
                   then eval fuel' (SWhile b S0) (eval fuel' S0 st)
                   else st
  end
end.

(* Adj meg olyan programokat, amelyekre teljesulnek a kovetkezo kiertekelesek! *)

(* Tipp: stmt1 mukodjon ugy, mint egy felteteles ertekadas:
   - ha az elso parameter kisebb, adja ertekul X-nek
   - ha a masodik parameter kisebb, adja ertekul Y-nak
*)
(* END FIX *)
Definition stmt1 (n m : nat) : Stmt :=
  SIf (BLe (ALit n) (ALit m)) (SAssign X (ALit n)) (SAssign Y (ALit m)).

(* BEGIN FIX *)
Goal eval 1000 (stmt1 10 15) empty X = 10. Proof. reflexivity. Qed.
Goal eval 1000 (stmt1 10 15) empty Y = 0. Proof. reflexivity. Qed.
Goal eval 1000 (stmt1 10 15) aState X = 10. Proof. reflexivity. Qed.
Goal eval 1000 (stmt1 10 15) aState Y = 2. Proof. reflexivity. Qed.
Goal eval 1000 (stmt1 15 4) empty X = 0. Proof. reflexivity. Qed.
Goal eval 1000 (stmt1 15 4) empty Y = 4. Proof. reflexivity. Qed.
Goal eval 1000 (stmt1 15 4) aState X = 1. Proof. reflexivity. Qed.
Goal eval 1000 (stmt1 15 4) aState Y = 4. Proof. reflexivity. Qed.

(*
  Add meg a szamlalo ciklust szintaktikus cukorkakent!
  0-tol n-ig szamoljon el a v valtozoval, es S0 legyen a ciklusmag
  (ezek mind parameterek, lasd lejjebb)
*)
(* END FIX *)
Definition stmt2 (n : nat) (v : string) (S0 : Stmt) : Stmt := 
  SSeq (SAssign v (ALit 0)) (SWhile (BLe (AVar v) (ALit n)) (SSeq S0 (SAssign v (APlus (AVar v) (ALit 1))))).

(* BEGIN FIX *)
Goal eval 1000 (stmt2 10 X SSkip) empty X = 11. Proof. reflexivity. Qed.
Goal eval 1000 (stmt2 10 X (SAssign Y (APlus (AVar Y) (AVar X)))) empty Y = 55.
Proof. reflexivity. Qed.
Goal eval 1000 ((SSeq (SAssign Y (ALit 1)) 
                      (stmt2 10 X (SAssign Y (AMult (AVar Y) (AVar X)))))) empty Y = 0.
Proof. reflexivity. Qed.
Goal eval 1000 (SSeq (SAssign Y (ALit 1)) 
                     (stmt2 6 X (SIf (BEq (AVar X) (ALit 0))
                                SSkip
                                (SAssign Y (AMult (AVar Y) (AVar X)))))) empty Y = 720.
Proof. reflexivity. Qed.


(* Add meg azt a programot, amely a parameter `n`-tol kezdve osszegzi a szamokat 0-ig! *)
(* END FIX *)
Definition stmt3 (n : nat) : Stmt :=
(*
  X := n;
  Y := 0;
  while X > 0 do
    Y := Y + X;
    X := X - 1
  end
*)
  SSeq (
    SAssign X (ALit n)) (SSeq (
    SAssign Y (ALit 0)) (
    SWhile (BLe (ALit 1) (AVar X)) (SSeq (
      SAssign Y (APlus (AVar Y) (AVar X))) (
      SAssign X (AMinus (AVar X) (ALit 1)))
    ))).

(* BEGIN FIX *)
Goal eval 16 (stmt3 5) empty X = 0. Proof. simpl. reflexivity. Qed.
Goal eval 1000 (stmt3 10) empty Y = 55. Proof. reflexivity. Qed.
Goal eval 1000 (stmt3 1) empty X = 0. Proof. reflexivity. Qed.
Goal eval 1000 (stmt3 1) empty Y = 1. Proof. reflexivity. Qed.

(** Tipp: Kovetkezo tetelhez nem kell indukcio, eleg (egy vagy tobb) esetszetvalasztas
          (valami alapjan) *)
Theorem seq_skip : forall S0 st fuel,
  eval (S fuel) (SSeq S0 SSkip) st = eval fuel S0 st.
Proof.
(* END FIX *)
intros. simpl. destruct fuel.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

(* BEGIN FIX *)
(** Kiegeszito, nehez feladatok:

    A kovetkezo feladatok megmutatjak, hogy hogyan lehet egy "okosabb"
    "functional big-step" szemantikat hasznalni `option` tipus hasznalataval.
    Ennek segitsegevel sokkal tobb dolgot lehet bizonyitani es divergencia kifejezese is
    lehetove valik.

    Erdemes megprobalkozni ezekkel a feladatokkal, mert nagyon tanulsagosak, illetve
    megprobalhatjatok ugyanezeket a teteleket bizonyitani a sime `eval` fuggvennyel.
*)

(*
  option típus ~ Maybe típus: vagy tartalmaz egy értéket, vagy nem. Példák:
    Some 1 : option nat   ~ Just 1 Haskellben
    None : option nat     ~ Nothing Haskellben
    None : option State
    Some empty : option State
*)
Fixpoint option_eval (S0 : Stmt) (st : state) (fuel : nat) : option state :=
match fuel with
| 0 => None
| S fuel' =>
  match S0 with
  | SSkip => Some st
  | SAssign x a => Some (update st x (aeval a st))
  | SSeq S1 S2 => match (option_eval S1 st fuel') with
                  | Some st' => option_eval S2 st' fuel'
                  | None     => None  (** ha a fuel kifogyott, propagaljuk None-t *)
                  end
  | SIf b S1 S2 => if beval b st
                   then option_eval S1 st fuel'
                   else option_eval S2 st fuel'
  | SWhile b S0 => if beval b st
                   then match (option_eval S0 st fuel') with
                        | Some st' => option_eval (SWhile b S0) st' fuel'
                        | None     => None (** ha a fuel kifogyott, propagaljuk None-t *)
                        end
                   else Some st
  end
end.

(*
  while true do skip end
*)
Definition inf_iter : Stmt := SWhile BTrue SSkip.
(*
  while true do X := X + 1 end
*)
Definition inf_iter2 : Stmt := SWhile BTrue (SAssign X (APlus (AVar X) (ALit 1))).
(* END FIX *)
(** divergencia: *)
Theorem inf_iter_div :
  forall fuel st, option_eval inf_iter st fuel = None.
Proof. induction fuel.
- intros. simpl. reflexivity.
- intros. simpl. destruct fuel.
-- reflexivity.
-- simpl. simpl in IHfuel. apply IHfuel.
Qed.

Theorem inf_iter2_div :
  forall fuel st, option_eval inf_iter2 st fuel = None.
Proof. induction fuel.
- intros. simpl. reflexivity.
- intros. simpl. destruct fuel.
-- reflexivity.
-- simpl. simpl in IHfuel. apply IHfuel.
Qed.

(** Meg nehezebb tetelek: *)

Theorem refuel :
  forall fuel st S0 result, option_eval S0 st fuel = Some result
->
  option_eval S0 st (S fuel) = Some result. (** Ez annyit mond, hogy a fuel novelheto *)
Proof.
  induction fuel.
Admitted.

(**
  Tipp: szinten probald meg esetszetvalasztassal
*)
Theorem seq_assoc : (** Szekvencia kiertekelesekor nem szamit a zarojelezes *)
  forall fuel st S1 S2 S3 result,
    option_eval (SSeq S1 (SSeq S2 S3)) st fuel = Some result ->
    exists fuel', option_eval (SSeq (SSeq S1 S2) S3) st fuel' = Some result.
Proof.

Admitted.