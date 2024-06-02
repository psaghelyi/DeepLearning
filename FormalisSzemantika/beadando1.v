(* BEGIN FIX *)
From Coq Require Import Strings.String
                        Arith.PeanoNat
                        Arith.Plus.

Definition X:string := "X"%string.
Definition Y:string := "Y"%string.
Definition Z:string := "Z"%string.

Inductive AExp : Set :=
| ALit (n : nat)
| AVar (s : string)
| APlus (a1 a2 : AExp)
(* END FIX *)
(** 1. feladat: (0.5 pont)
                Egeszitsd ki a kifejezesnyelvet a ternary operatorral 
                (konkret szintaxissal: `a1 ? a2 : a3`)!
                Legyen a konstruktor neve `AIf`!
                A konkret hasznalatra lentebb lathatsz peldakat.

    Task 1: (0.5 points)
                Define the abstract syntax for the ternary operator (`a1 ? a2 : a3`)!
                The name of the corresponding constructor should be `AIf`.
*)
| AIf (a1 a2 a3 : AExp)
.

(* BEGIN FIX *)
Definition ex1 := AIf (ALit 0) (ALit 5) (ALit 4).
Definition ex2 := AIf (AVar X) (ALit 2) (ALit 3).
Definition ex3 := APlus (AIf (ALit 0) (AVar X) (AVar Z)) 
                        (AIf (AVar X) (ALit 0) (ALit 1)).
Definition ex4 := AIf (APlus (AVar Z) (ALit 1)) (ALit 10) (ALit 0).

Definition state := string -> nat.

Definition empty : state := fun x => 0.

Definition aState : state := 
fun x =>
  match x with
  | "X"%string => 1
  | "Y"%string => 2
  | "Z"%string => 42
  | _ => 0
  end
.

Fixpoint aeval (a : AExp) (s : state) : nat :=
match a with
| ALit n => n
| AVar x => s x
| APlus a1 a2 => aeval a1 s + aeval a2 s
(* END FIX *)
(** 2. feladat: (0.5 pont)
                Ertelmezd a denotacios szemantikat a ternary operatorokra,
                ugy hogy az alabbi tesztek lefussanak! A ternary operator
                `a1 ? a2 : a3` ugy mukodik, mint egy kifejezesszintu elagazas,
                azaz eloszor kiertekeli `a1`-et, es ha a vegeredmeny *nem* `0`,
                akkor `a2`-t, egyekent `a3`-t ertekeli ki.
                A megoldas soran csak a szukseges kifejezeseket ertekeld ki! Pl.
                ha `a1` eredmenye `0`, akkor `a2`-t ne ertekelje ki a szemantika!

    Task 2: (0.5 points)
                Define denotational semantics for the ternary operator `a1 ? a2 : a3`
                in the following way: first, evaluate `a1`, if the result is *not*
                `0`, then evaluate `a2`, otherwise evaluate `a3`!
                In your semantics, only evaluate the necessary expressions! For
                example, if the result of `a1` is `0`, then `a2` should *not* be
                evaluated!
*)
| AIf a1 a2 a3 => if aeval a1 s =? 0 then aeval a3 s else aeval a2 s
end.

(* BEGIN FIX *)

Goal forall s, aeval ex1 s = 4. Proof. intro. simpl. reflexivity. Qed.
Goal aeval ex2 aState = 2. Proof. simpl. reflexivity. Qed.
Goal aeval ex2 empty = 3. Proof. simpl. reflexivity. Qed.
Goal aeval ex3 aState = 42. Proof. simpl. reflexivity. Qed.
Goal aeval ex3 empty = 1. Proof. simpl. reflexivity. Qed.
Goal forall s, aeval ex4 s = 10.
Proof.
  intro. simpl.
  rewrite Nat.add_comm.
  simpl.
  reflexivity.
Qed.

Fixpoint optim (a : AExp) : AExp :=
match a with
| ALit n => ALit n
| AVar x => AVar x
| APlus a1 a2 => APlus (optim a1) (optim a2)
| AIf (ALit 0) a2 a3 => a3
| AIf a1 a2 a3 => AIf (optim a1) (optim a2) (optim a3)
end.

Theorem optim_sound :
  forall a s, aeval a s = aeval (optim a) s.
(* END FIX *)
(** 3. feladat: (1 pont)
                Bizonyitsd be a fenti optimalizacio helyesseget!

    Task 3: (1 point)
                Prove the correctness of the optimisation above!
*)
(* Tipp: AIf eseten segithet a `remember` vagy a `simpl in *` taktika
         az atirasok megvalositasahoz.

   Hint: to avoid oversimplification, `remember` could be useful, or `simpl in *`.
*)
Proof.
  intro.
  induction a.
  - simpl. reflexivity.
  - simpl. destruct s0.
    + reflexivity.
    + simpl. reflexivity.
  - simpl. intro. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. destruct a1.
    + simpl. intro. rewrite IHa2. 
      destruct n.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + simpl. intro. rewrite IHa2. rewrite IHa3. reflexivity.
    + simpl. intro. simpl in IHa1. rewrite IHa1. rewrite IHa2. rewrite IHa3. reflexivity.
    + simpl. intro. simpl in IHa1. rewrite IHa1. rewrite IHa2. rewrite IHa3. reflexivity.
Qed.
    
  
(* BEGIN FIX *)
Reserved Notation "| a , st | -=> v" (at level 60).
Inductive eval_bigstep : AExp -> state -> nat -> Prop :=

| eval_lit (n : nat) (s : state) :
(* ----------------------- *)
   | ALit n , s | -=> n

| eval_var (x : string) (s : state) :
(* ---------------------- *)
  | AVar x , s | -=> s x

| eval_plus (a1 a2 : AExp) (s : state) (n1 n2 : nat) :
    | a1 , s | -=> n1 -> | a2 , s | -=> n2 ->
(* --------------------------------------- *)
       | APlus a1 a2 , s | -=> (n1 + n2)


(* END FIX *)
(** 4. feladat: (1 pont)
               Add meg a ternary operator big-step szemantikajat a
               2. feladatbeli leiras szerint, ugy, hogy a lenti
               tetelek (tesztek) bizonyithatoak legyenek!
               Tippek:
                - 2 levezetesi szabalyt is fel kell venned!
                - Tovabbi otletekert nezd meg, hogy az elagazas (if-then-else)
                  szemantikaja hogyan volt eloadason definialva!

    Task 4: (1 point)
               Define the big-step semantics of the ternary operator
               based on the informal descrition in task 2!
               Hints:
                - You need to define 2 derivation rules!
                - Check the lecture notes on the semantics of if-then-else for
                  inspiration!
*)
| eval_if_true (a1 a2 a3 : AExp) (s : state) (n : nat) :
    aeval a1 s <> 0 -> | a2 , s | -=> n -> 
(* --------------------------------------- *)
       | AIf a1 a2 a3 , s | -=> n
    

| eval_if_false (a1 a2 a3 : AExp) (s : state) (n : nat) :
    aeval a1 s = 0 -> | a3 , s | -=> n -> 
(* --------------------------------------- *)
       | AIf a1 a2 a3 , s | -=> n



(* BEGIN FIX *)
where "| a , st | -=> v" := (eval_bigstep a st v).


(** 5. feladat: (1 pont)
               Bizonyitsd a kovetkezo teszteseteket!
    Tipp: hasznald az `apply eval_if_true with (n1 := )` taktikat, ha a
          ternary operator igaz agat ertekeled ki! `` a `a1 ? a2 : a3`
          kifejezes `a1` reszkifejezesenek eredmenyet reprezentalja!

    Task 5: (1 point)
               Prove the following derivations!
    Hint: use `apply eval_if_true with (n1 := )` when you need to
          evaluate based on `eval_if_true`! `` should reflect the result
          of `a1` (in `a1 ? a2 : a3`)!

*)
Goal forall s, | ex1 , s | -=> 4.
(* END FIX *)
Proof.
  intro. simpl. apply eval_if_false.
  - reflexivity.
  - apply eval_lit.
Qed.



(* BEGIN FIX *)
Goal | ex2 , aState | -=> 2.
(* END FIX *)
Proof.
  simpl. apply eval_if_true.
  - unfold not. intro. discriminate.
  - apply eval_lit.
Qed.


(* BEGIN FIX *)
Goal | ex3 , aState | -=> 42.
(* END FIX *)
Proof.
  (* Tipp: 42-t csereld le 42 + 0-ra!
     Hint: replace 42 with 42 + 0 *)
  replace 42 with (42 + 0).
  - apply eval_plus.
    + apply eval_if_false.
      * reflexivity.
      * apply eval_var.
    + apply eval_if_true.
      * unfold not. intro. discriminate.
      * apply eval_lit.
  - rewrite Nat.add_0_r. reflexivity.
Qed.

(* BEGIN FIX *)
(*
  1. Bonusz feladat (0.5 pont)

  Tippek:
   - `a1` kiertekeleset `s` fuggvenyeben fogod tudni megadni!
   - Nincs szukseg indukciora/esetszetvalasztasra!
   - Szukseg lehet a `Nat.add_1_r` tetelre!

  Bonus task 1 (0.5 points)

  Hints:
   - The evaluation of `a1` is going to depend on `s`!
   - There is no need for induction/case separation!
   - To evaluate the `APlus` subexpression, you might need `Nat.add_1_r`
     from the standard library!
*)
Goal forall s, | ex4 , s | -=> 10.
(* END FIX *)
Proof.
  intro. simpl. apply eval_if_true.
  - simpl. rewrite Nat.add_1_r. unfold not. intro. discriminate.
  - apply eval_lit.
Qed.


(* BEGIN FIX *)
Theorem bigstep_deterministic : 
  forall a s n, | a, s | -=> n -> forall m, | a, s | -=> m -> n = m.
(* END FIX *)
(** 6. feladat: (0.5 pont)
                Bizonyitsd a determinizmusat az igy kapott big-step szemantikanak!

    Task 6: (0.5 points)
                Prove that the big-step semantics is deterministic!
*)
Proof.
  (* Tipp: `AIf` eseten 4 eset lesz, attol fuggoen, hogy `a1` 0-ra (vagy nem 0-ra)
           ertekelodik-e ki. Probalj meg ellentmodast talalni abban a 2
           esetben, amikor `a1` egyszerre 0-ra es nem 0-ra ertekelodik ki
           a ket levezetesben!

     Hint: In case of `AIf`, four subgoals will be created based on which derivation
           rule has been applied in which derivation. In two cases, try to
           find counterexample when `a1` is evaluated both to 0 and not 0!
*)
  intros a s n H1 m H2.
  induction n.
  - inversion H1.
    + inversion H2. 
  Abort.

(* BEGIN FIX *)
Reserved Notation "| a , st | => v" (at level 60).
Inductive eval_smallstep : AExp -> state -> AExp -> Prop :=

| seval_var x s :
  (* ------------------------ *)
    | AVar x, s | => ALit (s x)

| seval_plus_lhs a1 a1' a2 s:
     | a1, s | => a1' ->
  (* ---------------------------------- *)
     | APlus a1 a2, s | => APlus a1' a2

| seval_plus_rhs n a2' a2 s:
     | a2, s | => a2' ->
  (* ---------------------------------------------- *)
     | APlus (ALit n) a2, s | => APlus (ALit n) a2'

| seval_plus n1 n2 s :
  (* ------------------------------------------------- *)
    | APlus (ALit n1) (ALit n2), s | => ALit (n1 + n2)
(* END FIX *)
(** 7. feladat: (1 pont)
                Add meg a ternaris operator small-step szemantikajat a 2.
                feladateli leírás alapán úgy, hogy a követező tesztek 
                bizonyíthatóak legyenek!
                Tippek:
                - 3 levezetesi szabalyt is fel kell venned!
                - Az egyik szabalynak `a1`-et kell kiertekelnie!
                - Tovabbi otletekert nezd meg, hogy az elagazas (if-then-else)
                  small-step szemantikaja hogyan volt eloadason definialva!

    Task 7: (1 point)
                Define the small-step semantics of the ternary operator based
                on the description in task 2!
                Hints:
                - You need to define 3 derivation rules!
                - You need a rule to evaluate `a1`!
                - Check the lecture notes on the small-step semantics of
                  if-then-else for inspiration!
*)

  (* evaluate a1 to help moving on with the AIf *)
  | seval_if a1 a1' a2 a3 s :
      | a1, s | => a1' ->
  (* --------------------------------- *)
      | AIf a1 a2 a3, s | => AIf a1' a2 a3

  | seval_if_true a1 a2 a3 s n :
    | a1, s | => ALit n -> n <> 0 ->
  (* --------------------------------- *)
      | AIf a1 a2 a3, s | => a2

  | seval_if_false a1 a2 a3 s :
    | a1, s | => ALit 0 ->
  (* --------------------------------- *)
      | AIf a1 a2 a3, s | => a3

(* BEGIN FIX *)
where "| a , st | => v" := (eval_smallstep a st v).

Reserved Notation "| a , st | =>* v" (at level 60).
Inductive eval_smallstep_rtc : AExp -> state -> AExp -> Prop := 

| seval_refl a s :
  | a , s | =>* a
| seval_trans a a' a'' s :
  | a, s | => a' -> | a', s | =>* a'' ->
(* ------------------------------------*)
            | a, s | =>* a''

where "| a , st | =>* v" := (eval_smallstep_rtc a st v).

(** 8. feladat: (1 pont)
               Bizonyitsd a kovetkezo teszteseteket!

    Task 8: (1 point)
               Prove the following tests!
*)
Goal forall s, | ex1 , s | =>* ALit 4.
(* END FIX *)
Proof.
  intro s. unfold ex1.
  apply seval_trans with (a' := AIf (ALit 0) (ALit 5) (ALit 4)).
  - apply seval_if. apply seval_refl.

(* BEGIN FIX *)
Goal | ex2 , aState | =>* ALit 2.
(* END FIX *)
Proof.

Admitted.

(* BEGIN FIX *)
Goal | ex3 , aState | =>* ALit 42.
(* END FIX *)
Proof.

Admitted.

(* BEGIN FIX *)
(*
  2. Bonusz feladat (0.5 pont)

  Tippek:
   - Nincs szukseg indukciora/esetszetvalasztasra!
   - Szükség lehet a `Nat.add_1_r` tétel használatára!

  Bonus task 2 (0.5 points)
  Hints:
   - There is no need for induction/case separation!
   - You might need to use `Nat.add_1_r`!
*)
Goal forall s, | ex4 , s | =>* ALit 10.
(* END FIX *)
Proof.

Admitted.

(* BEGIN FIX *)
Theorem smallstep_determinism :
  forall a s a', | a, s | => a' -> forall a'', | a, s | => a'' -> a' = a''.
(** 9. feladat: (0.5 pont)
                 Bizonyitsd a determinizmusat az igy kapott small-step szemantikanak!

    Task 9: (0.5 points)
                 Prove the determinism of the small-step semantics!
*)
(* END FIX *)
Proof.

Admitted.
