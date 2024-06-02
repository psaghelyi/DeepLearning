Require Import Strings.String.

Inductive exp : Type :=
  | lit : nat -> exp
  | var : string -> exp
  | plus : exp -> exp -> exp.
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition state : Type := string -> nat.
Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | plus e1 e2 => eval e1 s + eval e2 s
  end.
Definition empty : state := fun x => 0.
Definition update (x : string)(n : nat)(s : state)
  : state := fun x' => match string_dec x x' with
  | left e  => n
  | right ne => s x'
  end.

(* ismetles *)
Definition e1 : exp := plus (var Y) (plus (var X) (var Y)).
Definition st1 : state := fun x => 2. (* st1-et modositsd, hogy e1 bizonyithato legyen! *)
Lemma e1test : eval e1 (update X 0 st1) = 4.
compute. reflexivity. Qed.

(* hf-bol *)
Lemma update_sound (x : string)(n : nat)(s : state) :
  (update x n s) x = n.
Proof.
(* tipp *) unfold update. Check (string_dec x x). destruct (string_dec x x).
- reflexivity.
- unfold "<>" in n0. assert False. apply n0. reflexivity. destruct H. Qed.

(*            bevezetes          eliminalas
              (ha ez a Goal)     (ha ez a feltetel)
->            intro              apply
forall        intro              apply
/\            split              destruct
\/            left, right        destruct
exists        exists             destruct
False         -                  destruct
True          trivial            -
=             reflexivity        rewrite
barmi                            assumption
Inductive     (konstruktorok)    destruct, induction
*)

Lemma update_neq (x x' : string)(n : nat)(s : state)(ne : x <> x') :
  (update x n s) x' = s x'.
unfold update. destruct (string_dec x x').
- assert False. apply ne. assumption. destruct H.
- reflexivity.
Qed.

(* Denotacios szemantika: egy e kifejezes jelentese egy 

     eval e : state -> nat

   fuggveny.

   Operacios szemantika: egy e kifejezes jelentese egy 

      evalo e : state -> exp -> Prop
      evalo e ⊂ state x exp

   relacio.
 *)

(* Other relations in Coq:
   ----------------------- *)

Definition P : nat -> Prop
  := fun n => 3 <= n.
(* unaris relacio / predikatum ,  P ⊂ nat,   P : nat -> Bool,  P = {3,4,5,6,7,...} 
P O = False
P 1 = False
P 2 = False
P 3 = True
P 4 = True
...
*)
Definition P' (n : nat) : Prop := match n with
  | 0 => False
  | 1 => False
  | 2 => False
  | _ => True
  end.

(*Lemma lem : (3 = 2 /\ 2 < 5).*)

Example P3 : P 3.  (* 3 ∈ P ,   P(3) teljesul *)
unfold P. Print "<=". Check le_n. apply le_n. Qed.

Example notP'2 : not (P' 2).
unfold not. intro. simpl in H. assumption. Qed.

(* hasznalj inversion-t! *)
Example notP2 : not (P 2).
intro. unfold P in H. Print "<=". inversion H. inversion H1. inversion H3. Qed.
(*
le_S (_ : 3 <= 1) : 3 <= 2
le_S (_ : 3 <= 0) : 3 <= 1

le_n : n <= n
le_S : 3 <= n -> 3 <= S n
*)

Print "=".

(* Most megadunk induktivan egy relaciot a kifejezeseken.
R ⊂ exp x state x exp
R(e,s,e') === s allapotban az e kifejezesbol egy lepesben e' kepzodik
e,s=>e'
e',s=>e''
e'',s=>e'''
...
  

Levezetesi szabalyok:

  ----------------------eval_var
  var x , s => lit (s x)

          e1 , s => e1'
  -----------------------------eval_plus_lhs
  plus e1 e2 , s => plus e1' e2

               e2 , s => e2'
  ---------------------------------------eval_plus_rhs
  plus (lit n) e2 , s => plus (lit n) e2'

  ---------------------------------------eval_plus_fin
  plus (lit m) (lit n) , s => lit (m + n)


Ha s X = 1, vezesd le, hogy 


           ------------------eval_var
           var X , s => lit 1
  ------------------------------------------------eval_plus_lhs
  plus (var X) (lit 3) , s => plus (lit 1) (lit 3)

  plus e1      e2      , s => plus e1'     e2

!

Mutasd meg, hogy  

  --------------------------------- nincs ilyen szabaly
  plus (var X) (lit 3) , s => lit 4


nem levezetheto!

Vezesd le, hogy 

  --------------------------------- eval_plus_fin
  plus (lit 1) (lit 3) , s => lit 4

!

Vezesd le, hogy mire irodik at (tobb lepesben)
  plus (var X) (var Y)
!

Most megcsinaljuk ezeket formalisan is:
*)

Reserved Notation "e , s => e'" (at level 50).
Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :

    (*-------------------*)
    var x , s => lit (s x)

  | eval_plus_lhs (e1 e2 e1' : exp)(s : state) :

    e1 , s => e1' ->
    (*-------------------------*)
    plus e1 e2 , s => plus e1' e2

  | eval_plus_rhs (e2 e2' : exp)(s : state)(n : nat) :

    e2 , s => e2' ->
    (*-----------------------------------*)
    plus (lit n) e2 , s => plus (lit n) e2'

  | eval_plus_fin (n m : nat)(s : state) :

    (*------------------------------------*)
    plus (lit m) (lit n) , s => lit (m + n)

  where "e , s => e'" := (evalo e s e').


(* 
          ----------------------eval_var
          (var X) , s => (lit 4)
  ------------------------------------------------eval_plus_lhs
  plus (var X) (lit 3) , s => plus (lit 4) (lit 3)
*)

Example eval1 : plus (var X) (lit 3) , (update X 4 empty) => plus (lit 4) (lit 3).
(* probald meg eval_plus_rhs-t alkalmazni! *)
apply eval_plus_lhs. apply eval_var. Qed.

Example eval2 : forall s, plus (lit 4) (lit 3) , s => lit 7.
Admitted.

(*
unfold valami
simpl
compute

inversion: azt vizsgalja meg, hogy egy ertek egy induktiv Prop-beli allitasnak mely 
  konstruktoraval jott letre, es ebbol a leheto legtobb informaciot kiszedi

*)