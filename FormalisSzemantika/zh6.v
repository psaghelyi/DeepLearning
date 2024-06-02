(* BEGIN FIX *)
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
Definition empty : state := fun x => 0.
Definition update (x : string)(n : nat)(s : state)
  : state := fun x' => match string_dec x x' with
  | left e  => n
  | right ne => s x'
  end.
Reserved Notation "e , s => e'" (at level 50).
Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :
    var x , s => lit (s x)
  | eval_plus_lhs (e1 e2 e1' : exp)(s : state) :
    e1 , s => e1' ->
    plus e1 e2 , s => plus e1' e2
  | eval_plus_rhs (e2 e2' : exp)(s : state)(n : nat) :
    e2 , s => e2' ->
    plus (lit n) e2 , s => plus (lit n) e2'
  | eval_plus_fin (n m : nat)(s : state) :
    plus (lit m) (lit n) , s => lit (m + n)
  where "e , s => e'" := (evalo e s e').

Definition s : state :=
(* END FIX *)
  
  
  (* ezt ird at ugy, hogy ex-et bizonyitani tudd! *)
    update W 3 (update X 4 (update Y 7 empty)).

(* BEGIN FIX *)
Example ex : 
  plus (plus (lit 2) (var Y)) (lit 5) , s =>
  plus (plus (lit 2) (lit 7)) (lit 5).
Proof.
  apply eval_plus_lhs.
  apply eval_plus_rhs.
  apply eval_var.
Qed.

(* END FIX *)
