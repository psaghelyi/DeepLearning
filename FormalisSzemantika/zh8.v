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
Reserved Notation "e , s =v n" (at level 50).
Inductive evalb : exp -> state -> nat -> Prop :=
  | evalb_lit (n : nat)(s : state) :
    lit n , s =v n
  | evalb_var (x : string)(s : state) :
    var x , s =v s x
  | evalb_plus (n1 n2 : nat)(e1 e2 : exp)(s : state) :
    e1 , s =v n1  ->  e2 , s =v n2 ->
    plus e1 e2 , s =v (n1 + n2)
  where "e , s =v n" := (evalb e s n).

Example ex3 : exists (str : string),
  plus (plus (var Y) (var str)) (lit 4) , 
  update X 3 (update Y 2 empty) =v 9.
Proof.
  exists X.
  apply evalb_plus with (n1 := 5) (n2 := 4).
  - apply evalb_plus with (n1 := 2) (n2 := 3).
    + apply evalb_var.
    + apply evalb_var.
  - apply evalb_lit.
Qed.


(* END FIX *)

