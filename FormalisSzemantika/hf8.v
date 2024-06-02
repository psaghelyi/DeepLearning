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

Example ex1 : forall (n : nat)(s : state), 
  plus (lit n) (lit n) , s =v (n + n).


Example ex2 : forall (n : nat)(x : string), 
  plus (var x) (lit n) , empty =v n.


Example ex3 : exists (x : string),
  var x , update X 3 (update Y 2 empty) =v 2.


Example ex4 : exists (x : string)(n : nat),
  plus (plus (lit 1) (var x)) (lit n) ,
  update X 3 (update Y 4 (update Z 5 empty)) =v 8.

