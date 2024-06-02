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

Reserved Notation "e , s =>* e'" (at level 50).
Inductive evalo_rtc : exp -> state -> exp -> Prop :=
  | eval_refl (e : exp)(s : state) : 
    e , s =>* e
  | eval_trans (e e' e'' : exp)(s : state) :
    e , s => e'    ->    e' , s =>* e'' ->
    e , s =>* e''
  where "e , s =>* e'" := (evalo_rtc e s e').


(*

                 + (5)
                / \
            (5)+   X (0)
              / \
             2   3

                                                    +
                /                                                               \
  eval_trans with (e' := plus (lit 5) (var X))            eval_trans with (e' := plus (lit 5) (lit 0))
              /
      eval_plus_lhs
              /
eval_plus_fin

*)


Example steps : exists n , 
  plus (plus (lit 2) (lit 3)) (var X) , empty =>* lit n.
Proof.
exists 5.
apply eval_trans with (e' := plus (lit 5) (var X)).
- apply eval_plus_lhs.
-- apply eval_plus_fin.
- apply eval_trans with (e' := plus (lit 5) (lit 0)).
-- apply eval_plus_rhs.
--- apply eval_var.
-- apply eval_trans with (e' := lit 5).
--- apply eval_plus_fin.
--- apply eval_refl.
Qed.

(*
draw the tree of the evaluation from the rule names used from the proof above



eval_trans with (e' := plus (lit 5) (var X)).
  eval_plus_lhs.
    eval_plus_fin.

eval_trans with (e' := plus (lit 5) (lit 0)).
  eval_plus_rhs.
    eval_var.
  eval_plus_fin.
    eval_refl.

eval_trans with (e' := lit 5).
  eval_plus_fin.
    eval_refl.


*)
    
  


(* END FIX *)