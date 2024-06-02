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

(* big step operational semantics *)

Reserved Notation "e , s =v n" (at level 50).
Inductive evalb : exp -> state -> nat -> Prop :=
  | evalb_lit (n : nat)(s : state) :

    (*------------------*)
    lit n , s =v n

  | evalb_var (x : string)(s : state) :

    (*------------------*)
    var x , s =v s x

  | evalb_plus (n1 n2 : nat)(e1 e2 : exp)(s : state) :

    e1 , s =v n1  ->  e2 , s =v n2 ->
    (*----------------------------*)
    plus e1 e2 , s =v (n1 + n2)

  where "e , s =v n" := (evalb e s n).

Example ex1 : eval (plus (plus (var W) (var X)) (lit 100)) 
                     (update W 200 empty) = 300.
Proof.
  simpl. reflexivity.
Qed.

(*
s = W |-> 200, X |-> 0

levezetési fa:
 ------------   ---------- evalb_var
  W, s =v 200   X, s =v 0
 ----------------------- evalb_plus    -------------- evalb_lit
     W + X, s =v 200                     100, s =v 100
 ----------------------------------------------------- evalb_plus
             (W + X) + 100, s =v 300
 *)

Example ex1b : plus (plus (var W) (var X)) (lit 100) ,
                     update W 200 empty =v 300.
Proof.
  Check evalb_plus.
  (* pose proof (evalb_plus 200 100 (plus (var W) (var X)) (lit 100)).
  simpl in H. apply H. *)
  apply (evalb_plus 200 100).
  * apply evalb_plus with (n1 := 200) (n2 := 0).
    - apply evalb_var.
    - apply evalb_var.
  * apply evalb_lit.
Qed.

Example ex1b_not : ~ plus (plus (var W) (var X)) (lit 100) ,
                       update W 201 empty =v 300.
Proof.
  intro.
  Check evalb_plus.
  (* eapply evalb_plus in H. <- ez bonyolultabb plus kifejezések
     levezetésére következtet *)
  inversion H. subst. clear H.
  inversion H4. subst. clear H4.
  inversion H5. subst. clear H5.
  inversion H1. subst. clear H1.
  (*
  Opaque Nat.add.
  unfold update, empty in H2. cbn in H2. (* cbn ua. mint a simpl, csak több definíciót unfoldol egyszerűsítés közben *)
  Transparent Nat.add.
  *)
  inversion H7. subst. clear H7.
  (* discriminate *)
  unfold update, empty in H2. cbn in H2.
  discriminate.
Qed.

Example ex2b : exists (n : nat),
  plus (plus (var X) (var Y)) (plus (lit 3) (var Z)) , 
  update X 3 (update Y 2 empty) =v n.
Proof.
  exists 8.
  replace 8 with (5 + 3) (*at 1*) by reflexivity.
  apply evalb_plus.
  * apply evalb_plus with (n1 := 3) (n2 := 2).
    - apply evalb_var.
    - apply evalb_var.
  * apply evalb_plus with (n1 := 3) (n2 := 0).
    - apply evalb_lit.
    - apply evalb_var.
Qed.

Lemma denot2bigstep (e : exp)(s : state) : forall (n : nat), eval e s = n -> e , s =v n.
Proof.
  induction e; intros.
  * simpl in H. rewrite H. apply evalb_lit.
  * simpl in H. rewrite <- H. apply evalb_var.
  * simpl in H. rewrite <- H.
    apply evalb_plus.
    - apply IHe1. reflexivity.
    - apply IHe2. reflexivity.
Qed.

Lemma bigstep2denot (e : exp)(s : state) : forall (n : nat), e , s =v n -> eval e s = n.
Proof.
  intros. induction H. (* levezetés szerinti indukció *)
  * simpl. reflexivity.
  * (* now *) simpl. reflexivity.
  * simpl. (* now *) rewrite IHevalb1, IHevalb2. reflexivity.
Qed.

Lemma bigstepVsdenot (e : exp)(s : state)(n : nat) : e , s =v n <-> eval e s = n.
Proof.
  split.
  * apply bigstep2denot.
  * apply denot2bigstep.
Qed.

Lemma totality :
  forall (e : exp) (s : state), exists (n : nat), e, s =v n.
Proof.
  intros. exists (eval e s).
  apply denot2bigstep. reflexivity.
Qed. 

(* no need for induction. just use bigstep2denot! *)
Lemma determBigstep (e : exp)(s : state)(n : nat) : e , s =v n -> forall n', e , s =v n' -> n = n'.
Proof.
  (* intro. induction H. *)
  intros.
  apply bigstep2denot in H, H0.
  rewrite H in H0. assumption.
Qed.


Lemma notInvertible (n : nat)(s : state) : 
  exists (e e' : exp), e <> e' /\ e , s =v n /\ e' , s =v n.



