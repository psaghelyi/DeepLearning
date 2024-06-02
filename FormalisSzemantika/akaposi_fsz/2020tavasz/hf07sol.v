From Coq Require Import Strings.String.

Inductive exp : Type :=
| lit (n : nat)
| var (x : string)
| plus (e1 e2 : exp).

Definition state : Type := string -> nat.

Definition empty : state := fun x => 0.

Definition update (x:string)(n:nat)(s:state) : state :=
  fun x' => match string_dec x x' with
  | left  e => n
  | right e => s x'
  end.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Reserved Notation "e , s => e'" (at level 50).

Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :

    (*------------------*)
    var x , s => lit (s x)

  | eval_plus_lhs (e1 e2 e1' : exp)(s : state) :

          e1 , s => e1'           ->
    (*-------------------------*)
    plus e1 e2 , s => plus e1' e2

  | eval_plus_rhs (e2 e2' : exp)(s : state)(n : nat) :

             e2 , s => e2'                  ->
    (*-----------------------------------*)
    plus (lit n) e2 , s => plus (lit n) e2'

  | eval_plus_fin (n m : nat)(s : state) :

    (*-----------------------------------*)
    plus (lit m) (lit n) , s => lit (m + n)

  where "e , s => e'" := (evalo e s e').

Example ex1 : exists (e : exp)(m n : nat), e , empty => plus (lit m) (lit n).
exists (plus (lit 0) (var X)). exists 0. exists 0. apply eval_plus_rhs. apply eval_var.
Qed.

Example ex2 : exists (e : exp), plus (lit 1) (plus (lit 2) (lit 3)) , empty => e.
exists (plus (lit 1) (lit 5)). apply eval_plus_rhs. apply eval_plus_fin. Qed.

Example ex3 : ~ (exists (s : state), var X , s => var Y).
intro. destruct H. inversion H. Qed.

Example ex4 : forall (s : state)(e : exp), var X , s => e -> exists (n : nat), e = lit n.
intros. inversion H. exists (s X). reflexivity. Qed.

Example ex5 : ~ (plus (lit 3) (plus (lit 4) (plus (lit 5) (lit 6))) , empty => 
                 plus (lit 3) (plus (lit 4) (lit 12))).
intro. inversion H. inversion H3. inversion H8. Qed.

Example ex6 : exists (e1 e2 : exp), e1 <> e2 /\ e1 , empty => lit 0 /\ e2 , empty => lit 0.
exists (plus (lit 0) (lit 0)). exists (var X). split.
 - intro. inversion H.
 - split.
   + apply eval_plus_fin.
   + apply eval_var.
Qed.

Reserved Notation "e , s =>* e'" (at level 50).

Inductive evalo_rtc : exp -> state -> exp -> Prop :=
  | eval_refl (e : exp)(s : state) : 

    e , s =>* e

  | eval_trans (e e' e'' : exp)(s : state) :

    e , s => e'    ->    e' , s =>* e'' ->
    (*-------------------------------*)
    e , s =>* e''

  where "e , s =>* e'" := (evalo_rtc e s e').

Example ex7 : exists (n : nat),
  plus (plus (var X) (var Y)) (plus (lit 3) (var Z)) , update X 3 (update Y 2 empty) =>* lit n.
exists 8.
apply (eval_trans _ (plus (plus (lit 3) (var Y)) (plus (lit 3) (var Z)))).
 * apply (eval_plus_lhs _ _ (plus (lit 3) (var Y))).
   ** apply eval_plus_lhs.
      *** apply eval_var.
 * apply (eval_trans _ (plus (plus (lit 3) (lit 2)) (plus (lit 3) (var Z)))).
   ** apply eval_plus_lhs.
      *** apply eval_plus_rhs.
          **** apply eval_var.
   ** apply (eval_trans _ (plus (lit 5) (plus (lit 3) (var Z)))).
      *** apply eval_plus_lhs.
          **** apply eval_plus_fin.
      *** apply (eval_trans _ (plus (lit 5) (plus (lit 3) (lit 0)))).
          **** apply eval_plus_rhs.
               ***** apply eval_plus_rhs.
                     ******* apply eval_var.
          **** apply (eval_trans _ (plus (lit 5) (lit 3))).
               ***** apply eval_plus_rhs.
                     ******* apply eval_plus_fin.
               ***** apply (eval_trans _ (lit 8)).
                     ******* apply eval_plus_fin.
                     ******* apply eval_refl.
Qed.

Lemma notrefl (e : exp)(s : state) : ~ (e , s => e).
intro.
induction e.
 * inversion H.
 * inversion H.
 * inversion H.
   - (* eval_plus_lhs *) apply IHe1. exact H3.
   - (* eval_plus_rhs *) apply IHe2. exact H3.
Qed.

(* tanacs: szukseg lesz a notrefl-re *)
Lemma notsym (e e' : exp)(s : state) : e , s => e' -> ~ e' , s => e.
intros.
induction H.
 - intro. inversion H.
 - intro. inversion H0.
   + apply IHevalo. exact H4. 
   + apply (notrefl e2 s). exact H4.
 - intro. inversion H0.
   + inversion H4.
   + apply IHevalo. exact H4.
 - intro. inversion H.
Qed.

Lemma trans (e e' e'' : exp)(s : state) : e , s =>* e' -> e' , s =>* e'' -> e , s =>* e''.
intros.
induction H.
  - exact H0.
  - apply (eval_trans _ _ _ _ H). apply IHevalo_rtc. exact H0.
Qed.
