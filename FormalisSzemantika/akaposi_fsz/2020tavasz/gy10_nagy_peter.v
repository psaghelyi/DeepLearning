(*

Ebben a fájlban Nagy Péter MSc hallgató belátta, hogy a WHILE nyelv
operációs és üzemanyagos denotációs szemantikája ekvivalens.

 *)


From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

Inductive aexp : Type :=
  | alit (n : nat)
  | avar (x : string)
  | aplus (a1 a2 : aexp)
  | aminus (a1 a2 : aexp)
  | amult (a1 a2 : aexp).

Inductive bexp : Type :=
| btrue
| bfalse
| band (b1 b2 : bexp)
| bnot (b : bexp)
| beq (a1 a2 : aexp)
| bleq (a1 a2 : aexp).

Inductive cmd : Type :=
| cskip
| cif (b : bexp) (c1 c2 : cmd)
| cwhile (b : bexp) (c : cmd)
| cassign (x : string) (a : aexp)
| cseq (c1 c2 : cmd).

Coercion avar : string >-> aexp.
Coercion alit : nat >-> aexp.
Notation "x + y"     := (aplus x y) (at level 50, left associativity).
Notation "x - y"     := (aminus x y) (at level 50, left associativity).
Notation "x * y"     := (amult x y) (at level 40, left associativity).
Definition bool2bexp (b : bool) : bexp := if b then btrue else bfalse.
Coercion bool2bexp : bool >-> bexp.
Notation "x & y" := (band x y) (at level 81, left associativity).
Notation "'~' b" := (bnot b) (at level 75, right associativity).
Notation "x == y" := (beq x y) (at level 70, no associativity).
Notation "x <= y" := (bleq x y) (at level 70, no associativity).
Notation "'SKIP'"    := cskip.
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" := (cif b c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := (cwhile b c) (at level 80, right associativity).
Notation "x '::=' a" := (cassign x a) (at level 60).
Notation "c1 ;; c2"  := (cseq c1 c2) (at level 80, right associativity).

Definition X : string := "X"%string.
Definition Y : string := "Y"%string.
Definition Z : string := "Z"%string.

Definition state : Type := string -> nat.

Definition empty : state := fun x => 0.

Definition update (x:string)(n:nat)(s:state) : state :=
  fun x' => match string_dec x x' with
  | left  e => n
  | right e => s x'
  end.

Fixpoint aeval (a : aexp)(s : state) : nat :=
match a with
| alit n => n
| avar x => s x
| aplus a1 a2 => (aeval a1 s) + (aeval a2 s)
| aminus a1 a2 => (aeval a1 s) - (aeval a2 s)
| amult a1 a2 => (aeval a1 s) * (aeval a2 s)
end.

Fixpoint beval (b : bexp)(s : state) : bool :=
match b with
 | btrue => true
 | bfalse => false
 | band b1 b2 => (beval b1 s) && (beval b2 s)
 | bnot b => negb (beval b s)
 | beq a1 a2 => aeval a1 s =? aeval a2 s
 | bleq a1 a2 => aeval a1 s <=? aeval a2 s
end.

Inductive result : Type :=
  | final : state -> result
  | outoffuel : state -> result.

(* Ird at ceval-t, hogy result-ot adjon vissza! *)
Fixpoint ceval (c : cmd)(s : state)(n : nat) : result := match n with
  | O => outoffuel s
  | S n' => match c with
    | cskip       => final s
    | cif b c1 c2 => if beval b s then ceval c1 s n' else ceval c2 s n'
    | cwhile b c  => if beval b s then
        match (ceval c s n') with
        | final t => ceval (cwhile b c) t n'
        | outoffuel t => outoffuel t
        end
      else final s
    | cassign x a => final (update x (aeval a s) s)
    | cseq c1 c2  =>
      match ceval c1 s n' with
      | final t => ceval c2 t n'
      | r => r
      end
    end
 end.

Definition fromResult (r : result)(x : string) : nat * bool := match r with
  | final s => (s x , true)
  | outoffuel s => (s x , false)
  end.

(* Letezik olyan program, ami nem csinal semmit. *)
Lemma l1 : exists (c : cmd), forall n s, ceval c s (S n) = final s.
Proof.
  exists SKIP.
  intros.
  simpl.
  reflexivity.
Qed.

(* Letezik vegtelen ciklus. *)
Lemma l2 : exists (c : cmd), forall n s, exists s', ceval c s n = outoffuel s'.
Proof.
  exists (WHILE true DO X ::= X + 1 END).
  intro n.
  induction n.
  all: intro s.
  - simpl.
    exists s.
    reflexivity.
  - simpl.
    destruct (ceval (X ::= X + 1) s n).
    * apply IHn.
    * exists s0.
      reflexivity.
Qed.

(* Letezik vegtelen ciklus, ami nem csinal semmit. *)
Lemma l3 : exists (c : cmd), forall s, exists s', forall n,
  ceval c s n = outoffuel s'.
Proof.
  exists (WHILE true DO SKIP END).
  simpl.
  intros.
  exists s.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    destruct n.
    * simpl.
      reflexivity.
    * (*remember (S n).
      rewrite -> Heqn0 at 1.
      simpl.
      exact IHn.*)
      simpl.
      exact IHn.
Qed.

(* Letezik vegtelen ciklus, ami nem csinal semmit. *)
Lemma l3' : exists (c : cmd), forall s, forall n, ceval c s n = outoffuel s.
Proof.
  exists (WHILE true DO SKIP END).
  simpl.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    destruct n.
    * simpl.
      reflexivity.
    * (*remember (S n).
      rewrite -> Heqn0 at 1.
      simpl.
      exact IHn.*)
      simpl.
      exact IHn.
Qed.

(* Lemma l4 : forall n, exists c,
  (exists s, ceval c empty n = final s) /\
  (exists s, ceval c empty (S n) = outoffuel s). *)
Lemma l4 : forall n, exists c,
  (exists s, ceval c empty (S n) = final s) /\
  (exists s, ceval c empty n = outoffuel s).
(* Proof.
  induction n.
  - exists SKIP.
    split.
    * exists empty.
      reflexivity.
    * exists empty.
      reflexivity.
  - destruct IHn as[c IHn].
    destruct IHn as [H I].
    exists (c ;; SKIP).
    split.
    * destruct H as [s H].
      exists s.
      simpl in H.
      simpl.
      rewrite H.
      reflexivity.
    * destruct I as [s I].
      exists s.
      simpl.
      rewrite I.
      reflexivity.
Qed. *)
Proof.
  assert (forall n, exists c,
    (ceval c empty (S n) = final empty) /\
    (ceval c empty n = outoffuel empty)).
  - induction n.
    * exists SKIP.
      split.
      + simpl.
        reflexivity.
      + simpl.
        reflexivity.
    * destruct IHn as [c].
      exists (SKIP ;; c).
      split.
      + apply H.
      + simpl.
        destruct n.
        -- simpl.
           reflexivity.
        -- apply H.
  - intros.
    destruct (H n) as [c I].
    exists c.
    split.
    * exists empty.
      apply I.
    * exists empty.
      apply I.
Qed.

(* Lemma l5 : exists c, forall n,
  exists s, ceval c empty (S n) = final s /\ s X = n. *)
Lemma l5 : exists c, forall n,
  exists s, ceval c empty (S n) = outoffuel s /\ s X = n.
Proof.
  assert (exists (c : cmd), (forall (n : nat)(s : state),
    (exists (t : state), ((ceval c s (S n) = outoffuel t)
           /\ ((n%nat + (s X)%nat)%nat = (t X)%nat))))).
  - exists (WHILE true DO X ::= X + 1 END).
    induction n.
    * intros.
      exists s.
      simpl.
      split.
      + reflexivity.
      + reflexivity.
    * intros.
      pose proof (IHn (update X (s X + 1) s)) as IHn.
      destruct IHn as [t IHn].
      destruct IHn as [IHn1 IHn2].
      exists t.
      split.
      + remember (S n).
        simpl.
        rewrite Heqn0 at 1.
        simpl.
        assumption.
      + rewrite <- IHn2.
        assert (update X ((s X) + 1) s X = ((s X)%nat + 1%nat)%nat).
        reflexivity.
        rewrite H.
        rewrite <- (plus_n_Sm).
        rewrite <- (plus_n_Sm).
        rewrite <- (plus_n_O).
        simpl.
        reflexivity.
  - destruct H as [c H].
    exists c.
    intros.
    pose proof (H n empty) as H.
    destruct H as [t H].
    exists t.
    destruct H as [H1 H2].
    split.
    * assumption.
    * rewrite <- H2.
      rewrite (PeanoNat.Nat.add_comm).
      reflexivity.
Qed.

(*
opcionalis HF-ok: egeszistd ki a nyelvet FOR ciklussal, listakkal, eljarasokkal, 
fuggvenyekkel, bool/lista tipusu valtozokkal, stb.
*)


(* Big-step operacios szemantika. 
(a denotacios szemantika grafja -- itt nem problema a nemterminalas) *)

(*
  informális/Haskell/ML denotacios szemantika: fun c s => match c with
   | SKIP => s
   | x ::= a => update x (aeval a s) s
   | c1 ;; c2 => ceval c2 (ceval c1 s)
   | TEST b THEN c1 ELSE c2 FI => if beval b s then (ceval c1 s) else (ceval c2 s)
   | WHILE b DO c END => if beval b s then ceval (cwhile b c) (ceval c s) else s
*)

(* Add hozza a hianyzo szabalyokat! *)
(* ternális reláció *)
Reserved Notation "| s , st |=> st'" (at level 50).
Inductive cevalb : cmd -> state -> state -> Prop :=
  | cevalb_skip (s : state) :
  
       (*-------------*)
       | SKIP , s |=> s

  | cevalb_assign (x : string)(a : aexp)(s : state) :

       (*------------------------------------*)
       | x ::= a , s |=> update x (aeval a s) s

  | cevalb_seq (c1 c2 : cmd)(s s' s'' : state) :

       | c1 , s |=> s' -> | c2 , s' |=> s'' ->
       (*-------------*)
       | c1 ;; c2 , s |=> s''

  | cevalb_if_true (b : bexp)(c1 c2 : cmd)(s s' : state) :

       beval b s = true -> | c1 , s |=> s' ->
       (*------------------------------------*)
       | TEST b THEN c1 ELSE c2 FI , s |=> s'

  | cevalb_if_false (b : bexp)(c1 c2 : cmd)(s s' : state) :

       beval b s = false -> | c2 , s |=> s' ->
       (*------------------------------------*)
       | TEST b THEN c1 ELSE c2 FI , s |=> s'

  | cevalb_while_false (b : bexp)(c : cmd)(s : state) :

       beval b s = false ->
       (*------------------------------------*)
       | WHILE b DO c END , s |=> s

  | cevalb_while_true (b : bexp)(c : cmd)(s s' s'' : state) :

       beval b s = true ->
       | c, s |=> s' ->
       | WHILE b DO c END , s' |=> s'' ->
       (*------------------------------------*)
       | WHILE b DO c END , s |=> s''

where "| c , s |=> s'" := (cevalb c s s').


Example ex1 (s : state) : | X ::= 42 , s |=> update X 42 s.
Proof.
  apply cevalb_assign.
Qed.

(* coq-ban nem bizonyítható, hogy
    (update X 4 (update X 3 empty)) = (update X 3 empty)
      (következik a függvény extenzionalitás axiomából)
  de az se, hogy
    (update X 4 (update X 3 empty)) <> (update X 3 empty)
  és egyik feltételezése se ellentmondásos
  *)

Example ex2 : exists c s, | c , empty |=> s /\ s X = 4.
Proof.
  exists (X ::= 4).
  exists (update X 4 empty).
  split.
  - apply cevalb_assign.
  - reflexivity.
Qed.

Example ex3 : exists (c : cmd), forall (n : nat), exists s,
  | c , update X n empty |=> s /\ s X = (n + 1)%nat.
Proof.
  exists (X ::= X + 1).
  intros.
  exists (update X (n+1) (update X n empty)).
  split.
  - apply cevalb_assign.
  - reflexivity.
Qed.

Example ex4 : exists (c : cmd), forall (n : nat), exists s,
  | c , update X n empty |=> s /\ s Y = (2 * n)%nat.
Proof.
  exists (Y ::= 2 * X).
  intros.
  exists (update Y (2*n) (update X n empty)).
  split.
  - apply (cevalb_assign).
  - reflexivity.
Qed.

Definition progif : cmd := (SKIP ;; TEST X <= Y THEN SKIP ELSE SKIP FI).

Example ex5 : | progif , empty |=> empty.
Proof.
  apply (cevalb_seq _ _ empty empty empty).
  - apply cevalb_skip.
  - apply cevalb_if_true.
    * reflexivity.
    * apply cevalb_skip.
Qed.

Definition prog6 : cmd :=
  X ::= 0 ;;
  WHILE X <= 2 DO
    X ::= X + 1
  END.

Example ex6 : exists s, | prog6 , empty |=> s /\ s X = 3.
Proof.
  remember (update X 0 empty) as s0.
  remember (update X 1 s0) as s1.
  rewrite Heqs0 in Heqs1.
  remember (update X 2 s1) as s2.
  rewrite Heqs1 in Heqs2.
  remember (update X 3 s2) as s3.
  rewrite Heqs2 in Heqs3.
  exists s3.
  split.
  - apply cevalb_seq with (s' := s0).
    * rewrite Heqs0.
      apply cevalb_assign.
    * apply cevalb_while_true with (s' := s1).
      + rewrite Heqs0.
        reflexivity.
      + rewrite Heqs1.
        rewrite Heqs0.
        apply cevalb_assign.
      + apply cevalb_while_true with (s' := s2).
        -- rewrite Heqs1.
           reflexivity.
        -- rewrite Heqs2.
           rewrite Heqs1.
           apply cevalb_assign.
        -- apply cevalb_while_true with (s' := s3).
          ** rewrite Heqs2.
             reflexivity.
          ** rewrite Heqs3.
             rewrite Heqs2.
             apply cevalb_assign.
          ** apply cevalb_while_false.
             rewrite Heqs3.
             reflexivity.
  - rewrite Heqs3.
    reflexivity.
Qed.

Require Import Coq.Program.Equality.
(* Do dependent induction on the big-step derivation! *)
Example ex7 : ~ (exists s, | WHILE true DO SKIP END , s |=> s).
Proof.
  unfold not.
  intros.
  destruct H as [s].
  (* remember s as s'.
  remember (WHILE true DO SKIP END) as c.
  induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - inversion Heqc.
    rewrite H1 in H.
    discriminate.
  - apply IHcevalb2.
    * assumption.
    * assumption. *)
  dependent induction H.
  apply IHcevalb2.
  - reflexivity.
  - inversion H0.
    reflexivity.
Qed.

Lemma determ_bigstep (s s1 s2 : state)(c : cmd) :
  | c , s |=> s1 -> | c , s |=> s2 -> s1 = s2.
Proof.
  intro.
  generalize dependent s2.
  dependent induction H.
  all: intros.
  - inversion H.
    reflexivity.
  - inversion H.
    reflexivity.
  - inversion H1.
    apply IHcevalb2.
    assert (s' = s'0).
    apply IHcevalb1.
    assumption.
    rewrite H8.
    assumption.
  - inversion H1.
    * apply IHcevalb.
      assumption.
    * rewrite H7 in H.
      inversion H.
  - inversion H1.
    * rewrite H7 in H.
      inversion H.
    * apply IHcevalb.
      assumption.
  - inversion H0.
    * reflexivity.
    * rewrite H3 in H.
      inversion H.
  - inversion H2.
    * rewrite <- H6 in H7.
      rewrite H7 in H.
      inversion H.
    * apply IHcevalb2.
      assert (s' = s'0).
      apply IHcevalb1.
      assumption.
      rewrite H10.
      assumption.
Qed.

Lemma ceval_S(c : cmd)(s t : state)(n : nat):
  (ceval c s n = (final t)) -> (ceval c s (S n) = (final t)).
Proof.
  dependent induction c.
  all: intros.
  all: destruct n eqn:N.
  1, 3, 5, 7, 9: inversion H.
  - simpl.
    simpl in H.
    assumption.
  - rewrite <- N.
    simpl.
    rewrite N.
    simpl in H.
    destruct (beval b s) eqn:B.
    * apply IHc1.
      assumption.
    * apply IHc2.
      assumption.
  - rewrite <- N.
    rewrite <- N in H.
    clear N n0.
    generalize dependent t.
    generalize dependent s.
    dependent induction n.
    all: intros.
    * inversion H.
    * simpl in H.
      destruct (beval b s) eqn:B.
      + destruct (ceval c s n) eqn:C.
        --remember (S n) as Sn.
          simpl.
          rewrite B.
          rewrite HeqSn.
          rewrite (IHc _ _ _ C).
          rewrite HeqSn in IHn.
          apply IHn.
          assumption.
        --inversion H.
      + simpl.
        rewrite B.
        assumption.
  - simpl in H.
    simpl.
    assumption.
  - simpl in H.
    rewrite <- N.
    simpl.
    rewrite N.
    destruct (ceval c1 s n0) eqn:C.
    * rewrite (IHc1 _ _ _ C).
      exact (IHc2 _ _ _ H).
    * inversion H.
Qed.

Inductive cevald : cmd -> state -> nat -> result -> Prop :=
  | cevald_outoffuel(c : cmd)(s : state) :
      cevald c s O (outoffuel s)
  | cevald_skip (s : state)(n : nat) :
      cevald SKIP s (S n) (final s)
  | cevald_assign (x : string)(a : aexp)(s : state)(n : nat) :
      cevald (x ::= a) s (S n) (final (update x (aeval a s) s))
  | cevald_seq_final (c1 c2 : cmd)(s s': state)(r : result)(n : nat) :
      (cevald c1 s n (final s'))
      -> (cevald c2 s' n r)
      -> (cevald (c1 ;; c2) s (S n) r)
  | cevald_seq_outoffuel (c1 c2 : cmd)(s s' : state)(n : nat) :
      (cevald c1 s n (outoffuel s'))
      -> (cevald (c1 ;; c2) s (S n) (outoffuel s'))
  | cevald_if_true (b : bexp)(c1 c2 : cmd)(s : state)(r : result)(n : nat) :
      (beval b s = true)
      -> (cevald c1 s n r)
      -> (cevald (TEST b THEN c1 ELSE c2 FI) s (S n) r)
  | cevald_if_false (b : bexp)(c1 c2 : cmd)(s : state)(r : result)(n : nat) :
      (beval b s = false)
      -> (cevald c2 s n r)
      -> (cevald (TEST b THEN c1 ELSE c2 FI) s (S n) r)
  | cevald_while_false (b : bexp)(c : cmd)(s : state)(n : nat) :
      (beval b s = false)
      -> (cevald (WHILE b DO c END) s (S n) (final s))
  | cevald_while_true_final (b : bexp)(c : cmd)(s s' : state)(r : result)(n : nat) :
      (beval b s = true)
      -> (cevald c s n (final s'))
      -> (cevald (WHILE b DO c END) s' n r)
      -> (cevald (WHILE b DO c END) s (S n) r)
  | cevald_while_true_outoffuel (b : bexp)(c : cmd)(s s' : state)(n : nat) :
      (beval b s = true)
      -> (cevald c s n (outoffuel s'))
      -> (cevald (WHILE b DO c END) s (S n) (outoffuel s'))
  .

Lemma ceval_cevald(c : cmd)(s : state)(n : nat)(r : result):
  (ceval c s n = r) <-> (cevald c s n r).
Proof.
  split.
  - dependent induction c.
    all: generalize dependent r.
    all: generalize dependent s.
    all: dependent induction n.
    all: intros.
    1, 3, 5, 7, 9: simpl in H; rewrite <- H; apply cevald_outoffuel.
    all: simpl in H.
    * rewrite <- H.
      apply cevald_skip.
    * destruct (beval b s) eqn:B.
      + apply cevald_if_true.
        --assumption.
        --apply IHc1.
          assumption.
      + apply cevald_if_false.
        --assumption.
        --apply IHc2.
          assumption.
    * destruct (beval b s) eqn:B.
      + destruct (ceval c s n) eqn:C.
        --apply cevald_while_true_final with (s' := s0).
          **assumption.
          **apply IHc.
            assumption.
          **apply IHn.
            assumption.
        --rewrite <- H.
          apply cevald_while_true_outoffuel.
          **assumption.
          **apply IHc.
            assumption.
      + rewrite <- H.
        apply cevald_while_false.
        assumption.
    * rewrite <- H.
      apply cevald_assign.
    * destruct (ceval c1 s n) eqn:C.
      + apply cevald_seq_final with (s' := s0).
        --apply IHc1.
          assumption.
        --apply IHc2.
          assumption.
      + rewrite <- H.
        apply cevald_seq_outoffuel.
        apply IHc1.
        assumption.
  - intros.
    dependent induction H.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * simpl.
      rewrite IHcevald1.
      assumption.
    * simpl.
      rewrite IHcevald.
      reflexivity.
    * simpl.
      rewrite H.
      assumption.
    * simpl.
      rewrite H.
      assumption.
    * simpl.
      rewrite H.
      reflexivity.
    * simpl.
      rewrite H.
      rewrite IHcevald1.
      assumption.
    * simpl.
      rewrite H.
      rewrite IHcevald.
      reflexivity.
Qed.

Lemma ceval_S2(c : cmd)(s t : state)(n : nat):
  (ceval c s n = (final t)) -> (ceval c s (S n) = (final t)).
Proof.
  intros.
  rewrite ceval_cevald.
  rewrite ceval_cevald in H.
  dependent induction H.
  - apply cevald_skip.
  - apply cevald_assign.
  - apply cevald_seq_final with (s' := s').
    * apply IHcevald1.
      reflexivity.
    * apply IHcevald2.
      reflexivity.
  - apply cevald_if_true.
    * assumption.
    * apply IHcevald.
      reflexivity.
  - apply cevald_if_false.
    * assumption.
    * apply IHcevald.
      reflexivity.
  - apply cevald_while_false.
    assumption.
  - apply cevald_while_true_final with (s' := s').
    * assumption.
    * apply IHcevald1.
      reflexivity.
    * apply IHcevald2.
      reflexivity.
Qed.

Lemma ceval_plus(c : cmd)(s t : state)(m n : nat):
  (ceval c s n = (final t)) -> (ceval c s (n+m) = (final t)).
Proof.
  dependent induction m.
  all: intros.
  - rewrite <- plus_n_O.
    assumption.
  - rewrite <- plus_n_Sm.
    apply ceval_S.
    apply IHm.
    assumption.
Qed.

Lemma bigstep2denot (s s' : state)(c : cmd) :
  | c , s |=> s' -> exists n, ceval c s n = final s'.
Proof.
  intros.
  dependent induction H.
  - exists 1.
    simpl.
    reflexivity.
  - exists 1.
    simpl.
    reflexivity.
  - destruct IHcevalb1 as [m IHcevalb1].
    destruct IHcevalb2 as [n IHcevalb2].
    exists (S (m+n)).
    simpl.
    assert (ceval c1 s (m+n) = (final s')).
    * apply ceval_plus.
      assumption.
    * rewrite H1.
      rewrite PeanoNat.Nat.add_comm.
      apply ceval_plus.
      assumption.
  - destruct IHcevalb as [n IHcevalb].
    exists (S n).
    simpl.
    rewrite H.
    assumption.
  - destruct IHcevalb as [n IHcevalb].
    exists (S n).
    simpl.
    rewrite H.
    assumption.
  - exists 1.
    simpl.
    rewrite H.
    reflexivity.
  - destruct IHcevalb1 as [m IHcevalb1].
    destruct IHcevalb2 as [n IHcevalb2].
    exists (S (m+n)).
    simpl.
    rewrite H.
    rewrite (ceval_plus _ _ _ n _ IHcevalb1).
    rewrite PeanoNat.Nat.add_comm.
    apply ceval_plus.
    assumption.
Qed.

Lemma denot2Bigstep (s s' : state)(c : cmd) :
  (* exists n, ceval c s n = final s' -> | c , s |=> s'. *)
  (exists n, ceval c s n = final s') -> | c , s |=> s'.
Proof.
  intros.
  destruct H as [n H].
  rewrite ceval_cevald in H.
  dependent induction H.
  - apply cevalb_skip.
  - apply cevalb_assign.
  - apply cevalb_seq with (s' := s'0).
    * apply IHcevald1.
      reflexivity.
    * apply IHcevald2.
      reflexivity.
  - apply cevalb_if_true.
    * assumption.
    * apply IHcevald.
      reflexivity.
  - apply cevalb_if_false.
    * assumption.
    * apply IHcevald.
      reflexivity.
  - apply cevalb_while_false.
    assumption.
  - apply cevalb_while_true with (s' := s'0).
    * assumption.
    * apply IHcevald1.
      reflexivity.
    * apply IHcevald2.
      reflexivity.
Qed.
