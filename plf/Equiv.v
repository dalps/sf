(** * Equiv: Program Equivalence *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.
Set Default Goal Selector "!".

(** *** Before You Get Started:

    - Create a fresh directory for this volume. (Do not try to mix the
      files from this volume with files from _Logical Foundations_ in
      the same directory: the result will not make you happy.)  You
      can either start with an empty directory and populate it with
      the files listed below, or else download the whole PLF zip file
      and unzip it.

    - The new directory should contain at least the following files:
         - [Imp.v] (make sure it is the one from the PLF distribution,
           not the one from LF: they are slightly different);
         - [Maps.v] (ditto)
         - [Equiv.v] (this file)
         - [_CoqProject], containing the following line:

           -Q . PLF

    - If you see errors like this...

             Compiled library PLF.Maps (in file
             /Users/.../plf/Maps.vo) makes inconsistent assumptions
             over library Coq.Init.Logic

      ... it may mean something went wrong with the above steps.
      Doing "[make clean]" (or manually removing everything except
      [.v] and [_CoqProject] files) may help.

    - If you are using VSCode with the VSCoq extension, you'll then
      want to open a new window in VSCode, click [Open Folder > plf],
      and run [make].  If you get an error like "Cannot find a
      physical path..." error, it may be because you didn't open plf
      directly (you instead opened a folder containing both lf and
      plf, for example). *)

(** *** Advice for Working on Exercises:

    - Most of the Coq proofs we ask you to do in this chapter are
      similar to proofs that we've provided.  Before starting to work
      on exercises, take the time to work through our proofs (both
      informally and in Coq) and make sure you understand them in
      detail.  This will save you a lot of time.

    - The Coq proofs we're doing now are sufficiently complicated that
      it is more or less impossible to complete them by random
      experimentation or following your nose.  You need to start with
      an idea about why the property is true and how the proof is
      going to go.  The best way to do this is to write out at least a
      sketch of an informal proof on paper -- one that intuitively
      convinces you of the truth of the theorem -- before starting to
      work on the formal one.  Alternately, grab a friend and try to
      convince them that the theorem is true; then try to formalize
      your explanation.

    - Use automation to save work!  The proofs in this chapter can get
      pretty long if you try to write out all the cases explicitly. *)

(* ################################################################# *)
(** * Behavioral Equivalence *)

(** In an earlier chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    in that setting it was very easy to define what it means for a
    program transformation to be correct: it should always yield a
    program that evaluates to the same number as the original.

    To talk about the correctness of program transformations for the
    full Imp language -- in particular, assignment -- we need to
    consider the role of mutable state and develop a more
    sophisticated notion of correctness, which we'll call _behavioral
    equivalence_. *)

(** For example:
      - [X + 2] is behaviorally equivalent to [1 + X + 1]
      - [X - X] is behaviorally equivalent to [0]
      - [(X - 1) + 1] is _not_ behaviorally equivalent to [X]   *)

(* ================================================================= *)
(** ** Definitions *)

(** For [aexp]s and [bexp]s with variables, the definition we want is
    clear: Two [aexp]s or [bexp]s are "behaviorally equivalent" if
    they evaluate to the same result in every state. *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

(** Here are some simple examples of equivalences of arithmetic
    and boolean expressions. *)

Theorem aequiv_example:
  aequiv
    <{ X - X }>
    <{ 0 }>.
Proof.
  intros st. simpl.
  (* induction (st X); try reflexivity; simpl; rewrite IHn; reflexivity. *)
  lia.
Qed.

Theorem bequiv_example:
  bequiv
    <{ X - X = 0 }>
    <{ true }>.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** For commands, the situation is a little more subtle.  We
    can't simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!

    What we need instead is this: two commands are behaviorally
    equivalent if, for any given starting state, they either (1) both
    diverge or (2) both terminate in the same final state.  A compact
    way to express this is "if the first one terminates in a
    particular state then so does the second, and vice versa." *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

(** We can also define an asymmetric variant of this relation: We say
    that [c1] _refines_ [c2] if they produce the same final states
    _when [c1] terminates_ (but [c1] may not terminate in some cases
    where [c2] does). *)

Definition refines (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').

(* ================================================================= *)
(** ** Simple Examples *)

(** For examples of command equivalence, let's start by looking at
    a trivial program equivalence involving [skip]: *)

Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.

(** **** Exercise: 2 stars, standard (skip_right)

    Prove that adding a [skip] after a command results in an
    equivalent program *)

(* 3:42 min *)
Theorem skip_right : forall c,
  cequiv
    <{ c ; skip }>
    c.
Proof.
  intros c st st'. split; intros H.
  - inversion H. subst.
    inversion H5. subst. assumption.
  - eapply E_Seq; [ | constructor]; assumption.
Qed.
(** [] *)

(** Similarly, here is a simple equivalence that optimizes [if]
    commands: *)

Theorem if_true_simple : forall c1 c2,
  cequiv
    <{ if true then c1 else c2 end }>
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + assumption.
    + discriminate.
  - (* <- *)
    apply E_IfTrue.
    + reflexivity.
    + assumption.  Qed.

(** Of course, no (human) programmer would write a conditional whose
    condition is literally [true].  But they might write one whose
    condition is _equivalent_ to true:

    _Theorem_: If [b] is equivalent to [true], then [if b then c1
    else c2 end] is equivalent to [c1].
   _Proof_:

     - ([->]) We must show, for all [st] and [st'], that if [st =[
       if b then c1 else c2 end ]=> st'] then [st =[ c1 ]=> st'].

       Proceed by cases on the rules that could possibly have been
       used to show [st =[ if b then c1 else c2 end ]=> st'], namely
       [E_IfTrue] and [E_IfFalse].

       - Suppose the final rule in the derivation of [st =[ if b
         then c1 else c2 end ]=> st'] was [E_IfTrue].  We then have,
         by the premises of [E_IfTrue], that [st =[ c1 ]=> st'].
         This is exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of [st =[ if b then c1 else c2 end ]=> st'] was [E_IfFalse].
         We then know that [beval st b = false] and [st =[ c2 ]=> st'].

         Recall that [b] is equivalent to [true], i.e., forall [st],
         [beval st b = beval st <{true}> ].  In particular, this means
         that [beval st b = true], since [beval st <{true}> = true].  But
         this is a contradiction, since [E_IfFalse] requires that
         [beval st b = false].  Thus, the final rule could not have
         been [E_IfFalse].

     - ([<-]) We must show, for all [st] and [st'], that if
       [st =[ c1 ]=> st'] then
       [st =[ if b then c1 else c2 end ]=> st'].

       Since [b] is equivalent to [true], we know that [beval st b] =
       [beval st <{true}> ] = [true].  Together with the assumption that
       [st =[ c1 ]=> st'], we can apply [E_IfTrue] to derive
       [st =[ if b then c1 else c2 end ]=> st'].  []

   Here is the formal version of this proof: *)

Theorem if_true: forall b c1 c2,
  bequiv b <{true}>  ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. Qed.

(** **** Exercise: 2 stars, standard, especially useful (if_false) *)

(* 5:09 min *)
Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros b c1 c2 Hb.
  unfold bequiv in Hb; simpl in Hb.
  split; intro H.
  - (* -> *)
    inversion H.
    + simpl in Hb. rewrite Hb in H5. discriminate.
    + subst. assumption.
  - (* <- *)
    apply E_IfFalse; [ | assumption ]; rewrite Hb; reflexivity.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (swap_if_branches)

    Show that we can swap the branches of an [if] if we also negate its
    condition. *)

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  intros b c1 c2. split; intro H;
  inversion H; subst; 
  [ apply E_IfFalse | apply E_IfTrue |
    apply E_IfFalse | apply E_IfTrue ];
  try assumption;
  try (simpl; rewrite H5; reflexivity);
  simpl in H5; destruct beval; try discriminate; reflexivity.
Qed.

  (* Too much compression? Original:
  - inversion H; subst; [ apply E_IfFalse | apply E_IfTrue ];
    try assumption;
    simpl; rewrite H5; reflexivity.
  - inversion H; subst; [ apply E_IfFalse | apply E_IfTrue ];
    try assumption;
    simpl in H5; destruct beval; try discriminate; reflexivity. *)

(** [] *)

(** For [while] loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to [false] is equivalent to [skip],
    while a loop whose guard is equivalent to [true] is equivalent to
    [while true do skip end] (or any other non-terminating program). *)

(** The first of these facts is easy. *)

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. discriminate.
  - (* <- *)
    inversion H. subst.
    apply E_WhileFalse.
    apply Hb.  Qed.

(** **** Exercise: 2 stars, advanced, optional (while_false_informal)

28:09 min

    Write an informal proof of [while_false].

  _Theorem_: If [b] is equivalent to [false], then the command [while b do c end] is equivalent to [skip].

  _Proof_:

    - ([->]) We must show, for all [st] and [st'], that [st =[ while b do c end ]=> st'] implies [st =[ skip ]=> st'], provided that [bequiv b <{ false }>].

    Proceed by case analysis on the constructors that could have been used to derive [st =[ while b do c end ]=> st']. There are two:

      - Suppose [E_WhileFalse] was the final rule used to derive [st =[ while b do c end ]=> st']. By the premises of [E_WhileFalse], we then have that [st = st'] (the loop was never executed). Under this assumption, we can apply [E_Skip] to derive [st' =[ skip ]=> st'].

      - Conversely, suppose the final rule in the derivation of [st =[ while b do c end ]=> st'] is [E_WhileTrue]. This rule assumes that [beval st b = true]. However, recall that we also have that [bequiv b <{ false }>], which ultimately entails [beval st b = false]. Since we have a contradiction, [st =[ while b do c end ]=> st'] could not have been derived with [E_WhileTrue].

    - ([<-]) We must show, for all [st] and [st'], that if we have [bequal b <{false}>] and [st =[ skip ]=> st'], then [st =[ while b do c end ]=> st'].

      The only rule that could have been used to derive [st =[ skip ]=> st'] is [E_Skip], which means that [st = st']. But then the thesis follows from the rule [E_WhileFalse] and the hypothesis that [b] is equivalent to [false] are equivalent.
*)
(** [] *)

(** To prove the second fact, we need an auxiliary lemma stating that
    [while] loops whose guards are equivalent to [true] never
    terminate. *)

(** _Lemma_: If [b] is equivalent to [true], then it cannot be
    the case that [st =[ while b do c end ]=> st'].

    _Proof_: Suppose that [st =[ while b do c end ]=> st'].  We show,
    by induction on a derivation of [st =[ while b do c end ]=> st'],
    that this assumption leads to a contradiction. The only two cases
    to consider are [E_WhileFalse] and [E_WhileTrue], the others
    are contradictory.

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileFalse].  Then by assumption [beval st b = false].  But
      this contradicts the assumption that [b] is equivalent to
      [true].

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileTrue].  We must have that:

      1. [beval st b = true],
      2. there is some [st0] such that [st =[ c ]=> st0] and
         [st0 =[ while b do c end ]=> st'],
      3. and we are given the induction hypothesis that
         [st0 =[ while b do c end ]=> st'] leads to a contradiction,

      We obtain a contradiction by 2 and 3. [] *)

Print E_WhileTrue.
Print ceval_ind.

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for while loops: *)
  - (* E_WhileFalse *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. discriminate.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** Exercise: 2 stars, standard, optional (while_true_nonterm_informal)

~5 min

    Explain what the lemma [while_true_nonterm] means in English.

    A [while] command whose guard neven ceases to evaluate to [true] doesn't terminate. Specifically, this means that there is no pair of states [st] and [st'] nor a command [c] such that executing [while b do c end] on [st] yields [st'], or [st =[ while b do c end ]=> st'] never holds for any [c], [st] and [st'].
*)
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (while_true)

    Prove the following theorem. _Hint_: You'll want to use
    [while_true_nonterm] here. *)

(* 7:40 min *)
Theorem while_true : forall b c,
  bequiv b <{true}>  ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros b c Hb. split; intros contra;
  apply while_true_nonterm in contra;
  try contradiction; try assumption;
  unfold bequiv; reflexivity.
Qed.
(** [] *)

(** A more interesting fact about [while] commands is that any number
    of copies of the body can be "unrolled" without changing meaning.

    Loop unrolling is an important transformation in any real
    compiler: its correctness is of more than academic interest! *)

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse.
      * assumption.
      * apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue.
      * assumption.
      * apply E_Seq with (st' := st'0).
        -- assumption.
        -- assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      * assumption.
      * assumption.
      * assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileFalse. assumption.  Qed.

(** **** Exercise: 2 stars, standard, optional (seq_assoc) *)

(* 11:57 min *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
  intros c1 c2 c3. split; intros Hc.
  - (* -> *)
    inversion Hc; subst.
    inversion H1; subst.
    eapply E_Seq.
    * apply H2.
    * eapply E_Seq.
      + apply H6.
      + apply H4.
  - (* <- *)
    inversion Hc; subst.
    inversion H4; subst.
    eapply E_Seq.
    * eapply E_Seq.
      + apply H1.
      + apply H2.
    * apply H6.
Qed.

(** [] *)

(** Proving program properties involving assignments is one place
    where the fact that program states are treated extensionally
    (e.g., [x !-> m x ; m] and [m] are equal maps) comes in handy. *)

Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Asgn. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (assign_aequiv) *)

(* 33 min - informal proof sketch took most of the time *)
Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a ->
  cequiv <{ skip }> <{ X := a }>.
Proof.
  unfold aequiv. intros X a HXa.
  split; intro Hc.
  - (* -> *)
    inversion Hc; subst.
    assert (Hx : st' =[ X := a ]=> (X !-> aeval st' a ; st'))
    by (apply E_Asgn; reflexivity).
    rewrite <- HXa, t_update_same in Hx. assumption.
  - (* <- *)
    inversion Hc; subst.
    rewrite <- HXa, t_update_same. apply E_Skip.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (equiv_classes) *)

(** Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    Write down your answer below in the definition of
    [equiv_classes]. *)

(* 22:35 min *)

Definition prog_a : com :=
  <{ while X > 0 do
       X := X + 1
     end }>.

Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.

Definition prog_c : com :=
  <{ skip }> .

Definition prog_d : com :=
  <{ while X <> 0 do
       X := (X * Y) + 1
     end }>.

Definition prog_e : com :=
  <{ Y := 0 }>.

Definition prog_f : com :=
  <{ Y := X + 1;
     while X <> Y do
       Y := X + 1
     end }>.

Definition prog_g : com :=
  <{ while true do
       skip
     end }>.

Definition prog_h : com :=
  <{ while X <> X do
       X := X + 1
     end }>.

Definition prog_i : com :=
  <{ while X <> Y do
       X := Y + 1
     end }>.

Definition equiv_classes : list (list com) :=
  [ [ prog_b ; prog_e ] ; (* always converge in the same state *)
    [ prog_c ; prog_h ] ; (* loop never executes *)
    [ prog_a ; prog_d ; prog_i ] ; (* guard might be false in the beginning, otherwise divergent behavior *)
    [ prog_f ; prog_g ] (* guards is always true, program always diverges *)
  ].

(* Do not modify the following line: *)
Definition manual_grade_for_equiv_classes : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Properties of Behavioral Equivalence *)

(** We next consider some fundamental properties of program
    equivalence. *)

(* ================================================================= *)
(** ** Behavioral Equivalence Is an Equivalence *)

(** First, let's verify that the equivalences on [aexps], [bexps], and
    [com]s really are _equivalences_ -- i.e., that they are reflexive,
    symmetric, and transitive.  The proofs are all easy. *)

Lemma refl_aequiv : forall (a : aexp),
  aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof.
  unfold cequiv. intros c st st'. reflexivity.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  rewrite H12. apply H23.
Qed.

(* ================================================================= *)
(** ** Behavioral Equivalence Is a Congruence *)

(** Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded:

                 aequiv a a'
         -------------------------
         cequiv (x := a) (x := a')

              cequiv c1 c1'
              cequiv c2 c2'
         --------------------------
         cequiv (c1;c2) (c1';c2')

    ... and so on for the other forms of commands. *)

(** (Note that we are using the inference rule notation here not
    as part of an inductive definition, but simply to write down some
    valid implications in a readable format. We prove these
    implications below.) *)

(** We will see a concrete example of why these congruence
    properties are important in the following section (in the proof of
    [fold_constants_com_sound]), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the parts that didn't
    change -- i.e., the "proof burden" of a small change to a large
    program is proportional to the size of the change, not the
    program! *)

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.  Qed.

(* 7:18 min - Added by me, just for the sake of exercise *)
Theorem CSeq_congurence : forall c1 c2 c1' c2',
  cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1 ; c2 }> <{ c1' ; c2' }>.
Proof.
  intros c1 c2 c1' c2' Heq1 Heq2.
  unfold cequiv in *.
  split; intros Hc.
  - (* -> *)
    inversion Hc; subst.
    rewrite (Heq1 st st'0) in H1.
    rewrite (Heq2 st'0 st') in H4.
    eapply E_Seq; eassumption.
  - (* <- *)
    inversion Hc; subst.
    erewrite <- Heq1 in H1.
    erewrite <- Heq2 in H4.
    eapply E_Seq; eassumption.
Qed.

Print ceval_ind.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [while] -- that is, if
    [b] is equivalent to [b'] and [c] is equivalent to [c'], then
    [while b do c end] is equivalent to [while b' do c' end].

    _Proof_: Suppose [b] is equivalent to [b'] and [c] is
    equivalent to [c'].  We must show, for every [st] and [st'], that
    [st =[ while b do c end ]=> st'] iff [st =[ while b' do c'
    end ]=> st'].  We consider the two directions separately.

      - ([->]) We show that [st =[ while b do c end ]=> st'] implies
        [st =[ while b' do c' end ]=> st'], by induction on a
        derivation of [st =[ while b do c end ]=> st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileFalse] or [E_WhileTrue].

          - [E_WhileFalse]: In this case, the form of the rule gives us
            [beval st b = false] and [st = st'].  But then, since
            [b] and [b'] are equivalent, we have [beval st b' =
            false], and [E_WhileFalse] applies, giving us
            [st =[ while b' do c' end ]=> st'], as required.

          - [E_WhileTrue]: The form of the rule now gives us [beval st
            b = true], with [st =[ c ]=> st'0] and [st'0 =[ while
            b do c end ]=> st'] for some state [st'0], with the
            induction hypothesis [st'0 =[ while b' do c' end ]=>
            st'].

            Since [c] and [c'] are equivalent, we know that [st =[
            c' ]=> st'0].  And since [b] and [b'] are equivalent,
            we have [beval st b' = true].  Now [E_WhileTrue] applies,
            giving us [st =[ while b' do c' end ]=> st'], as
            required.

      - ([<-]) Similar. [] *)

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  (* WORKED IN CLASS *)

  (* We will prove one direction in an "assert"
     in order to reuse it for the converse. *)
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
             bequiv b b' -> cequiv c c' ->
             st =[ while b do c end ]=> st' ->
             st =[ while b' do c' end ]=> st').
  { unfold bequiv,cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hbe. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hbe. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. }

  intros. split.
  - apply A; assumption.
  - apply A.
    + apply sym_bequiv. assumption.
    + apply sym_cequiv. assumption.
Qed.

(** **** Exercise: 3 stars, standard, optional (CSeq_congruence) *)

(* ~ 8 min - little did I know they'd give it later as an exercise *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  assert (A: forall c1 c1' c2 c2', 
    cequiv c1 c1' -> cequiv c2 c2' ->
    forall st st', st =[ c1 ; c2 ]=> st' -> st =[ c1' ; c2' ]=> st'
  ).
  { intros c1 c1' c2 c2' Heq1 Heq2 st st' Hc.
    inversion Hc; subst.
    rewrite (Heq1 st st'0) in H1;
    rewrite (Heq2 st'0 st') in H4.
    eapply E_Seq; eassumption. }

  intros. split.
  - apply A; assumption.
  - apply A; apply sym_cequiv; assumption.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (CIf_congruence) *)

(* 10:33 min *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  assert (A: forall b b' c1 c1' c2 c2' st st',
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
    st =[ if b then c1 else c2 end ]=> st' ->
    st =[ if b' then c1' else c2' end ]=> st'
  ).
  { intros b b' c1 c1' c2 c2' st st' Heqb Heq1 Heq2 Hc.
    inversion Hc; subst; [ apply E_IfTrue | apply E_IfFalse ];
    try (rewrite <- Heqb; assumption).
    - rewrite <- (Heq1 st st'). assumption.
    - rewrite <- (Heq2 st st'). assumption. }
  
  intros. split; apply A; auto using sym_cequiv, sym_bequiv.
Qed.
(** [] *)

(** For example, here are two equivalent programs and a proof of their
    equivalence using these congruence theorems... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if X = 0 then Y := 0
       else Y := 42 end }>
    (* Program 2: *)
    <{ X := 0;
       if X = 0 then Y := X - X   (* <--- Changed here *)
       else Y := 42 end }>.
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAsgn_congruence. unfold aequiv. simpl.
      symmetry. apply sub_diag.
    + apply refl_cequiv.
Qed.

(** **** Exercise: 3 stars, advanced (not_congr)

    We've shown that the [cequiv] relation is both an equivalence and
    a congruence on commands.  Can you think of a relation on commands
    that is an equivalence but _not_ a congruence?  Write down the
    relation (formally), together with an informal sketch of a proof
    that it is an equivalence but not a congruence. *)

(* FILL IN HERE *)

Definition refl (R : com -> com -> Prop) := forall c, R c c.
Definition sym R := forall (c1 c2 : com), R c1 c2 -> R c2 c1.
Definition trans R := forall (c1 c2 c3 : com), R c1 c2 -> R c2 c3 -> R c1 c3.

(* Haven't really thought out whether this is not a congruence, just winging it. *)
Definition crel c1 c2 : Prop :=
  forall st st' st'',
    st =[ c1 ]=> st' ->
    st =[ c2 ]=> st'' ->
    forall x, st' x = st'' x.

Theorem refl_crel : refl crel.
Proof.
  intros c st st' st'' Hst' Hst'' x.
  assert (Heqst : st' = st'') by (apply (ceval_deterministic c st st' st'' Hst' Hst'')). rewrite Heqst. reflexivity.  Qed.

Theorem sym_crel : sym crel.
Proof.
  unfold crel, sym. intros. rewrite (H st st'' st' H1 H0); reflexivity.  Qed.

Theorem trans_crel : trans crel.
Proof.
  unfold crel. intros c1 c2 c3 Hc12 Hc23 st st' st'' Hc1 Hc2 x.
  rewrite (Hc12 st st' st'').
  - reflexivity.
  - apply Hc1.
  - (* stuck... how do I prove anything about [c2]? *)
Abort.

(** You could proceed like this:
      [assert (Hc2 : exist st'0, st =[ c2 ]=> st'0) by (...).]
    But you can't, because [c2] might diverge (loop endlessly).
    Since you can't really know how [c2] behaves, transitivity is not
    provable, and therefore [crel] is _not_ an equivalence.
    
    Come up with another relation to solve the exercise.
    Nonetheless, this helped me understand why [cequiv] was defined
    in a different way. *)

(* Do not modify the following line: *)
Definition manual_grade_for_not_congr : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Program Transformations *)

(** A _program transformation_ is a function that takes a program as
    input and produces a modified program as output.  Compiler
    optimizations such as constant folding are a canonical example,
    but there are many others. *)

(** A program transformation is said to be _sound_ if it preserves the
    behavior of the original program. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ================================================================= *)
(** ** The Constant-Folding Transformation *)

(** An expression is _constant_ if it contains no variable references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | <{ a1 + a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }>
  = <{ 3 * X }>.
Proof. reflexivity. Qed.

(** Note that this version of constant folding doesn't do other
    "obvious" things like eliminating trivial additions (e.g.,
    rewriting [0 + X] to just [X]).: we are focusing attention on a
    single optimization for the sake of simplicity.

    It is not hard to incorporate other ways of simplifying
    expressions -- the definitions and proofs just get longer.  We'll
    consider optimizations in the exercises. *)

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
Proof. reflexivity. Qed.

(** Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq], [BNeq], and [BLe] cases); we can also look for constant
    _boolean_ expressions and evaluate them in-place as well. *)

Print beval.
Print bexp_ind.
Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>        => <{true}>
  | <{false}>       => <{false}>
  | <{ a1 = a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if negb (n1 =? n2) then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end
  | <{ ~ b1 }>  =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }>  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
Proof. reflexivity. Qed.

(** To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }>  =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if (X - Y) = (2 + 4) then skip
       else Y := 0 end;
       if 0 <= (4 - (2 + 1)) then Y := 0
       else skip end;
       while Y = 0 do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if (X - Y) = 6 then skip
       else Y := 0 end;
       Y := 0;
       while Y = 0 do
         X := X + 1
       end }>.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

(** Here's the proof for arithmetic expressions: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (<{ a1 + a2 }>)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** Exercise: 3 stars, standard, optional (fold_bexp_Eq_informal)

    Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp b],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [a1 = a2].

   In this case, we must show

       beval st <{ a1 = a2 }>
     = beval st (fold_constants_bexp <{ a1 = a2 }>).

   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have

           fold_constants_bexp <{ a1 = a2 }>
         = if n1 =? n2 then <{true}> else <{false}>

       and

           beval st <{a1 = a2}>
         = (aeval st a1) =? (aeval st a2).

       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know

           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1

       and

           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,

       so

           beval st <{a1 = a2}>
         = (aeval a1) =? (aeval a2)
         = n1 =? n2.

       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that

           beval st (if n1 =? n2 then <{true}> else <{false}>)
         = if n1 =? n2 then beval st <{true}> else beval st <{false}>
         = if n1 =? n2 then true else false
         = n1 =? n2.

       So

           beval st (<{ a1 = a2 }>)
         = n1 =? n2.
         = beval st (if n1 =? n2 then <{true}> else <{false}>),

       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show

           beval st <{a1 = a2}>
         = beval st (<{ (fold_constants_aexp a1) =
                         (fold_constants_aexp a2) }>),

       which, by the definition of [beval], is the same as showing

           (aeval st a1) =? (aeval st a2)
         = (aeval st (fold_constants_aexp a1)) =?
                   (aeval st (fold_constants_aexp a2)).

       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       completing the case.  [] *)

(* ~1:15 min - Uh-oh... I did look at the formal proof beforehand. Is that failing the exercise? At best, I made it 1 star now. At worst, I have defeated its purpose. *)

Print beval.
Print BEq.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  (* Bad attempt at shortening the proof. Perhaps Ltac is more suited for this case.
  assert (A : forall (op : nat -> nat -> bool) (constr : aexp -> aexp -> bexp) (a1 a2 : aexp) (st : state),
    beval st (constr a1 a2) = beval st (fold_constants_bexp (constr a1 a2))
  ). {  } *)
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BNeq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Ea1'.
    remember (fold_constants_aexp a2) as a2' eqn:Ea2'.
    replace (aeval st a1) with (aeval st a1')
      by (rewrite Ea1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2')
      by (rewrite Ea2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1', a2';
      (* Most cases are immediate *) try reflexivity.
      (* The interesting case is when both [a1] and [a2] are folded into constants. *)
        simpl. destruct (n <=? n0); reflexivity.
  - (* BGt - exactly the same *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Ea1'.
    remember (fold_constants_aexp a2) as a2' eqn:Ea2'.
    replace (aeval st a1) with (aeval st a1')
      by (rewrite Ea1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2')
      by (rewrite Ea2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1', a2';
      (* Most cases are immediate *) try reflexivity.
      (* The interesting case is when both [a1] and [a2] are folded into constants. *)
        simpl. destruct (n <=? n0); reflexivity.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl. (* breaks down product scrutinees *)
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (fold_constants_com_sound)

    Complete the [while] case of the following proof. *)

(* 19:45 min to internalize proof + 4:32 min for while *)
Print fold_constants_com.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound, cequiv. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAsgn_congruence.
              apply fold_constants_aexp_sound.
  - (* ; *) apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. } (* pronounce: [b] and [fold_constants_bexp b] are equivalent by the soundness of the transformation on boolean expressions. *)
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* ^ (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - (* while *)
    assert (Heqb : bequiv b (fold_constants_bexp b))
      by (apply fold_constants_bexp_sound).
    destruct (fold_constants_bexp b);
    [ apply while_true; assumption
    | apply while_false; assumption | | | | | | ];
    apply CWhile_congruence; assumption.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Soundness of (0 + n) Elimination, Redux *)

(** **** Exercise: 4 stars, standard, optional (optimize_0plus_var)

    Recall the definition [optimize_0plus] from the [Imp] chapter
    of _Logical Foundations_:

    Fixpoint optimize_0plus (a:aexp) : aexp :=
      match a with
      | ANum n =>
          ANum n
      | <{ 0 + a2 }> =>
          optimize_0plus a2
      | <{ a1 + a2 }> =>
          <{ (optimize_0plus a1) + (optimize_0plus a2) }>
      | <{ a1 - a2 }> =>
          <{ (optimize_0plus a1) - (optimize_0plus a2) }>
      | <{ a1 * a2 }> =>
          <{ (optimize_0plus a1) * (optimize_0plus a2) }>
      end.

   Note that this function is defined over the old version of [aexp]s,
   without states.

   Write a new version of this function that deals with variables (by
   leaving them alone), plus analogous ones for [bexp]s and commands:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com
*)

Print aexp.

(* 11:39 min *)
Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | <{ 0 + a2 }> => optimize_0plus_aexp a2
  | <{ a1 + a2 }> =>
      <{ optimize_0plus_aexp a1 + optimize_0plus_aexp a2 }>
  | <{ a1 - a2 }> =>
      <{ optimize_0plus_aexp a1 - optimize_0plus_aexp a2 }>
  | <{ a1 * a2 }> =>
      <{ optimize_0plus_aexp a1 * optimize_0plus_aexp a2 }>
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | <{ true }> => <{ true }>
  | <{ false }> => <{ false }>
  | <{ a1 = a2 }> =>
      <{ optimize_0plus_aexp a1 = optimize_0plus_aexp a2 }>
  | <{ a1 <> a2 }> =>
      <{ optimize_0plus_aexp a1 <> optimize_0plus_aexp a2 }>
  | <{ a1 <= a2 }> =>
      <{ optimize_0plus_aexp a1 <= optimize_0plus_aexp a2 }>
  | <{ a1 > a2 }> =>
      <{ optimize_0plus_aexp a1 > optimize_0plus_aexp a2 }>
  | <{ ~b }> =>
      <{ ~ optimize_0plus_bexp b }>
  | <{ a1 && a2 }> =>
      <{ optimize_0plus_bexp a1 && optimize_0plus_bexp a2 }>
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | <{ skip }> => <{ skip }>
  | <{ x := a }> => <{ x := optimize_0plus_aexp a }>
  | <{ c1 ; c2 }> =>
      <{ optimize_0plus_com c1 ; optimize_0plus_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      <{  if optimize_0plus_bexp b
          then optimize_0plus_com c1
          else optimize_0plus_com c2 end }>
  | <{ while b do c end }> =>
      <{  while optimize_0plus_bexp b
          do optimize_0plus_com c end }>
  end.

Example test_optimize_0plus:
    optimize_0plus_com
       <{ while X <> 0 do X := 0 + X - 1 end }>
  =    <{ while X <> 0 do X := X - 1 end }>.
Proof.
  simpl. reflexivity. Qed.

(** Prove that these three functions are sound, as we did for
    [fold_constants_*].  Make sure you use the congruence lemmas in the
    proof of [optimize_0plus_com] -- otherwise it will be _long_! *)

(* 18:24 min *)
Theorem optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. induction a; simpl;
  (* ANum and AId *)
  try (apply refl_aequiv); unfold aequiv in *;
  try (intro; simpl; rewrite <- IHa1, <- IHa2; reflexivity).
  - (* APlus *)
    destruct a1 eqn:Ea1; simpl in *; intro.
    * destruct n; simpl; rewrite <- IHa2; reflexivity.
    * rewrite <- IHa2; reflexivity.
    * simpl. rewrite <- IHa1. rewrite <- IHa2. reflexivity.
    * simpl. rewrite <- IHa1. rewrite <- IHa2. reflexivity.
    * simpl. rewrite <- IHa1. rewrite <- IHa2. reflexivity.
Qed.

(* 12:21 min *)
Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  intro b. induction b; simpl;
  try (apply refl_bequiv);
  unfold bequiv in *; intro st; simpl; 
  try rewrite <- IHb1;
  try rewrite <- IHb2;
  try rewrite <- IHb;
  try reflexivity;
  rewrite <- optimize_0plus_aexp_sound;
  rewrite <- optimize_0plus_aexp_sound; reflexivity.
Qed.

(* 8 min circa *)
Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  intros c. induction c; intros st st'.
  - apply refl_cequiv.
  - apply CAsgn_congruence.
    unfold aequiv. intro. rewrite optimize_0plus_aexp_sound.
    reflexivity.
  - apply CSeq_congruence; unfold cequiv in *; intros.
    + rewrite IHc1. reflexivity.
    + rewrite IHc2. reflexivity.
  - apply CIf_congruence; auto using optimize_0plus_bexp_sound.
  - apply CWhile_congruence; auto using optimize_0plus_bexp_sound.
Qed.

(** Finally, let's define a compound optimizer on commands that first
    folds constants (using [fold_constants_com]) and then eliminates
    [0 + n] terms (using [optimize_0plus_com]). *)

Definition optimizer (c : com) := optimize_0plus_com (fold_constants_com c).

(** Prove that this optimizer is sound. *)

(* 10:34 min *)
Theorem optimizer_sound :
  ctrans_sound optimizer.
Proof.
  intros c. unfold optimizer. 
  apply trans_cequiv with (fold_constants_com c).
  - apply fold_constants_com_sound.
  - apply optimize_0plus_com_sound.
Qed.

(** [] *)

(* ################################################################# *)
(** * Proving Inequivalence *)

(** Next, let's look at some programs that are _not_ equivalent. *)

(** Suppose that [c1] is a command of the form

       X := a1; Y := a2

    and [c2] is the command

       X := a1; Y := a2'

    where [a2'] is formed by substituting [a1] for all occurrences
    of [X] in [a2].

    For example, [c1] and [c2] might be:

       c1  =  (X := 42 + 53;
               Y := Y + X)
       c2  =  (X := 42 + 53;
               Y := Y + (42 + 53))

    Clearly, this _particular_ [c1] and [c2] are equivalent.  Is this
    true in general? *)

    (* No. These [c1] and [c2] are not equivalent:
    
       c1  =  (X := X + 42 + 53;
               Y := Y + X)
       c2  =  (X := X + 42 + 53;
               Y := [X -> a1]a2
                    Y + (X + 42 + 53))

    Generally, when [a1] references [X], [c1] and [c2] are not equivalent. This is _not> because the substitution keeps replacing [X] infinitely often, but because [X] has different values when it is evaluated in [a1] and [a2']. *)

(** We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. *)

(** More formally, here is the function that substitutes an arithmetic
    expression [u] for each occurrence of a given variable [x] in
    another expression [a]: *)

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId x'       =>
      if String.eqb x x' then u else AId x'
  | <{ a1 + a2 }>  =>
      <{ (subst_aexp x u a1) + (subst_aexp x u a2) }>
  | <{ a1 - a2 }> =>
      <{ (subst_aexp x u a1) - (subst_aexp x u a2) }>
  | <{ a1 * a2 }>  =>
      <{ (subst_aexp x u a1) * (subst_aexp x u a2) }>
  end.

Example subst_aexp_ex :
  subst_aexp X <{42 + 53}> <{Y + X}>
  = <{ Y + (42 + 53)}>.
Proof. simpl. reflexivity. Qed.

Compute subst_aexp X <{X + 42}> <{Y + X}>.

(** And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)

Definition subst_equiv_property : Prop := forall x1 x2 a1 a2,
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.

(** Sadly, the property does _not_ always hold.

    Here is a counterexample:

       X := X + 1; Y := X

    If we perform the substitution, we get

       X := X + 1; Y := X + 1

    which clearly isn't equivalent. *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember <{ X := X + 1;
              Y := X }>
      as c1.
  remember <{ X := X + 1;
              Y := X + 1 }>
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  clear Contra.

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = (Y !-> 1 ; X !-> 1)
        st2 = (Y !-> 2 ; X !-> 1). *)
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Asgn; reflexivity).
  clear Heqc1 Heqc2.

  unfold cequiv in *.

  apply H in H1.
  clear H.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  clear H1 H2.

  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. discriminate. Qed.

(** **** Exercise: 4 stars, standard, optional (better_subst_equiv)

    The equivalence we had in mind above was not complete nonsense --
    in fact, it was actually almost right.  To make it correct, we
    just need to exclude the case where the variable [X] occurs in the
    right-hand side of the first assignment statement. *)

(* The transformation function is unchanged. All occurrences of a variable that doesn't reference itself in its definition are good to be replaced. *)

(* A property on aexps: [a] does not contain the string [x] *)
Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>).

(* If [a] doesn't reference the variable [x], the evaluation of [a] in [st] is indifferent of the value of [x] in [st]. *)

(* 27:03 min *)
Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros x st a ni Hvnu.
  induction Hvnu; simpl;
  (* Most cases follow from the properties of [aeval] and the IH *)
  auto;
  (* [VNUId] is the only interesting case *)
  apply t_update_neq; assumption.
Qed.


(** Using [var_not_used_in_aexp], formalize and prove a correct version
    of [subst_equiv_property]. *)

(* ~ 1h 20min (includes lunch break) *)
Theorem subst_equiv_property' : forall x1 a1 x2 a2,
  var_not_used_in_aexp x1 a1 ->
  cequiv
    <{ x1 := a1 ; x2 := a2 }>
    <{ x1 := a1 ; x2 := subst_aexp x1 a1 a2 }>.
Proof.
  intros x1 a1 x2 a2 Hvnu st st'. split; intros Hc;
  inversion Hc; subst; inversion H1; subst.
  - eapply E_Seq.
    + apply H1.
    + inversion H4; subst. eapply E_Asgn.
      clear Hc H4 H1 x2.
      induction a2;
      try reflexivity;
      try (simpl; rewrite IHa2_1, IHa2_2; reflexivity).
      * (* AId *) simpl. destruct (x1 =? x)%string eqn:Evar;
        try reflexivity.
        apply String.eqb_eq in Evar. subst x.
        rewrite t_update_eq.
        (* Cool, does ever [a1] mention [x]? No. *)
        apply aeval_weakening. assumption.
  - eapply E_Seq.
    + apply H1.
    + inversion H4; subst. eapply E_Asgn.
      clear Hc H4 H1 x2.
      symmetry.
      induction a2;
      try reflexivity;
      try (simpl; rewrite IHa2_1, IHa2_2; reflexivity).
      * (* AId *) simpl. destruct (x1 =? x)%string eqn:Evar;
        try reflexivity.
        apply String.eqb_eq in Evar. subst x.
        rewrite t_update_eq.
        apply aeval_weakening. assumption.
Qed.

  (* First tempting attempt:
  
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CAsgn_congruence. intro st''.
    clear x2 st st'. rename st'' into st.
    induction a2.
    * (* ANum *) reflexivity.
    * (* AId *) simpl. destruct (x1 =? x)%string eqn:Evar;
      try reflexivity.
      apply String.eqb_eq in Evar. subst x.
      nope *)
(** [] *)

(** **** Exercise: 3 stars, standard (inequiv_exercise)

    Prove that an infinite loop is not equivalent to [skip] *)

(* 6:52 min *)
Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
  intros contra.
  edestruct contra.
  assert (H1 : empty_st =[ skip ]=> empty_st) by (apply E_Skip).
  apply H0 in H1. apply loop_never_stops in H1.
  contradiction.
Qed.

(** [] *)

(* ################################################################# *)
(** * Extended Exercise: Nondeterministic Imp *)

(** As we have seen (in theorem [ceval_deterministic] in the [Imp]
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment

      x = 0;
      f(++x, x)

    might call [f] with arguments [(1, 0)] or [(1, 1)], depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives the compiler writer useful
    freedom.

    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an _arbitrary_ number to the variable [X],
    nondeterministically. For example, after executing the program:

      HAVOC Y;
      Z := Y * 2

    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes -- just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do [HAVOC] roughly corresponds
    to an uninitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ (``Imp extended with [HAVOC]''). *)

Module Himp.

(** To formalize Himp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                (* <--- NEW *)

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(** **** Exercise: 2 stars, standard (himp_ceval)

    Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)

(* 8:31 min *)

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr,
          st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Havoc : forall st n x,
      st =[ havoc x ]=> (x !-> n ; st)

  where "st =[ c ]=> st'" := (ceval c st st').

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).
Proof. constructor. Qed.

Example havoc_example2 :
  empty_st =[ skip; havoc Z ]=> (Z !-> 42).
Proof. eapply E_Seq; constructor. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_Check_rule_for_HAVOC : option (nat*string) := None.
(** [] *)

(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

(** **** Exercise: 3 stars, standard (havoc_swap)

    Are the following two programs equivalent? *)

Definition pXY :=
  <{ havoc X ; havoc Y }>.

Definition pYX :=
  <{ havoc Y; havoc X }>.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)

(* 57:03 min *)
Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
  left. intros st st'; unfold pXY, pYX. split; intro Hc;
  inversion Hc; subst;
  inversion H1; subst;
  inversion H4; subst;
  clear Hc H1 H4.
  - apply E_Seq with (st' := (Y !-> n0 ; st)).
    + apply E_Havoc.
    + rewrite t_update_permute.
      * apply E_Havoc.
      * apply String.eqb_neq. reflexivity.
  - apply E_Seq with (st' := (X !-> n0 ; st)).
    + apply E_Havoc.
    + rewrite t_update_permute.
      * apply E_Havoc.
      * apply String.eqb_neq. reflexivity.
Qed.

  (* I thought they weren't equivalent  at first...
     I'm still not convinced they are.

    ~~~ I know understand: [cequiv c1 c2] for Himp states that the commands [c1] and [c2] share the same _set_ of terminating outcomes. Every state resulting from the execution of [c1] is included in the possibe states resulting from [c2] and vice-reversa!
     
  right. unfold cequiv, pXY, pYX. intros Hequiv.
  assert (A : forall x y, exists nx ny,
    empty_st =[ havoc x ; havoc y ]=> (y !-> ny ; x !-> nx ; empty_st)).
  {
    intros x y. exists 1, 0. eapply E_Seq.
    - apply E_Havoc with (n := 1).
    - apply E_Havoc with (n := 0).
  }
  destruct (A X Y) as [nx [ny H]].
  destruct (A Y X) as [nx' [ny' H']].
  apply Hequiv in H.

  You don't have [ceval_deterministic] in Himp! *)

  (* Hint: You may want to use [t_update_permute] at some point,
     in which case you'll probably be left with [X <> Y] as a
     hypothesis. You can use [discriminate] to discharge this. *)

(** [] *)

(** **** Exercise: 4 stars, standard, optional (havoc_copy)

    Are the following two programs equivalent? *)

Definition ptwice :=
  <{ havoc X; havoc Y }>.

Definition pcopy :=
  <{ havoc X; Y := X }>.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)

(* ~ 4:20 hours (shave off ~1:30 of lunch) - Not proud of this one *)
Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof.
  unfold cequiv, ptwice, pcopy.
  right. intros Contra.
  assert (empty_st =[ havoc X ; havoc Y ]=> (Y !-> 1 ; X !-> 0))
    as A by (eauto using E_Seq, E_Havoc).
  apply Contra in A.
  inversion A; subst.
  inversion H1; subst.
  inversion H4; subst.
  clear A H1 H4 Contra. rename H5 into Contra.
  simpl in Contra.
  rewrite t_update_eq in Contra. (* I'm so blind *)
  assert (Hn1 : (X !-> n ; Y !-> n) X = (X !-> 0 ; Y !-> 1) X).
  { rewrite
      t_update_permute,
      t_update_permute with (v1 := 0);
    try discriminate;
    congruence. }
  assert (Hn2 : (Y !-> n; X !-> n) Y = (Y !-> 1; X !-> 0) Y) by congruence.
  rewrite 2 t_update_eq in Hn1, Hn2.
  congruence.
Qed.

  (* See why [(->)] is unprovable?
  left. intros st st'. split; intros Hc;
  inversion Hc; subst;
  inversion H1; subst;
  inversion H4; subst;
  clear Hc H1 H4.
  - apply E_Seq with (st' := (X !-> n0 ; st)).
    + apply E_Havoc.
    + apply E_Asgn. <-- stuck *)
(** [] *)

(** The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    [cequiv] says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)

(** **** Exercise: 4 stars, advanced (p1_p2_term)

    Consider the following commands: *)

Definition p1 : com :=
  <{ while ~ (X = 0) do
       havoc Y;
       X := X + 1
     end }>.

Definition p2 : com :=
  <{ while ~ (X = 0) do
       skip
     end }>.

(** Intuitively, [p1] and [p2] have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of [p1] and
    [p2] individually with these lemmas: *)

(* 38:46 min *)
Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof.
  unfold p1. intros st st' Hx Contra.
  remember (<{ while ~ X = 0 do havoc Y; X := X + 1 end }> )
    as cwhile eqn:Ecwhile.
  induction Contra; try discriminate; inversion Ecwhile; subst.
  - (* E_WhileFalse *)
    simpl in H.
    apply negb_false_iff, eqb_eq in H.
    contradiction.
  - (* E_WhileTrue *)
    clear H IHContra1.
    (* the loop condition holds after running the body *)
    inversion Contra1; subst.
    inversion H1; subst.
    inversion H4; subst.
    remember (X !-> aeval (Y !-> n; st) <{ X + 1 }>; Y !-> n; st) as st' eqn:Est'.
    simpl in Est'.
    assert (A : st' X <> 0).
    { rewrite Est', t_update_eq, t_update_neq;
      try discriminate.
      rewrite add_comm; discriminate. }
    auto.
Qed.

(* 8:07 min *)
Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
  unfold p2.
  intros st st' Hx Contra.
  remember (<{ while ~ X = 0 do skip end }>) as cwhile eqn:Ecwhile.
  induction Contra; try discriminate; inversion Ecwhile; subst.
  - (* E_WhileFalse *)
    simpl in H.
    apply negb_false_iff, eqb_eq in H.
    contradiction.
  - (* E_WhileTrue *)
    clear H IHContra1.
    (* [skip] has no effect on the loop guard *)
    inversion Contra1; subst.
    auto.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (p1_p2_equiv)

    Use these two lemmas to prove that [p1] and [p2] are actually
    equivalent. *)

(* 10:56 min (->) + 7:15 min (<-) (spent some time trying to golf) *)
Theorem p1_p2_equiv : cequiv p1 p2.
Proof.
  unfold p1, p2. intros st st'. split; intros Hc;
  destruct (eqb_spec (st X) 0) as [HX | HX]; (* don't specify an equation when you destruct a [reflect] lemma *)
  try (inversion Hc; subst;
      [ apply E_WhileFalse; assumption
      | simpl in H1; rewrite HX in H1; discriminate ]);
  [ apply (p1_may_diverge st st') in HX
  | apply (p2_may_diverge st st') in HX ];
  apply HX in Hc; contradiction.
Qed.

(** [] *)

Lemma t_empty_0 : forall x, empty_st x = 0.
Proof. reflexivity. Qed.

(** **** Exercise: 4 stars, advanced (p3_p4_inequiv)

    Prove that the following programs are _not_ equivalent.  (Hint:
    What should the value of [Z] be when [p3] terminates?  What about
    [p4]?) *)

Definition p3 : com :=
  <{ Z := 1;
     while X <> 0 do
       havoc X;
       havoc Z
     end }>.

Definition p4 : com :=
  <{ X := 0;
     Z := 1 }>.

(* 1:19:06 hours - pats on the back for not reading the hint! *)
Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof.
  unfold cequiv, p3, p4. intro Contra.

  assert (A :
    (X !-> 1) =[ p3 ]=> (Z !-> 2 ; X !-> 0 ; Z !-> 1 ; X !-> 1)).
  { unfold p3. eapply E_Seq.
    - apply E_Asgn. simpl. reflexivity.
    - apply E_WhileTrue with (st' := (Z !-> 2 ; X !-> 0 ; Z !-> 1 ; X !-> 1)).
      + reflexivity.
      + apply E_Seq with (st' := (X !-> 0 ; Z !-> 1 ; X !-> 1)).
        * apply (E_Havoc (Z !-> 1; X !-> 1) 0).
        * apply E_Havoc.
      + apply E_WhileFalse. reflexivity. }

  apply Contra in A.

  assert (M :
    (Z !-> 2; X !-> 0; Z !-> 1; X !-> 1) = (Z !-> 2; X !-> 0; X !-> 1)).
  { clear Contra A.
    rewrite t_update_permute; try discriminate.
    replace (Z !-> 2; X !-> 0; X !-> 1)
      with (X !-> 0 ; Z !-> 2; X !-> 1)
      by (rewrite t_update_permute; [ reflexivity | discriminate ]).
    f_equal. rewrite t_update_shadow. reflexivity. }

  rewrite M in A.

  clear Contra M.
  inversion A; subst.
  inversion H1; subst.
  inversion H4; subst.
  
  clear A H1 H4.
  simpl in H5.
  assert (Contra :
    (Z !-> 1; X !-> 0; X !-> 1) Z = (Z !-> 2; X !-> 0; X !-> 1) Z)
    by congruence.
  cbn in Contra. discriminate.
Qed.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv)

    Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of [cequiv] for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if the set of possible terminating
    states is the same for both programs when given a same starting state
    [st].  If [p5] terminates, what should the final state be? Conversely,
    is it always possible to make [p5] terminate?) *)

Definition p5 : com :=
  <{ while X <> 1 do
       havoc X
     end }>.

Definition p6 : com :=
  <{ X := 1 }>.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

End Himp.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, optional (swap_noninterfering_assignments)

    (Hint: You may or may not -- depending how you approach it -- need
    to use [functional_extensionality] explicitly for this one.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    <{ l1 := a1; l2 := a2 }>
    <{ l2 := a2; l1 := a1 }>.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (for_while_equiv)

    This exercise extends the optional [add_for_loop] exercise from
    the [Imp] chapter, where you were asked to extend the language
    of commands with C-style [for] loops.  Prove that the command:

      for (c1; b; c2) {
          c3
      }

    is equivalent to:

       c1;
       while b do
         c3;
         c2
       end
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 4 stars, advanced, optional (capprox)

    In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program [c1] _approximates_ a program [c2] when, for each of
    the initial states for which [c1] terminates, [c2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

(** For example, the program

  c1 = while X <> 1 do
         X := X - 1
       end

    approximates [c2 = X := 1], but [c2] does not approximate [c1]
    since [c1] does not terminate when [X = 0] but [c2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)

(** Find two programs [c3] and [c4] such that neither approximates
    the other. *)

Definition c3 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Definition c4 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof. (* FILL IN HERE *) Admitted.

(** Find a program [cmin] that approximates every other program. *)

Definition cmin : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof. (* FILL IN HERE *) Admitted.

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

Definition zprop (c : com) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(* 2024-01-02 21:54 *)
