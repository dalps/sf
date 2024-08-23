(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.

    In this chapter, we bring yet another new tool into the mix:
    _inductively defined propositions_.

    To begin, some examples... *)

(* ================================================================= *)
(** ** Example: The Collatz Conjecture *)

(** The _Collatz Conjecture_ is a famous open problem in number
    theory.

    Its statement is quite simple.  First, we define a function [f]
    on numbers, as follows: *)

Fixpoint div2 (n : nat) :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Compute div2 7.
Compute div2 8.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.

Compute map f [0;1;2;3;4;5].
Compute fold (fun _ acc => match acc with
| [] => []
| h :: t => f h :: acc
end
) (repeat 0 100) [12].

(** Next, we look at what happens when we repeatedly apply [f] to
    some given starting number.  For example, [f 12] is [6], and [f
    6] is [3], so by repeatedly applying [f] we get the sequence
    [12, 6, 3, 10, 5, 16, 8, 4, 2, 1].

    Similarly, if we start with [19], we get the longer sequence
    [19, 58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5,
    16, 8, 4, 2, 1].

    Both of these sequences eventually reach [1].  The question
    posed by Collatz was: Is the sequence starting from _any_
    natural number guaranteed to reach [1] eventually? *)

(** To formalize this question in Coq, we might try to define a
    recursive _function_ that calculates the total number of steps
    that it takes for such a sequence to reach [1]. *)

Fail Fixpoint reaches_1_in (n : nat) :=
  if n =? 1 then true
  else 1 + reaches_1_in (f n).

(** This definition is rejected by Coq's termination checker, since
    the argument to the recursive call, [f n], is not "obviously
    smaller" than [n].

    Indeed, this isn't just a pointless limitation: functions in Coq
    are required to be total, to ensure logical consistency.

    Moreover, we can't fix it by devising a more clever termination
    checker: deciding whether this particular function is total
    would be equivalent to settling the Collatz conjecture! *)

(** Fortunately, there is another way to do it: We can express the
    concept "reaches [1] eventually" as an _inductively defined
    property_ of numbers: *)

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more (n : nat) : Collatz_holds_for (f n) -> Collatz_holds_for n.
(* Collatz_holds_for n <===> the sequence starting from n eventually reaches 1 *)

(** What we've done here is to use Coq's [Inductive] definition
    mechanism to characterize the property "Collatz holds for..." by
    stating two different ways in which it can hold: (1) Collatz holds
    for [1] and (2) if Collatz holds for [f n] then it holds for
    [n]. *)

(** For particular numbers, we can now argue that the Collatz sequence
    reaches [1] like this (again, we'll go through the details of how
    it works a bit later in the chapter): *)

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_done.  Qed.

(** The Collatz conjecture then states that the sequence beginning
    from _any_ number reaches [1]: *)

Conjecture collatz : forall n, Collatz_holds_for n.

(** If you succeed in proving this conjecture, you've got a bright
    future as a number theorist!  But don't spend too long on it --
    it's been open since 1937. *)

(* ================================================================= *)
(** ** Example: Ordering *)

(** A binary _relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition
    about pairs of elements of [X].  *)

(** For example, one familiar binary relation on [nat] is [le], the
    less-than-or-equal-to relation.  We've already seen how to define
    it as a boolean computation.  Here is a "direct" propositional
    definition. *)

Module LePlayground.

(** The following definition says that there are two ways to
    show that one number is less than or equal to another: either
    observe that they are the same number, or, if the second has the
    form [S m], give evidence that the first is less than or equal to
    [m]. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

End LePlayground.

Module LePlayground1.

(** (By "reserving" the notation before defining the [Inductive], we
    can use it in the definition.) *)

Reserved Notation "n <= m" (at level 70).

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : n <= n
  | le_S (n m : nat) : n <= m -> n <= (S m)

  where "n <= m" := (le n m).

End LePlayground1.

(* ================================================================= *)
(** ** Example: Transitive Closure *)

(** As another example, the _transitive closure_ of a relation [R]
    is the smallest relation that contains [R] and that is
    transitive.  *)

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

(** For example, suppose we define a "parent of" relation on a group
    of people... *)

Inductive Person : Type := Sage | Cleo | Ridley | Moss | Maria.

Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

(** Then we can define "ancestor of" as its transitive closure: *)

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of1 : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM. Qed.

(** **** Exercise: 1 star, standard, optional (close_refl_trans)

    How would you modify this definition so that it defines _reflexive
    and_ transitive closure?  How about reflexive, symmetric, and
    transitive closure? *)

(* FILL IN HERE

  The reflexive closure adds a pair (x,x) for all (x : X) to the original relation. Simple.

  The symmetric closure builds on top of a relation so that for all (x y : X), if the pair (x,y) belonged to the original relation, then (y,x) also belongs to the symmetric closure.

    [] *)

(* 10min + 30min playing with examples *)

Inductive clos_refl_trans {X : Type} (R : X->X->Prop) : X->X->Prop :=
  | t_t (x y : X) : clos_trans R x y -> clos_refl_trans R x y
  | t_refl (x : X) : clos_refl_trans R x x.

Inductive clos_refl_symm_trans {X : Type} (R : X->X->Prop) : X->X->Prop :=
  | t_rt (x y : X) : clos_refl_trans R x y -> clos_refl_symm_trans R x y
  | t_symm (x y : X) : clos_refl_symm_trans R x y -> clos_refl_symm_trans R y x.
  (*
    I'm not so confident in this definition...
    Don't we miss out on some pairs?
    
    If R x y and R y z, the transitive closure of R, TR, has R x z
    Now, the symmetric transitive closure STR, has R z x, R z y, R y x.

    Consider instead the case where R x y and R z y. TR doesn't have R x z!!
    The symmetric-transitive closure introduces R y z, and consequently it should also have R x z; but under this definition STR doesn't have R x z, because the symmetric pairs are introduced on top of the transitive closure.

    So yeah, we miss out on some pairs.

    The transitive closure doesn't apply to the pairs introduced by t_symm!

    The follwing examples illustrates its incompletess:
  *)

Inductive parent_of' : Person -> Person -> Prop :=
  po_SC' : parent_of' Sage Cleo
| po_SR' : parent_of' Sage Ridley
| po_CM' : parent_of' Cleo Moss
| po_MR : parent_of' Maria Ridley.

Definition ancestor_of'''_bad : Person -> Person -> Prop :=
  clos_refl_symm_trans parent_of'.

Example ancestor_of'''1 : ancestor_of'''_bad Sage Maria.
Proof. unfold ancestor_of'''_bad. apply t_rt. apply t_t. apply t_trans with Ridley. apply t_step. apply po_SR'.
  apply t_step. (* Stuck... in order to use transitivity we had to descend to the bare relation, now it's impossible to apply symmetricity! *) Abort.

(* correct definition *)
Inductive clos_refl_symm_trans' {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | s_step (x y : X) :
      R x y ->
      clos_refl_symm_trans' R x y
  | s_refl (x : X) : clos_refl_symm_trans' R x x
  | s_symm (x y : X) : clos_refl_symm_trans' R x y -> clos_refl_symm_trans' R y x
  | s_trans (x y z : X) :
      clos_refl_symm_trans' R x y ->
      clos_refl_symm_trans' R y z ->
      clos_refl_symm_trans' R x z.

Definition ancestor_of''' : Person -> Person -> Prop :=
  clos_refl_symm_trans' parent_of'.

Example ancestor_of'''2 : ancestor_of''' Sage Maria.
Proof. unfold ancestor_of'''. apply s_trans with Ridley.
  - apply s_step. apply po_SR'.
  - apply s_symm. apply s_step. apply po_MR.
Qed.


(* other examples *)

Definition ancestor_of' : Person -> Person -> Prop :=
  clos_refl_trans parent_of.

Example ancestor_of'1 : ancestor_of' Sage Sage.
Proof.
  unfold ancestor_of'. apply t_refl. Qed.

Example ancestor_of'2 : ancestor_of' Sage Moss.
Proof.
  unfold ancestor_of'. apply t_t. apply ancestor_of1. Qed.

Definition ancestor_of'' : Person -> Person -> Prop :=
  clos_refl_symm_trans parent_of.

Example ancestor_of''1 : ancestor_of'' Moss Sage.
Proof. unfold ancestor_of''. apply t_symm. apply t_rt. apply ancestor_of'2. Qed. 

(* ================================================================= *)
(** ** Example: Permutations *)

(** The familiar mathematical concept of _permutation_ also has an
    elegant formulation as an inductive relation.  For simplicity,
    let's focus on permutations of lists with exactly three
    elements. *)

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(** This definition says:
      - If [l2] can be obtained from [l1] by swapping the first and
        second elements, then [l2] is a permutation of [l1].
      - If [l2] can be obtained from [l1] by swapping the second and
        third elements, then [l2] is a permutation of [l1].
      - If [l2] is a permutation of [l1] and [l3] is a permutation of
        [l2], then [l3] is a permutation of [l1]. *)

(** **** Exercise: 1 star, standard, optional (perm)

    According to this definition, is [[1;2;3]] a permutation of
    [[3;2;1]]?  Is [[1;2;3]] a permutation of itself? *)

(* 20min *)

(* FILL IN HERE

    [] *)

Example Perm3_example1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap23.   Qed.

Example Perm3_exercise1 : Perm3 [1;2;3] [3;2;1].
Proof.
  (* apply perm3_trans with [2; 1; 3].
  - apply perm3_swap12.
  (* or [apply Perm3_example1.]!*)
  - apply perm3_trans with [2; 3; 1].
    + apply perm3_swap23.
    + apply perm3_swap12. *)
  apply perm3_trans with [2;3;1].
  - apply Perm3_example1.
  - apply perm3_swap12.  Qed.

Example Perm3_exercise2 : Perm3 [1;2;3] [1;2;3].
Proof.
  apply perm3_trans with [3;2;1].
  - apply Perm3_exercise1.
  - apply perm3_trans with [2;3;1].
    + apply perm3_swap12.
    + apply perm3_trans with [2;1;3].
      * apply perm3_swap23.
      * apply perm3_swap12.  Qed.

(* ================================================================= *)
(** ** Example: Evenness (yet again) *)

(** We've already seen two ways of stating a proposition that a number
    [n] is even: We can say

      (1) [even n = true], or

      (2) [exists k, n = double k].

    A third possibility, which we'll use as a running example for the
    rest of this chapter, is to say that [n] is even if we can
    _establish_ its evenness from the following rules:

       - The number [0] is even.
       - If [n] is even, then [S (S n)] is even. *)

(** (Defining evenness in this way may seem a bit confusing,
    since we have already seen another perfectly good way of doing
    it -- "[n] is even if it is equal to the result of doubling some
    number". It makes a convenient running example because it is
    simple and compact, but we will see more compelling examples in
    future chapters.) *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. First, we give
    the rules names for easy reference:
       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even.

    Now, by rule [ev_SS], it suffices to show that [2] is even. This,
    in turn, is again guaranteed by rule [ev_SS], as long as we can
    show that [0] is even. But this last fact follows directly from
    the [ev_0] rule. *)

(** We can translate the informal definition of evenness from above
    into a formal [Inductive] declaration, where each "way that a
    number can be even" corresponds to a separate constructor: *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** This definition is interestingly different from previous uses of
    [Inductive].  For one thing, we are defining not a [Type] (like
    [nat]) or a function yielding a [Type] (like [list]), but rather a
    function from [nat] to [Prop] -- that is, a property of numbers.
    But what is really new is that, because the [nat] argument of [ev]
    appears to the _right_ of the colon on the first line, it is
    allowed to take _different_ values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].  Accordingly, the type of each constructor must be
    specified explicitly (after a colon), and each constructor's type
    must have the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

    or equivalently:

    Inductive list (X:Type) : Type :=
      | nil                       : list X
      | cons (x : X) (l : list X) : list X.

   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same type (i.e., [list X]).  But if we had tried to bring [nat]
   to the left of the colon in defining [ev], we would have seen an
   error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]" as 1st
        argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter, while in [Inductive ev : nat -> Prop := ...], the
    unnamed [nat] argument is an index. *)

(** We can think of this as defining a Coq property [ev : nat ->
    Prop], together with "evidence constructors" [ev_0 : ev 0] and
    [ev_SS : forall n, ev n -> ev (S (S n))]. *)

(** These evidence constructors can be thought of as "primitive
    evidence of evenness", and they can be used just like proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    constructor names to obtain evidence for [ev] of particular
    numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax to combine several
    constructors: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** In this way, we can also prove theorems that have hypotheses
    involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n as [| n' IH].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IH.  Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, reasoning about how it could have been
    built.

    Defining [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must be one of two things:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _case analysis_ or by _induction_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence for [ev n] _directly_.

    As a tool for such proofs, we can formalize the intuitive
    characterization that we gave above for evidence of [ev n], using
    [destruct]. *)

Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** Facts like this are often called "inversion lemmas" because they
    allow us to "invert" some given information to reason about all
    the different ways it could have been derived.

    Here, there are two ways to prove [ev n], and the inversion lemma
    makes this explicit. *)

(** We can use the inversion lemma that we proved above to help
    structure proofs: *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H.  destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.

(** Note how the inversion lemma produces two subgoals, which
    correspond to the two ways of proving [ev].  The first subgoal is
    a contradiction that is discharged with [discriminate].  The
    second subgoal makes use of [injection] and [rewrite].

    Coq provides a handy tactic called [inversion] that factors out
    this common pattern, saving us the trouble of explicitly stating
    and proving an inversion lemma for every [Inductive] definition we
    make.

    Here, the [inversion] tactic can detect (1) that the first case,
    where [n = 0], does not apply and (2) that the [n'] that appears
    in the [ev_SS] case must be the same as [n].  It includes an
    "[as]" annotation similar to [destruct], allowing us to assign
    names rather than have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E as [| n' E' Heq]. (* as many branches as constructors, as many labels as arguments of a constructor + equations *)
  (* the contradictory case is discharged automatically! *)
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. Compare: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)

    Prove the following result using [inversion].  (For extra
    practice, you can also prove it using the inversion lemma.) *)

(* 2min + 9min with inversion lemma *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* intros n E. apply ev_inversion in E. destruct E as [| [n' [En' E']]].
  * discriminate H.
  * injection En' as En'. rewrite <- En' in E'. 
    apply ev_inversion in E'. destruct E' as [| [n'' [En'' E'']]].
    + discriminate H.
    + injection En'' as En''. rewrite <- En'' in E''. apply E''.
  Qed. *)

  intros n E. inversion E as [| n' E']. inversion E' as [| n'' E''].
  apply E''.  Qed.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense)

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E5. inversion E5 as [| n E3]. inversion E3 as [| m E1].
  apply one_not_even in E1. destruct E1.  Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied to analyze
    evidence for arbitrary inductively defined propositions, not just
    equality.  As examples, we'll use it to re-prove some theorems
    from chapter [Tactics].  (Here we are being a bit lazy by
    omitting the [as] clause from [inversion], thereby asking Coq to
    choose names for the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.
      - Suppose the name [H] refers to an assumption [P] in the
        current context, where [P] has been defined by an [Inductive]
        declaration.
      - Then, for each of the constructors of [P], [inversion H]
        generates a subgoal in which [H] has been replaced by the
        specific conditions under which this constructor could have
        been used to prove [P].
      - Some of these subgoals will be self-contradictory; [inversion]
        throws these away.
      - The ones that are left represent the cases that must be proved
        to establish the original goal.  For those, [inversion] adds
        to the proof context all equations that must hold of the
        arguments given to [P] -- e.g., [n' = n] in the proof of
        [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma. *)

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKED IN CLASS *) unfold Even.

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy seems
    unpromising, because (as we've noted before) the induction
    hypothesis will talk about [n-1] (which is _not_ even!).  Thus, it
    seems better to first try [inversion] on the evidence for [ev].
    Indeed, the first case can be solved trivially. And we can
    seemingly make progress on the second case with a helper lemma. *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *) exists 0. reflexivity.
  - (* E = ev_SS n' E'

    Unfortunately, the second case is harder.  We need to show [exists
    n0, S (S n') = double n0], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [ev]: namely
    [E'].  More formally, we could finish our proof if we could show
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result would suffice. *)
    assert (H: (exists k', n' = double k')
               -> (exists n0, S (S n') = double n0)).
        { intros [k' EQ'']. exists (S k'). simpl.
          rewrite <- EQ''. reflexivity. }
    apply H.

    (** Unfortunately, now we are stuck. To see this clearly, let's
        move [E'] back into the goal from the hypotheses. *)

    generalize dependent E'.

    (** Now it is obvious that we are trying to prove another instance
        of the same theorem we set out to prove -- only here we are
        talking about [n'] instead of [n]. *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this story feels familiar, it is no coincidence: We
    encountered similar problems in the [Induction] chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction! *)

(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove that a property of [n] holds for all even numbers (i.e.,
    those for which [ev n] holds), we can use induction on [ev
    n]. This requires us to prove two things, corresponding to the two
    ways in which [ev n] could have been constructed. If it was
    constructed by [ev_0], then [n=0] and the property must hold of
    [0]. If it was constructed by [ev_SS], then the evidence of [ev n]
    is of the form [ev_SS n' E'], where [n = S (S n')] and [E'] is
    evidence for [ev n']. In this case, the inductive hypothesis says
    that the property we are trying to prove holds for [n']. *)

(** Let's try proving that lemma again: *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    unfold Even. exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : Even n' *)
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas -- in particular for
    formalizing the semantics of programming languages. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum) *)

(* 5 min *)

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En.
  generalize dependent m. (* stay safe *)
  induction En as [| n' En' IH].
  * intros m Em. simpl. apply Em.
  * intros m Em. simpl. apply ev_SS. apply IH. apply Em.  Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev)

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from the [Logic]
    chapter) of applying theorems to arguments, and note that the same
    technique works with constructors of inductively defined
    propositions. *)

(* 21 min *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  { intros En. 
    (* inversion En. apply ev_0. apply ev_SS. apply ev_0.
    apply ev_sum. *)
    (* better use induction on evidence, which subsumes inversion! *)
    induction En as [ | | n' m En' IHn' Em IHm].
    * apply ev_0.
    * apply ev_SS. apply ev_0.
    * apply (ev_sum n' m). apply IHn'. apply IHm. }
  { intros En.
    induction En as [ | n' En' IHn'].
    * apply ev'_0.
    * replace (S (S n')) with (2 + n'). apply ev'_sum.
      + apply ev'_2.
      + apply IHn'.
      + reflexivity. }
Qed.

(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)

(* 13 min *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros n m Esum En.
  generalize dependent m.
  induction En as [| n' En' IHn'].
  * intros m E0m. simpl in E0m. apply E0m.
  * intros m Esum. simpl in Esum. inversion Esum as [| p Em].
    apply IHn' in Em. apply Em.  Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint: Is [(n+m) + (n+p)] even? *)

(* 48 min *)

Check ev_sum.
Check add_assoc.
Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp. 
  apply (ev_sum (n+m) (n+p)) in Enm.
  (* grants you [ev (#1 + #2)] provided you prove [ev #2]*)
  * rewrite (add_comm n p) in Enm. rewrite add_assoc in Enm.
    rewrite <- (add_assoc n m p) in Enm. rewrite (add_comm n (m + p)) in Enm.
    rewrite <- add_assoc in Enm. rewrite add_comm in Enm. 
    apply (ev_ev__ev (n+n) (m+p)) in Enm.
    (* applies [ev_ev__ev] forward, granting you the conclusion ([ev (m+p)]) provided you prove the middle hypothesis ([ev (n+n)]), which is easy *)
    + apply Enm.
    + rewrite <- double_plus. apply ev_double.
  * apply Enp.
Qed.

(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** Just like properties, relations can be defined inductively.  One
    useful example is the "less than or equal to" relation on numbers
    that we briefly saw above. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(** (We've written the definition a bit differently this time,
    giving explicit names to the arguments to the constructors and
    moving them to the left of the colons.) *)

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m : nat) := le (S n) m. (* wow... ingenious *)

Notation "n < m" := (lt n m).

End Playground.

(** **** Exercise: 2 stars, standard, optional (total_relation)

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

(* 2 min *)

Inductive total_relation : nat -> nat -> Prop :=
  | any_p (n m : nat) : total_relation n m
.

Theorem total_relation_is_total : forall n m, total_relation n m.
Proof.
  intros n m. apply any_p.  Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation)

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(* wtf 30+ min - had to sleep over this
   improved 3 days later by leaving the body empty *)
Inductive empty_relation : nat -> nat -> Prop := (* empty *) .

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
Proof. intros n m H. inversion H. (* [destruct] also works *) Qed.
(** [] *)

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

(** **** Exercise: 5 stars, standard, optional (le_and_lt_facts) *)

(* I've been stuck on this exercise for two days now.
   Time to leave it behind and carry on reading. I'll return to the aborted
   proofs later on, when I'm a bit more learned. *)

(*
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).
*)

(* 28 min
  - always keep one variable universal!
*)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Lemn Leno. 
  generalize dependent m.
  induction Leno as [| o' Leno'].
  * intros m Lemn. apply Lemn.
  * intros m Lemn. apply le_S. apply IHLeno'. apply Lemn.
Qed.

(* 5 min *)
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [| n']. apply le_n. apply le_S. apply IHn'.  Qed.

(* 11 min *)
Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m Lenm. induction Lenm as [| m' Lenm'].
  * apply le_n.
  * apply le_S. apply IHLenm'.  Qed.

(* 1h30min... weak... *)
Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m LeSS. inversion LeSS as [| m' LeS].
  * apply le_n.
  * apply le_trans with (S n). apply le_S. apply le_n. apply LeS.
Qed.
  
  (* induction LeSS as [| m' E IH]. *)
  (* WHY. THE FUCK. DOESN'T INDUCTION REWRITE n?!? *)

  (* induction m as [| m' IHm'].
  * inversion LeSS as [| z contra Ez]. apply le_n. inversion contra.
  * apply le_S. apply IH. inversion LeSS as [| m'' H Em''].
    + apply n_le_m__Sn_le_Sm. rewrite H in LeSS. rewrite <- H. apply IH. *)

Lemma eqb_Sn_n : forall n, (S n =? n) = false.
Proof.
  intros n. induction n as [| n' IH].
  + reflexivity.
  + apply IH.  Qed.

Lemma not_Sn_le_n : forall n, ~ (S n <= n).
Proof.
  intros n N. induction n as [| n' IH].
    + inversion N.
    + apply Sn_le_Sm__n_le_m in N. apply IH in N. destruct N.
Qed.

(* no induction needed with transitivity *)
Lemma leb_S_l : forall n m, (S n <=? m) = true -> (n <=? m) = true.
Proof.
  intros n m H.
  generalize dependent n.
  induction m as [| m' IH].
  * intros n contra. discriminate contra.
  * intros n H. destruct n as [| n'].
    - reflexivity.
    - simpl. apply IH. simpl in H. apply H.  Qed.

(* same here *)
Lemma leb_S_r : forall n m, (n <=? m) = true -> (n <=? S m) = true.
Proof.
  intros n. induction n as [| n' IH].
  * intros m H. reflexivity.
  * intros m H. destruct m as [| m'].
    - discriminate H.
    - simpl. simpl in H. apply IH. apply H.  Qed.

(* 2+ days to process, solution in ~30 min - forgot induction was a thing lol *)
Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m. unfold lt. unfold ge.
  generalize dependent n.
  induction m.
  * right. apply O_le_n.
  * intros n. destruct (IHm n) as [H1 | H2]. 
    + left. apply le_S in H1. apply H1.
    + inversion H2 as [| n' Hn']. 
      - left. (* m = n *) apply le_n.
      - right. (* m <= n *) apply n_le_m__Sn_le_Sm. apply Hn'.
Qed.

(* 2 min *)
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a. induction a as [| a' IH].
  * intros b. simpl. apply O_le_n.
  * intros b. simpl. apply n_le_m__Sn_le_Sm. apply IH.  Qed.

(* 9 min *)
Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m Hsum. split.
  * apply (le_trans (n1) (n1 + n2) (m)). apply le_plus_l. apply Hsum.
  * apply (le_trans (n2) (n1 + n2) (m)). 
    rewrite add_comm. apply le_plus_l. apply Hsum.  Qed.

Lemma le_S_l : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n). apply le_S. apply le_n. apply H.  Qed.

(* 2+ days + 3 hours: took me a while to realize I needed the predecessor of [p] *)
(* Lemma add_le_l : forall m p q,
  m <= p + q -> m <= p \/ m <= q. (* silly *)
Proof.
  induction m as [| m' IH].
  - intros. left. apply O_le_n.
  - intros. destruct (IH (S p) (S q)).
    + simpl. apply le_S. apply le_S in H. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H. *)

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
  (** Hint: May be easiest to prove by induction on [n]. *)
Proof.
  intros n. induction n as [| n' IH].
  * simpl. intros m p q Hmpq. left. apply O_le_n.
  * intros m p q HS.
    destruct p as [| p'].
    - simpl in HS. right. 
      rewrite <- plus_Sn_m in HS.
      apply plus_le in HS.
      destruct HS. apply H0.
    - destruct (IH m p' q).
      + simpl in HS. apply Sn_le_Sm__n_le_m in HS. apply HS.
      + left. apply n_le_m__Sn_le_Sm. apply H.
      + right. apply H.
Qed.
    
  (* replace (S n' + m) with (n' + S m) in HS.
  
  destruct HS as [HS1 | HS2].
  + left. 
  apply plus_le in HS. destruct HS as [HS1 HS2].
  replace (S n') with (1 + n') in HS1 by reflexivity.
  assert (HS' : n' + m < p + q) by (apply HS).
  simpl in HS.
  destruct (p + q) as [| o] eqn:Eo.
  + simpl in HS. inversion HS.
  + apply plus_le in HS. destruct HS as [H1 H2].
  (* simpl in HS. apply le_S_l in HS. apply IH in HS. destruct HS as [H1 | H2]. *)

    replace (S n' <= p) with (n' < p) by reflexivity.
  simpl in HS. replace (S (n' + m) <= p + q) with (n' + m < p + q) in HS by reflexivity. *)

(* 11 min *)
Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros n m p Lenm. induction Lenm as [| m' Em' IH].
  * apply le_n.
  * apply (le_trans (p+n) (p+m') (p+S m')).
    + apply IH.
    + rewrite (add_comm p (S m')). simpl. apply le_S. rewrite (add_comm m' p).
      apply le_n.  Qed.

(* 2 min *)
Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n m p Lenm. rewrite add_comm. rewrite (add_comm m p). apply plus_le_compat_l. apply Lenm.  Qed.

(* 7 min *)
Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p Lenm. induction Lenm as [| m' Em' IH].
  * apply le_plus_l.
  * simpl. apply le_S. apply IH.  Qed.

(* 3 min *)
Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros n m Ltnm. unfold lt in Ltnm. apply (le_trans n (S n) m).
  apply le_S. apply le_n. apply Ltnm.  Qed.

(* 30 min *)
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m. unfold lt. intros LeS. inversion LeS as [| m' Em'].
  * split. 
    + rewrite <- (plus_1_l (n1 + n2)). rewrite add_assoc. rewrite (plus_1_l n1). apply le_plus_l.
    + rewrite plus_n_Sm. rewrite add_comm. apply le_plus_l.
  * rewrite plus_n_Sm in Em'. apply plus_le in Em'. destruct Em' as [Hn1 HSn2].
    split.
    + apply n_le_m__Sn_le_Sm. apply Hn1.
    + apply le_S. apply HSn2.  Qed.

(** [] *)

(** **** Exercise: 4 stars, standard, optional (more_le_exercises) *)

(* 10 min (proof of [leb_plus_exists] really helped) *)
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n. induction n as [| n' IH].
  * intros m H. apply O_le_n.
  * intros m H. destruct m as [| m'] eqn:Em'.
    + discriminate H.
    + simpl in H. apply IH in H. apply n_le_m__Sn_le_Sm. apply H.
Qed.

(* 33 min *)
Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
  (** Hint: May be easiest to prove by induction on [m]. *)
Proof.
  intros n m Lenm.
  generalize dependent n. (* fundamental *)
  induction m as [| m' IH].
  * intros n Lenm. inversion Lenm. reflexivity.
  * intros n Lenm. destruct n as [| n'] eqn:En.
    - reflexivity.
    - simpl. apply IH. apply Sn_le_Sm__n_le_m in Lenm. apply Lenm.
Qed.

(** Hint: The next two can easily be proved without using [induction]. *)

(* 1 min *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m. split. apply leb_complete. apply leb_correct.  Qed.

(* 2 min *)
Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o Lenm Leno.
  apply leb_complete in Lenm. apply leb_complete in Leno. apply leb_correct.
  apply le_trans with m. apply Lenm. apply Leno.  Qed.
(** [] *)

Lemma leb_S_l' : forall n m, (S n <=? m) = true -> (n <=? m) = true.
Proof.
  intros n m H. apply leb_true_trans with (S n).
  apply NatList.leb_n_Sn. apply H.  Qed.

Lemma leb_S_r' : forall n m, (n <=? m) = true -> (n <=? S m) = true.
Proof.
  intros n m H. apply leb_true_trans with m.
  apply H. apply NatList.leb_n_Sn.  Qed.


Module R.

(** **** Exercise: 3 stars, standard, especially useful (R_provability)

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

(* 30 min *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o
.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. *)

(* FILL IN HERE *)

(* 1. *)
Example R_112 : R 1 1 2.
Proof. apply c2. apply c3. apply c1.  Qed.

Example R_226 : R 2 2 6.
Proof. apply c2. apply c2. apply c3. apply c3. (* nope *) Abort.

Example R_123 : R 1 2 3.
Proof. apply c2. apply c3. apply c3. apply c1.  Qed.

(* 14 min

  2. No, because [c2] and [c3] let us increase the first two arguments 
    independently, so swapping them with [c5] beforehand has no effect 
    on the amount of times [o] can be decreased to reach 0.

  3. No, because in a derivation applying [c4] increases the first two operands
    by 1 and the last one by 2, but this effect can be promptly reversed 
    thereafter by applying [c2] and [c3] in sequence, returning to where we 
    started before applying [c4]. 
*)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq. *)

(* 21 min *)

(* It's [+] on nats! *)

Definition fR : nat -> nat -> nat := plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros m n o. unfold fR. split.
  { intro ER. induction ER.
    * reflexivity.
    * simpl. f_equal. apply IHER.
    * rewrite <- plus_n_Sm. f_equal. apply IHER.
    * rewrite <- plus_n_Sm in IHER. simpl in IHER. injection IHER.
      intros H. apply H.
    * rewrite add_comm. apply IHER. }
  { generalize dependent n. generalize dependent o.
    induction m as [| m' IH].
    * intros n o H. simpl in H. rewrite H.
      assert (forall a, R 0 a a) as R_0_n.
      { intros a. induction a as [| a']. apply c1. apply c3. apply IHa'. }
      apply R_0_n.
    * intros o n. destruct o as [| o'].
      + intros contra. discriminate contra.
      + intros H. apply c2. apply IH. injection H. intros H'. apply H'.
  }
Qed.

(** [] *)

End R.

(** **** Exercise: 3 stars, advanced (subsequence)

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3]. *)

(* 10 min + 7 min on examples *)
Inductive subseq : list nat -> list nat -> Prop :=
  | Sub0 l : subseq [] l
  | SubSkip y l1 l2
    (H2 : subseq l1 l2) : subseq l1 (y :: l2)
  | SubCons x y l1 l2
    (H2 : x = y) (H2 : subseq l1 l2) : subseq (x :: l1) (y :: l2)
.

Example subseq_test1 : subseq [1;2;3] [1;2;3].
Proof.  repeat apply SubCons; auto. apply Sub0.  Qed.

Example subseq_test2 : subseq [1;2;3] [1;1;1;2;2;3].
Proof. apply SubCons. reflexivity. apply SubSkip. apply SubSkip.
  apply SubCons. reflexivity. apply SubSkip. apply SubCons. reflexivity.
  apply Sub0.  Qed.

Example subseq_test3 : ~ subseq [1;2] [2;1].
Proof. intros F. inversion F.
  - inversion H0.
    inversion H5.
    inversion H8.
  - inversion H2.  Qed. 

(* 2 min *)
Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l. induction l as [| h l' IH].
  * apply Sub0.
  * apply SubCons. { reflexivity. } { apply IH. } Qed.

(* 15 min - wasted time doing induction on l1 *)
Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H. induction H as [| y l1 l2' | h1 h2 l1' l2'].
  * apply Sub0.
  * simpl. apply SubSkip. apply IHsubseq.
  * simpl. apply SubCons. apply H2. apply IHsubseq.  Qed.
  
  (* nope
  induction l1 as [| h1 l1' IH].
  * intros l2 l3 H. apply Sub0.
  * intros l2 l3 H. inversion H as [| y l1'' l2' | h1' y l1'' l2'].
    + (* h1 <> y *) 
      simpl. *)

(* 30+ min first attempt + 45 min solution (after revising "Varying the Induction Hypothesis" and the proof of [le_trans])*)
Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 Sub12 Sub23.
  generalize dependent l1.
  induction Sub23 as [| h3 l2 l3' eq IH | h2 h3 l2' l3' eq Sub2'3' IH ].
  * intros l1 E. destruct l1.
    - apply Sub0.
    - inversion E.
  * destruct l1 as [| h1 l1'].
    - intros E. apply Sub0.
    - intros E. apply SubSkip. apply IH. apply E.
  * intros l1 E. inversion E
    (* as [| h2' l1E l2'E eqE H | h1 h2E l1' l2'E eqE H]. *).
    - (* [l1] is the empty list *)
      apply Sub0.
    - (* [subseq l1 l2] was proved one element sooner than [subseq l2 l3] *)
      apply SubSkip. apply IH. apply H0.
    - (* evidences are synchronized: all heads are the same *)
      apply SubCons. 
      + rewrite H1. apply eq.
      + apply IH. apply H3.
Qed.

(* 
    h    l'
l1  1 :: [2]
l2  4 :: [1;2;3]
l3  1 :: [4;4;2;3]

l1  1 :: [2]
l2  4 :: [1;4;2]
l3  4 :: [5;1;4;2]
*)

(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2)

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n     l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* 21 min *)
(* FILL IN HERE

      R 2 [1;0]
c2 -> R 1 [0]
c2 -> R 0 []
c1.

      R 1 [1;2;1;0] 
c3 -> R 2 [1;2;1;0]
c2 -> R 1 [2;1;0]
c3 -> R 2 [2;1;0]
c3 -> R 3 [2;1;0]
c2 -> R 2 [1;0]
(proved).

      R 6 [3;2;1;0]
      I can only increment 6 using [c3], which leaves the list untouched, thus leading the goal astray from the successor of 3. Unprovable.
    [] *)
(* ################################################################# *)
(** * A Digression on Notation *)

(** There are several equivalent ways of writing inductive
    types.  We've mostly seen this style... *)

Module bin1.
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
End bin1.

(** ... which omits the result types because they are all the same (i.e., [bin]). *)

(** It is completely equivalent to this... *)
Module bin2.
Inductive bin : Type := (* no indexes - parameters in the right side of the colon *)
  | Z            : bin
  | B0 (n : bin) : bin
  | B1 (n : bin) : bin.
End bin2.

(** ... where we fill them in, and this... *)

Module bin3.
Inductive bin : Type :=
  | Z : bin
  | B0 : bin -> bin
  | B1 : bin -> bin.
End bin3.

(** ... where we put everything on the right of the colon. *)

(** For inductively defined _propositions_, we need to explicitly give
    the result type for each constructor (because they are not all the
    same), so the first style doesn't make sense, but we can use
    either the second or the third interchangeably. *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for
    illustrating inductive definitions and the basic techniques for
    reasoning about them, but it is not terribly exciting -- after
    all, it is equivalent to the two non-inductive definitions of
    evenness that we had already seen, and does not seem to offer any
    concrete benefit over them.

    To give a better sense of the power of inductive definitions, we
    now show how to use them to model a classic concept in computer
    science: _regular expressions_. *)

(** Regular expressions are a simple language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (Technical aside: We depart slightly from standard practice in
    that we do not require the type [T] to be finite.  This results in
    a somewhat different theory of regular expressions, but the
    difference is not significant for present purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        In particular, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows.  We use the notation [s =~ re] in
    place of [exp_match s re]. *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

(** Notice that these rules are not _quite_ the same as the
    informal ones that we gave at the beginning of the section.
    First, we don't need to include a rule explicitly stating that no
    string matches [EmptySet]; we just don't happen to include any
    rule that would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")
    (note: should have done the same in the [empty_relation] exercise...)

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the string
    [[1]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split
    the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

(* [Star re] is the family of strings obtained by repeating a string [s] that 
  matches [re] a finite number of times. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1)

    The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

(* ~25 min *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H. inversion H.  Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H1 | H2].
  { apply MUnionL. apply H1. }
  { apply MUnionR. apply H2. }  Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

(* 15 min *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re HIn. induction ss as [| w ss' IH].
  * simpl. apply MStar0.
  * simpl. apply MStarApp.
    { apply HIn. simpl. left. reflexivity. }
    { apply IH. intros w' HIn'. apply HIn. simpl. right. apply HIn'. }  Qed.

(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** For example, suppose we want to prove the following intuitive
    result: If a regular expression [re] matches some string [s], then
    all elements of [s] must occur as character literals somewhere in
    [re].

    To state this as a theorem, we first define a function [re_chars]
    that lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** The main theorem: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re1]), and a second one that applies when [x]
    occurs in [s2] (which matches [re2]). *)

    rewrite In_app_iff in *. (* new notation! *)
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin). (* instead of the lengthier [apply IH1. apply Hin.] *)
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for [exp_match], rather than
    induction on the regular expression [re]: The latter would only
    provide an induction hypothesis for strings that match [re], which
    would not allow us to reason about the case [In x s2]. *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin). (* simplifies [re_chars (Star re)] in [IH2] *)
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty)

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Check (Union (EmptySet) (Char 2)).

(* 5 min *)
Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr | Char _ | Star _ => true
  | App r1 r2 => re_not_empty r1 && re_not_empty r2 (* can't append to [s1 =~ r1] if there is no [s2 =~ r2], and viceversa! *)
  | Union r1 r2  => re_not_empty r1 || re_not_empty r2
  end.


Example re_union : [2] =~ (Union (EmptySet) (Char 2)).
Proof. apply MUnionR. apply MChar.  Qed.

Example re_not_empty1 : re_not_empty (Union (EmptySet) (Char 2)) = 
  (* false. - no *) true.
Proof. reflexivity.  Qed.

Example re_star : @exp_match nat [] (Star (EmptySet)).
Proof. apply MStar0.  Qed.

Example re_not_empty2 : @re_not_empty nat (Star EmptySet) = true.
Proof. reflexivity.  Qed.

Example re_not_empty3 : re_not_empty (Star (Union (Char 0) (Char 1))) = true.
Proof. reflexivity.  Qed.
  
Example re_bin1 : [0;1;0;0] =~ Star (Union (Char 0) (Char 1)).
Proof.
  apply (MStarApp [0]).
  { apply MUnionL. apply MChar. }
  apply (MStarApp [1]).
  { apply MUnionR. apply MChar. }
  apply (MStarApp [0]).
  { apply MUnionL. apply MChar. }
  apply (MStarApp [0]).
  { apply MUnionL. apply MChar. }
  apply MStar0.  Qed.

Example re_bin2 : [0;1;0;1] =~ Star (App (Char 0) (Char 1)).
Proof.
  apply (MStarApp [0;1]).
  { apply (MApp [0]). apply MChar. apply MChar. }
  apply (MStarApp [0;1]).
  { apply (MApp [0]). apply MChar. apply MChar. }
  apply MStar0.  Qed.

(* 40 min left dir, 35 min right dir
  guilty of mixing up && and || between [App] and [Union] *)
Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  { induction re.
    * intros [s Hs]. inversion Hs.
    * intros. reflexivity.
    * intros. reflexivity.
    Search orb.
    * intros [s Ms]. simpl. apply andb_true_iff.
      inversion Ms as [ | | s1 r1 s2 r2 Ms1 Ms2 | | | | ].
      split.
      { apply IHre1. exists s1. apply Ms1. }
      { apply IHre2. exists s2. apply Ms2. }
    * intros [s Ms]. simpl. apply orb_true_iff.
      inversion Ms as [ | | | s1 r1 r2 Ms1 | s2 r1 r2 Ms2 | | ].
      left. apply IHre1. exists s. apply Ms1.
      right. apply IHre2. exists s. apply Ms2.
    * simpl. intros []. reflexivity. }
  { intros H. induction re.
    * discriminate H.
    * exists []. apply MEmpty.
    * exists [t]. apply MChar.
    * simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IHre1 in H1. destruct H1 as [s1 H1].
      apply IHre2 in H2. destruct H2 as [s2 H2].
      exists (s1 ++ s2). apply MApp. apply H1. apply H2.
    * simpl in H. apply orb_true_iff in H. destruct H as [H1 | H2].
      + apply IHre1 in H1. destruct H1 as [s1 H1].
        exists s1. apply MUnionL. apply H1.
      + apply IHre2 in H2. destruct H2 as [s2 H2].
        exists s2. apply MUnionR. apply H2.
    * exists []. apply MStar0. }
Qed.

(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

(* I've used [generalize dependend] as a workaround so far *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Now, just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt. *)

  (* inversion H1 as [ | | | | | re1 Es1 H2 | s1' s2' re1 H2 H2Star Eapp Ere1 ].
  * intros H. simpl. apply H.
  * intros H. apply (MStarApp (s1' ++ s2') s2). -- stuck, as foretold... and [app_assoc] doesn't help *) 

  induction H1 (* this is the equivalent of doing induction on [S n], if [n] was a [nat], which is silly. *)
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect
    from the definition of [exp_match]), we have lost a very important
    bit of information from [H1]: the fact that [s1] matched something
    of the form [Star re].  This means that we have to give proofs for
    _all_ seven constructors of this definition, even though all but
    two of them ([MStar0] and [MStarApp]) are contradictory.  We can
    still get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show

      s2     =~ Char x' ->
      x'::s2 =~ Char x'

    which is clearly impossible. *)

  - (* MChar. *) intros H. simpl. (* Stuck... *)
Abort.

(** The problem here is that [induction] over a Prop hypothesis
    only works properly with hypotheses that are "completely
    general," i.e., ones in which all the arguments are variables,
    as opposed to more complex expressions like [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

    A possible, but awkward, way to solve this problem is "manually
    generalizing" over the problematic expressions by adding
    explicit equality hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence
    directly, because the argument to the first hypothesis is
    sufficiently general, which means that we can discharge most cases
    by inverting the [re' = Star re] equality in the context.

    This works, but it makes the statement of the lemma a bit ugly.
    Fortunately, there is a better way... *)
Abort.

(** The tactic [remember e as x] causes Coq to (1) replace all
    occurrences of the expression [e] by the variable [x], and (2) add
    an equation [x = e] to the context.  Here's how we can use it to
    show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    intros H. apply H.

  - (* MStarApp *)
    intros H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * apply Heqre'.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2) *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

(* 1h30min + 1h + 30min solve 1 month later *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re' eqn:Estar.
  induction H as [ | | | | | re'' | s1 s2 re'' Hmatch1 IH1 Hmatch2 IH2 ].
  * discriminate.
  * discriminate.
  * discriminate.
  * discriminate.
  * discriminate.
  * exists []. split.
    + reflexivity.
    + simpl. intros s' [].
  * assert (Hre : re'' = re).
    { injection Estar. intros. apply H. }
    apply IH2 in Estar.
    destruct Estar as [ss [Hfold HIn]].
    exists (s1 :: ss). simpl. split.
    + rewrite <- Hfold. reflexivity.
    + intros s' [Hs' | HIn'].
      - rewrite Hre,  Hs' in Hmatch1. apply Hmatch1.
      - apply HIn. apply HIn'.
Qed.

(** [] *)

Compute fold app [] [].
Compute fold app [[]] [].
Compute fold app [[];[]] [].
Compute fold app [[1];[]] [].

(** **** Exercise: 5 stars, advanced (weak_pumping)

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].  (For the sake of simplicity in this
    exercise, we consider a slightly weaker theorem than is usually
    stated in courses on automata theory -- hence the name
    [weak_pumping].)

    To get started, we need to define "sufficiently long."  Since we
    are working in a constructive logic, we actually need to be able
    to calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** You may find these lemmas about the pumping constant useful when
    proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - (* EmptySet *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  rewrite H in Hp1. inversion Hp1.
Qed.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** This auxiliary lemma might also be useful in your proof of the
    pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity. (* notice comma notation in [rewrite] *)
Qed.

Compute napp 0 [2].
Compute napp 2 [2].
Compute napp 30 [].
Compute napp 5 [[2;3]].

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc. (* remember: [++] is right associative *)
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

(** The (weak) pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3], will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

(* === my tests === *)
Definition re1 := App (Char 0) (Char 1).
Compute pumping_constant re1.

(* The pumping constant of any regexp built by recursively applying [App] to [Char _] is always greater than the length of the one possible string that matches it. The pumping lemma doesn't apply here. *)

Example match_re1 : [0;1] =~ re1. (* no other strings match [re1] *)
Proof. apply (MApp [0]). apply MChar. apply MChar.  Qed.

Definition re1' := Star re1. (* This kind of regexp is relevant to the pumping lemma, because it is matched by strings whose length is greater than its pumping constant. *)
Compute pumping_constant re1.

Example match_re1' : [0;1;0;1;0;1] =~ re1'.
Proof.
  apply (MStarApp [0;1]). apply match_re1.
  apply (MStarApp [0;1]). apply match_re1.
  apply (MStarApp [0;1]). apply match_re1.
  apply MStar0.  Qed.

Lemma le_add_cases : forall n p q, n <= p + q ->
  (n <= p \/ n <= q) \/ (n > p /\ n > q).
Proof. Admitted.

Lemma star_empty : forall T s,
  s =~ @Star T EmptyStr -> s = nil.
Proof.
  intros T s H. remember (Star EmptyStr) as re eqn:E.
  induction H
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  * reflexivity.
  * inversion E.
  * inversion E.
  * inversion E.
  * inversion E.
  * reflexivity.
  * injection E. intros H. rewrite H in *.
    inversion Hmatch1.
    rewrite IH2. reflexivity. apply E.  Qed.

Lemma s_not_nil : forall T s (re : reg_exp T),
    s =~ re -> pumping_constant re <= length s ->
    1 <= length s.
Proof.
  intros T s re Hmatch Hpc.
  apply le_trans with (pumping_constant re).
  apply pumping_constant_ge_1.
  apply Hpc.  Qed.

Lemma star_not_nil : forall T s ss (re : reg_exp T),
    s =~ re -> ss =~ Star re ->
    pumping_constant re <= length (s ++ ss) ->
    s <> nil.
Proof.
  intros T s ss re M1 M2. remember (Star re) as re' eqn:E.
  generalize dependent s.
  induction M2.
  * inversion E.
  * inversion E.
  * inversion E.
  * inversion E.
  * inversion E.
  * intros. injection E. intros. rewrite <- H0 in *. rewrite app_nil_r in H.
    apply s_not_nil in H. destruct s. simpl in *. inversion H0. unfold not. intros. inversion H. unfold not. intros. inversion H1. apply M1.
  * intros. inversion E. rewrite H1 in *. inversion M1.
    + rewrite <- H2 in *. inversion M2_1. apply star_empty in M2_2. rewrite <- H0 in *. rewrite <- H3 in *. rewrite M2_2 in *. simpl in H. inversion H.
    + unfold not. intros. inversion H3.
  Abort.

(** Complete the proof below. Several of the lemmas about [le] that
    were in an optional exercise earlier in this chapter may also be
    useful. *)
Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* MChar *)
    simpl. intros contra. inversion contra. inversion H0.
  - (* MApp - 42 min + 15 min *)
    simpl. intros H. rewrite app_length in H. apply add_le_cases in H.
    (* extract witnesses from induction hypotheses...? yessir *)
    destruct H as [Hs1 | Hs2].
    * (* PM holds of [s1] *)
      apply IH1 in Hs1.
      destruct Hs1 as [s1' [p1 [s1'' [Hs1' [Hnil Hpump]]]]].
      exists s1', p1, (s1'' ++ s2).
      rewrite Hs1'. split.
      + rewrite <- (app_assoc T s1' (p1 ++ s1'') s2).
        rewrite <- (app_assoc T p1 s1'' s2).
        reflexivity.
      + split.
        { apply Hnil. }
        { intros m. rewrite app_assoc, app_assoc.
          rewrite <- app_assoc with (n:=s1''). apply MApp.
          apply Hpump. apply Hmatch2. }
    * (* PM holds of [s2] *)
      apply IH2 in Hs2.
      destruct Hs2 as [s2' [p2 [s2'' [Hs2' [Hnil Hpump]]]]].
      exists (s1 ++ s2'), p2, s2''.
      rewrite Hs2'. split.
      + rewrite <- (app_assoc T s1 s2' (p2 ++ s2'')). reflexivity.
      + split.
        { apply Hnil. }
        { intros m. rewrite <- app_assoc with (l:=s1). apply MApp.
          apply Hmatch1. apply Hpump. }
  - (* MUnionL - 10 min *)
    simpl. intros H. apply plus_le in H. destruct H as [H1 _].
    apply IH in H1.
    destruct H1 as [s1' [p [s1'' [H1' [Hnil Hpump]]]]].
    exists s1', p, s1''. split.
      apply H1'. 
      split. 
        apply Hnil.
        intros m. apply MUnionL. apply Hpump.
  - (* MUnionR - immediate *)
    simpl. intros H. apply plus_le in H. destruct H as [_ H2].
    apply IH in H2.
    destruct H2 as [s2' [p [s2'' [H2' [Hnil Hpump]]]]].
    exists s2', p, s2''. split.
      apply H2'. 
      split. 
        apply Hnil.
        intros m. apply MUnionR. apply Hpump.
  - (* MStar0 - 10 min *)
    simpl. intros contra.
    assert (Hp1 : pumping_constant re >= 1).
    { apply pumping_constant_ge_1. }
    apply (le_trans 1 (pumping_constant re) 0) in Hp1.
    inversion Hp1. apply contra.
  - (* MStarApp *)
    intros H. simpl in H.
    exists [], s1, s2. simpl. split.
      reflexivity.
      split.
        assert (Hp1 : pumping_constant re >= 1).
        { apply pumping_constant_ge_1. }
        unfold ge in Hp1. simpl in H.
        apply (le_trans 1 (pumping_constant re)) in H.
        assert (len_not_nil : forall X (l : list X), 1 <= length l -> l <> [ ]).
        { intros X [| x l'].
          simpl. intros F. inversion F.
          intros _ F. inversion F. }
        apply len_not_nil in H.
        (* apply H. apply Hp1.
        intros m. rewrite app_nil_r.
        apply (napp_star T m s1 s2) in Hmatch1. simpl in Hmatch1.
        rewrite app_nil_r in Hmatch1. *)
        Admitted.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (pumping)

    Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also requires that [length s1 +
    length s2 <= pumping_constant re]. *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  (* FILL IN HERE *) Admitted.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we sometimes
    need to relate boolean computations to statements in [Prop].  But
    performing this conversion as we did there can result in tedious
    proof scripts.  Consider the proof of the following theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this sort of reasoning by defining an inductive
    proposition that yields a better case-analysis principle for [n =?
    m].  Instead of generating the assumption [(n =? m) = true], which
    usually requires some massaging before we can use it, this
    principle gives us right away the assumption we really need: [n =
    m].

    Following the terminology introduced in [Logic], we call this
    the "reflection principle for equality on numbers," and we say
    that the boolean [n =? m] is _reflected in_ the proposition [n =
    m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  It states that the property [P]
    _reflects_ (intuitively, is equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].

    To see this, notice that, by definition, the only way we can
    produce evidence for [reflect P true] is by showing [P] and then
    using the [ReflectT] constructor.  If we invert this statement,
    this means that we can extract evidence for [P] from a proof of
    [reflect P true].

    Similarly, the only way to show [reflect P false] is by tagging
    evidence for [~ P] with the [ReflectF] constructor. *)

(** To put this observation to work, we first prove that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
  (* also           intro F. rewrite H in F. discriminate F. *)
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, especially useful (reflect_iff) *)

(* 8 min *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b E. inversion E as [Et Eb | Ef Eb].
    - split.
      * intros H. reflexivity.
      * intros _. apply Et.
    - split.
      * intros contra. apply Ef in contra. destruct contra.
      * intros contra. discriminate contra.
Qed.


(** [] *)

(** We can think of [reflect] as a variant of the usual "if and only
    if" connective; the advantage of [reflect] is that, by destructing
    a hypothesis or lemma of the form [reflect P b], we can perform
    case analysis on [b] while _at the same time_ generating
    appropriate hypothesis in the two branches ([P] in the first
    subgoal and [~ P] in the second). *)

(** Let's use [reflect] to produce a smoother proof of
    [filter_not_empty_In].

    We begin by recasting the [eqb_eq] lemma in terms of [reflect]: *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** The proof of [filter_not_empty_In] now goes as follows.  Notice
    how the calls to [destruct] and [rewrite] in the earlier proof of
    this theorem are combined here into a single call to
    [destruct]. *)

(** (To see this clearly, execute the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (eqbP_practice)

    Use [eqbP] as above to prove the following: *)

(* ~15 min *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  * simpl. intro contra. destruct contra.
  * simpl. unfold count in Hcount.
    destruct (eqbP n m) in Hcount.
    - (* [n = m] *)
      discriminate Hcount.
    - (* [n <> m] *)
      intros [F | F].
      + destruct H. symmetry. apply F.
      + apply IHl'.
        { apply Hcount. }
        { apply F. }
Qed.

(** [] *)

(** This small example shows reflection giving us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    This way of using [reflect] was popularized by _SSReflect_, a Coq
    library that has been used to formalize important results in
    mathematics, including the 4-color theorem and the Feit-Thompson
    theorem.  The name SSReflect stands for _small-scale reflection_,
    i.e., the pervasive use of reflection to streamline small proof
    steps by turning them into boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (nostutter_defn)

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] has two occurrences of the element [1] but
    does not stutter.)  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

(* ~25 min *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | NoStt0 : nostutter []
  | NoStt1 x : nostutter [x] 
  | NoSttCons 
      (x y : X) (l : list X)
      (H1 : y <> x)
      (H2 : nostutter (y :: l)) : nostutter (x :: y :: l).

      (* have the inequality evidence first helps streamline the proofs and lets you use the provided proofs. *)

      (* Original (forgot the 1-element evidence, hypotheses unswapped):
      | NoSttEmpty : nostutter []
      | NoSttCons 
        (x y : X) (l : list X)
        (H1 : nostutter (y :: l)) 
        (H2 : y <> x) : nostutter (x :: y :: l). *)

(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto.
Qed.
(* 
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat). (* notice they're generalizing [nil] instead of [nostutter] *)
Proof. repeat constructor; apply eqb_neq; auto.  Qed.
(* 
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply eqb_neq; auto.  Qed.
(* 
  Proof. repeat constructor; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    First define what it means for one list to be a merge of two
    others.  Do this with an inductive relation, not a [Fixpoint].  *)

(* 20 min + ~30 min *)

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | Merge0L l : merge [] l l
  | Merge0R l : merge l [] l
  | MergeConsL x l1 l2 m
    (Hm : merge l1 l2 m) : merge (x :: l1) l2 (x :: m)
  | MergeConsR l1 y l2 m
    (Hm : merge l1 l2 m) : merge l1 (y :: l2) (y :: m)
.

Example merge_test1 : merge [1;6;2] [4;3] [1;4;6;2;3].
Proof. apply MergeConsL. apply MergeConsR. apply MergeConsL.
  apply MergeConsL. apply Merge0L.  Qed.

Example merge_test2 : merge [1;6;2] [4;3] [1;6;2;4;3].
Proof. repeat apply MergeConsL; auto. repeat apply MergeConsR; auto.
  apply Merge0L.  Qed.

Example merge_test3 : ~ merge [1;6;2] [4;3] [1;3;2;6;4].
Proof. intros H. inversion H. inversion Hm.  Qed.

(* unnecessary *)
Lemma forallb_filter_true : forall (X : Set) (test: X->bool) (l : list X),
  forallb test l = true <-> filter test l = l.
Proof. Admitted.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 Emerge HAll1 HAll2.
  induction Emerge
    as [ l2 | l1 | | ].
  * induction l2 as [| h l2' IH].
    - reflexivity.
    - destruct HAll2 as [Hh HAll2].
      unfold filter. rewrite Hh. apply IH. apply HAll2.
  * apply forallb_true_iff in HAll1.
    induction l1 as [| h l1' IH].
    - reflexivity.
    - simpl in *. 
      apply andb_true_iff in HAll1. destruct HAll1 as [Hh HAll1].
      rewrite Hh. f_equal. apply IH. apply HAll1.
  * simpl in *. destruct HAll1 as [Hh HAll1].
    rewrite Hh. f_equal. apply IHEmerge. apply HAll1. apply HAll2.
  * simpl in *. destruct HAll2 as [Hh HAll2].
    rewrite Hh. f_equal. apply IHEmerge. apply HAll1. apply HAll2.
Qed.

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* some lemmas I did for fun; besides that they serve no purpose in the solution of the exercise *)

(* 12 min*)
Lemma subseq_len : forall (l1 l2 : list nat),
  subseq l1 l2 -> length l1 <= length l2.
Proof.
  intros l1 l2 E. induction E
    as [l1 | h2 l1 l2 | h1 h2 l1' l2' Heq H IH ].
  * apply O_le_n.
  * simpl. apply le_S. apply IHE.
  * simpl. apply n_le_m__Sn_le_Sm. apply IH.
Qed.

(* 5 min *)
Lemma filter_is_subseq : forall (test : nat -> bool) (l : list nat),
  subseq (filter test l) l.
Proof.
  intros test l. induction l as [| x l' IH].
  * apply Sub0.
  * simpl. destruct (test x).
    - apply SubCons. { reflexivity. } { apply IH. }
    - apply SubSkip. apply IH.
Qed.

Lemma subseq_filter_all : forall (test : nat -> bool) (s l : list nat),
  subseq s (filter test l) -> All (fun x => test x = true) s.
Proof.
  intros test s l E.
  (* remember (filter test l) as f.
  generalize dependent l. *)
  induction E
    as [f | y s f' H IH | x y s' f' Heq H IH ].
  * simpl. apply I.
  * apply IH. (* [remember] complicates things ugh!!! *)
  * simpl. split.
    - (* stuck... I lost the information about filter *)
Abort.

(* 17 min in one go *)
Theorem filter_longest_subseq : forall (test : nat -> bool) (s l : list nat),
  subseq s l ->
  All (fun x => test x = true) s ->
  length s <= length (filter test l). 
Proof.
  intros test s l Hsub HAll.
  induction Hsub as [ l | y s l' Hsub IH | x y s' l' Heq Hsub IH ].
  * apply O_le_n.
  * apply IH in HAll. simpl.
    destruct (test y).
    + simpl. apply le_S. apply HAll.
    + apply HAll.
  * simpl in HAll. destruct HAll as [Hx HAll'].
    apply IH in HAll'.
    simpl. destruct (test y) eqn:Hy.
    + simpl. apply n_le_m__Sn_le_Sm. apply HAll'.
    + (* spiky: [test] cannot be [false] on the head [x] of [s]! *)
      rewrite Heq in *. rewrite Hy in Hx. discriminate Hx.
Qed.

(*
[1;2;2]
[1;2]

[1;2]
[3;1;2]
*)

(** **** Exercise: 4 stars, standard, optional (palindromes)

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

(* ~15 min *)

Inductive pal {X:Type} : list X -> Prop :=
  | Pal0 : pal []
  | Pal1 x : pal [x]
  | PalApp x l (H : pal l) : pal (x :: l ++ [x])
.

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros X l. induction l as [| h l' IH].
  * apply Pal0.
  * simpl.
    assert (cons_app : 
      forall A a (w1 w2: list A), (a :: w1) ++ w2 = a :: w1 ++ w2).
    { intros. reflexivity. } (* unnecessary *)
    rewrite app_assoc. apply PalApp. apply IH.
Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros X l Epal. induction Epal as [ | | x l' El' IH].
  * reflexivity.
  * reflexivity.
  * simpl. rewrite rev_app_distr. simpl. f_equal. f_equal. apply IH.
Qed.

(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse)

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

(* 1h20min + 1h *)
Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
  Search rev.
  intros X l. induction l as [| x l' IH].
  * intros H. apply Pal0.
  * (*
    - separate the last element [y] from [l'] to have the goal
      [pal (x :: l'' ++ [y])]
    - prove that [x] and [y] are equal
    *)
    intros H. simpl in H.
    rewrite <- (rev_involutive X l') in H.
    rewrite <- (rev_involutive X l').
    (* I want to do induction on (rev l'), but it adds an hypothesis that are impossible to satisfy (i.e. [rev l' = l'']) *)
    destruct (rev l') as [| y l''] eqn:Erev.
    + apply Pal1.
    + simpl. rewrite (rev_involutive) in H. simpl in H.
      injection H. intros H' Hx. rewrite <- Hx in *.
      rewrite H'. apply PalApp. (* stuck *)
Abort.
(** [] *)

(* 
      x    l'
      1 :: [2;3;3;2;1]
rev ( 1 :: [2;3;3;2;1] )

                l'                x
rev             [2;3;3;2;1]   ++ [1]
rev ( rev ( rev [2;3;3;2;1])) ++ [1]

            y    l''              x
rev ( rev ( 1 :: [2;3;3;2] )) ++ [1]
            1 :: [2;3;3;2]    ++ [1]
*)

(** **** Exercise: 4 stars, advanced, optional (NoDup)

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* FILL IN HERE *)

(* ~20 min *)
Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | Dis0L l : disjoint [] l
  | Dis0R l : disjoint l []
  | DisConsL x l1 l2
    (HIn : ~ In x l1 /\ ~ In x l2)
    (H : disjoint l1 l2) : disjoint (x :: l1) l2
  | DisConsR x l1 l2
    (HIn : ~ In x l1 /\ ~ In x l2)
    (H : disjoint l1 l2) : disjoint l1 (x :: l2).

Example disjoin_test1 : disjoint [3] [1;2].
Proof. apply DisConsL. unfold not. simpl.
  - split.
    * intros [].
    * intros [ | []].
      discriminate H. discriminate H. destruct H.
  - apply Dis0L.
Qed.

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* FILL IN HERE *)

(* 2 min + 8 min example *)
Inductive NoDup {X : Type} : list X -> Prop :=
  | NoDup0 : NoDup []
  | NoDup1 x : NoDup [x]
  | NoDupCons x l (HIn : ~ In x l) (H : NoDup l) : NoDup (x :: l).

Example nodup_test1 : NoDup [1;2;3;4].
Proof. apply NoDupCons.
  * intros [|[|[|[]]]].
    discriminate H. discriminate H. discriminate H.
  * apply NoDupCons.
    + intros [|[|[]]].
      discriminate H. discriminate H.
    + apply NoDupCons.
      - intros [|[]]. discriminate.
      - apply NoDup1.
Qed.

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* FILL IN HERE *)

Lemma nil_app :
  forall X (s1 s2 : list X), [] = s1 ++ s2 -> [] = s1 /\ [] = s2.
Proof.
  intros Y s1 s2 G. destruct s1.
  split. reflexivity. simpl in G. apply G.
  simpl in G. discriminate G.
Qed.

Lemma app_nodup : forall X (l1 l2 : list X),
  NoDup (l1 ++ l2) -> NoDup l2 /\ NoDup l1.
Proof.
  intros X l1 l2 Eapp.
  induction l1 as [| x l1' IH].
  * simpl in Eapp. split. apply Eapp. apply NoDup0.
  * simpl in Eapp. inversion Eapp.
    - apply nil_app in H1. destruct H1 as [Hnil1 Hnil2].
      split.
        rewrite <- Hnil2. apply NoDup0.
        rewrite <- Hnil1. apply NoDup1.
    - destruct IH as [IHl2 IHl1'].
      + apply H0.
      + split.
          apply IHl2.
          apply NoDupCons.
            intros F. apply HIn. apply In_app_iff. left. apply F.
            apply IHl1'.
Qed.

Lemma nodup_rev : forall X x (l : list X),
  NoDup (x :: l) -> NoDup (l ++ [x]).
Proof.
  intros X x l E.
  remember (x :: l) as s.
  induction E as [ | | x' s' Heq Hdup IH].
  * discriminate Heqs.
  * injection Heqs. intros Hnil Hx.
    rewrite <- Hnil. apply NoDup1.
  * (* [remember] ruins everything, as always *)
  
  (* induction l as [| x l' IH].
  * apply NoDup0.
  * simpl in E. apply app_nodup in E. destruct E as [HIn E].
      apply IH in E. inversion E.
      - intros [].
      - *)
  Abort.

(* 1h+ - blocked *)
Lemma nodup_comm : forall X (l1 l2 : list X),
  NoDup (l1 ++ l2) -> NoDup (l2 ++ l1).
Proof.
  induction l1 as [| x l1' IH].
  * simpl. intros l2 E. rewrite app_nil_r. apply E.
  * intros l2 E. inversion E.
    + apply nil_app in H1. destruct H1 as [Hl1' Hl2].
      rewrite <- Hl1'. rewrite <- Hl2. apply NoDup1.
    + replace (x :: l1') with ([x] ++ l1').
      rewrite app_assoc. apply IH.
      rewrite app_assoc. 
      (* apply IH. *)
  Admitted.

(* 48 min + time to prove nodup_comm *)
Theorem nodup_app : forall X (l1 l2 : list X),
  NoDup l1 /\ NoDup l2 ->
  disjoint l1 l2 -> NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 [Edup1 Edup2] Edisj.
  induction Edisj
    as [ l2 | l1 | x l1' l2 [HIn1 HIn2] E IH | x l1 l2' [HIn1 HIn2] E IH].
  * apply Edup2.
  * rewrite app_nil_r. apply Edup1.
  * simpl. apply NoDupCons.
    - intros F. apply In_app_iff in F. destruct F as [F | F].
      + apply HIn1 in F. destruct F.
      + apply HIn2 in F. destruct F.
    - apply IH.
      + inversion Edup1. { apply NoDup0. } { apply H0. }
      + apply Edup2.
  * apply nodup_comm. apply nodup_comm in IH.
    - simpl. apply NoDupCons.
        intros F. apply In_app_iff in F. destruct F as [F | F].
          apply HIn2 in F. destruct F.
          apply HIn1 in F. destruct F.
        apply IH.
    - apply Edup1.
    - inversion Edup2. { apply NoDup0. } { apply H0. }
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy and useful lemma. *)

(* 8 min *)
Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l HIn. induction l as [| h l' IH].
  * destruct HIn as [].
  * destruct HIn as [Hh | HIn].
    + exists [], l'. simpl. rewrite Hh. reflexivity.
    + apply IH in HIn. destruct HIn as [l1 [l2 Heq]].
      exists (h :: l1), l2. rewrite Heq. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | Rep0 x : repeats [x;x] (* covered by RepCons *)
  | RepCons x l (HIn : In x l) : repeats (x :: l)
  | RepSkip x l (H : repeats l) : repeats (x :: l)

  (* | Rep0 x : repeats [x;x]
  | Rep2 x l1 l2 : repeats (x :: l1 ++ x :: l2)
  | RepCons x l (H : repeats l) : repeats (x :: l) *)
  (* YesDup l (H : NoDup l) : repeats l *)
.

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

(* 1h40min + *)
Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1  l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [|x l1' IHl1'].
  * intros l2 _ Hlen. unfold lt in Hlen. inversion Hlen.
  * intros l2 HIn Hlen.
    destruct (EM (In x l1')) as [HxIn | HxOut].
    + (* [x] is the element that repeats in [l1]. Easy *)
      apply RepCons. apply HxIn.
      
    + (* [x] is _not_ the element that repeats in [l1],
          but [x] must belong in [l2]! Therefore it splits [l2] in two other lists by [in_split]. The element that repeats must be in one of these two. *)
      apply RepSkip.
      apply (in_split X x) in HIn. destruct HIn as [l2a [l2b eq]].
      apply (IHl1' (l2a ++ l2b)).
      intros y HInl1'. (* stuck: I lost information when I applied [in_split] *)
      apply In_app_iff.
Abort.
(** [] *)

(*
                                        x     l'
  l1 (items)    [a;a;c;a;b]    [a;a]    b ::  [a;a]              [a;a]

  l2 (labels)   [a;b;c]        [a]      [a;b] -- (in_split x) -> [a] 
*)

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match automatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Import Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(* note: doing this section after finishing the book, so my proofs will feature tactics and tricks introduces later *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H. (* [exp_match] doesn't have a case for [EmptySet] *)
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)

(* ~1 h *)

Search app.
Lemma app_cases : forall {X} (x : X) l l1 l2,
  x :: l = l1 ++ l2 ->
  ([] = l1 /\ x :: l = l2) \/
  exists a1 a2, x :: l = x :: a1 ++ a2 /\ x :: a1 = l1 /\ a2 = l2.
Proof.
  intros.
  destruct l1, l2; try intuition.
  - rewrite app_nil_r in H. inversion H.
    right. exists l1, []; rewrite app_nil_r. split; split; auto. 
  - right. simpl in H. inversion H. subst. exists l1, (x1 :: l2). auto.
Qed.

(* 50 min -> + 8 min <- *)
Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros. split; intros.
  - apply app_exists in H. destruct H as [s0 [s1 [Happ [Hs0 Hs1]]]].
    apply app_cases in Happ.
    destruct Happ as [[Es0 Es1] | [a0 [a1 [E1 [E2 E3]]]]]; subst.
    * left. auto.
    * right. inversion E1. subst. clear E1. exists a0, s1. auto.
  - destruct H as [[Es0 Es1] | [a0 [a1 [E1 [E2 E3]]]]].
    * replace (a :: s) with ([] ++ a :: s) by reflexivity.
      apply MApp; assumption.
    * rewrite E1.
      replace (a :: a0 ++ a1) with ((a :: a0) ++ a1) by reflexivity.
      apply MApp; assumption.
Qed.

(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive)

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 4 stars, standard, optional (derive_corr)

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] _matches regexes_ if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_match_correct)

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_match_correct : matches_regex regex_match.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* 2023-12-29 17:12 *)
