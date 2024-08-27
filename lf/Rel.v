(** * Rel: Properties of Relations *)

(** This short (and optional) chapter develops some basic definitions
    and a few theorems about binary relations in Coq.  The key
    definitions are repeated where they are actually used (in the
    [Smallstep] chapter of _Programming Language Foundations_),
    so readers who are already comfortable with these ideas can safely
    skim or skip this chapter.  However, relations are also a good
    source of exercises for developing facility with Coq's basic
    reasoning facilities, so it may be useful to look at this material
    just after the [IndProp] chapter. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

(* ################################################################# *)
(** * Relations *)

(** A binary _relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

Definition relation (X: Type) := X -> X -> Prop.

(** Somewhat confusingly, the Coq standard library hijacks the generic
    term "relation" for this specific instance of the idea. To
    maintain consistency with the library, we will do the same.  So,
    henceforth, the Coq identifier [relation] will always refer to a
    binary relation _on_ some set (between the set and itself),
    whereas in ordinary mathematical English the word "relation" can
    refer either to this specific concept or the more general concept
    of a relation between any number of possibly different sets.  The
    context of the discussion should always make clear which is
    meant. *)

(** An example relation on [nat] is [le], the less-than-or-equal-to
    relation, which we usually write [n1 <= n2]. *)

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.
(** (Why did we write it this way instead of starting with [Inductive
    le : relation nat...]?  Because we wanted to put the first [nat]
    to the left of the [:], which makes Coq generate a somewhat nicer
    induction principle for reasoning about [<=].) *)

(* note: Notice each case requires evidence on [n] instead of a constructor or [le]. This is typical of induction principles of inductively defined propositions, see "Induction Principles for Propositions" in [[IndPrinciples.v]]. *)

Check le_ind.
Print le_ind.

(* ################################################################# *)
(** * Basic Properties *)

(** As anyone knows who has taken an undergraduate discrete math
    course, there is a lot to be said about relations in general,
    including ways of classifying relations (as reflexive, transitive,
    etc.), theorems that can be proved generically about certain sorts
    of relations, constructions that build one relation from another,
    etc.  For example... *)

(* ----------------------------------------------------------------- *)
(** *** Partial Functions *)

(** A relation [R] on a set [X] is a _partial function_ if, for every
    [x], there is at most one [y] such that [R x y] -- i.e., [R x y1]
    and [R x y2] together imply [y1 = y2]. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(** For example, the [next_nat] relation is a partial function. *)
Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.

(** However, the [<=] relation on numbers is not a partial
    function.  (Assume, for a contradiction, that [<=] is a partial
    function.  But then, since [0 <= 0] and [0 <= 1], it follows that
    [0 = 1].  This is nonsense, so our assumption was
    contradictory.) *)

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.   Qed.

(** **** Exercise: 2 stars, standard, optional (total_relation_not_partial_function)

    Show that the [total_relation] defined in (an exercise in)
    [IndProp] is not a partial function. *)

(** Copy the definition of [total_relation] from your [IndProp]
    here so that this file can be graded on its own.  *)
Inductive total_relation : nat -> nat -> Prop :=
  | any_p (n m : nat) : total_relation n m
.

(* 2min37s *)
Theorem total_relation_not_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold not, partial_function. intros Hc.
  assert (3 = 42) as Nonsense. {
    apply Hc with (x := 7).
    * apply any_p.
    * apply any_p.
  }
  discriminate Nonsense.   Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation_partial_function)

    Show that the [empty_relation] defined in (an exercise in)
    [IndProp] is a partial function. *)

(* 2 min *)

(** Copy the definition of [empty_relation] from your [IndProp]
    here so that this file can be graded on its own.  *)
Inductive empty_relation : nat -> nat -> Prop :=
  (* empty *)
.

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 _.
  inversion H1.   Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Reflexive Relations *)

(** A _reflexive_ relation on a set [X] is one for which every element
    of [X] is related to itself. *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Transitive Relations *)

(** A relation [R] is _transitive_ if [R a c] holds whenever [R a b]
    and [R b c] do. *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(** **** Exercise: 2 stars, standard, optional (le_trans_hard_way)

    We can also prove [lt_trans] more laboriously by induction,
    without using [le_trans].  Do this. *)

(* 4min30s *)
Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that [m] is less than [o]. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  * apply le_S. apply Hnm.
  * apply le_S in IHHm'o. apply IHHm'o.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (lt_trans'')

    Prove the same thing again by induction on [o]. *)

(* 23min - draw, draw, draw if you can't visualize *)
Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  * (* o = 0 *) inversion Hmo.
  * (* o = S o' *) apply Sn_le_Sm__n_le_m in Hmo.
    inversion Hmo as [eq | o'' H eq].
    + (* m = o' *) apply le_S in Hnm. rewrite eq in Hnm. apply Hnm.
    + (* m < o' *) rewrite <- eq in *.
      apply le_S. apply IHo'.
      apply n_le_m__Sn_le_Sm. apply H.
Qed.
(** [] *)

(** The transitivity of [le], in turn, can be used to prove some facts
    that will be useful later (e.g., for the proof of antisymmetry
    below)... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

(** **** Exercise: 1 star, standard, optional (le_S_n) *)

(* ~10 min, pretty slow considering I've already done it...
  fiddling with tactics and lemmas is not the right way: plan on paper first, visualize your assumptions and do case analysis on the number line. *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H. inversion H as [| m' Hm' eq].
  * (* S n = S m *) apply le_n.
  * (* S n < S m *) apply le_trans with (S n).
    + apply le_S. apply le_n.
    + apply Hm'.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (le_Sn_n_inf)

    Provide an informal proof of the following theorem:

    Theorem: For every [n], [~ (S n <= n)]

    A formal proof of this is an optional exercise below, but try
    writing an informal proof without doing the formal proof first.

    Proof: *)

    (* 1h12min for the informal proof - I've been actively neglecting that there are two instances of [n] to rewrite in the inductive case. *)
    (*

    By case analysis on [n].
    
    Assume [S n <= n]. Then we have two cases to consider for [n]:

    * [n = 0]. Then we have [1 <= 0], which can be discharged immediately.

    * [n = S n']. Then we have [S n <= S n'] - (* no assumption on n'!!! *)

    NO
    ~~~~~~~~~~~~~~~~

    By case analysis on [le (S n) n].

    There two ways this could have been derived:

    * [le_n], which would imply [S n = n], a contradiciton.

    * [le_S] with [n = S n'] and [S n <= n'], we must show [S n <= S n'].

      The thesis can be simplified to [n <= n'] by [le_S_n]. Then, by 
      [le_trans] we destruct it in two subgoals:

      + [n <= S n']

      + [S n' <= n']. (* back to proving the same thing... *)

    NO
    ~~~~~~~~~~~~~~~~

    By induction on evidence [le (S n) n]. - (not possible)

    * The case [le_n] is obvious.

    * In the case [le_S] we have [n = S n'] with [S n <= n'] and [~ (S n <= n')] as the inductive hypothesis. 
      It is easy to see that the two assumptions contradict each other.  []

    NO
    ~~~~~~~~~~~~~~~~

    By induction on [n].

    * The case [n = 0] is obvious.

    * Let [n = S n'] with the inductive hypothesis [~ (S n' <= n')].
      We must show [~ (S (S n') <= S n')]. Assume [S (S n') <= S n'].
      By [le_S_n] we have [S n' <= n'], which contradicts the inductive
      hypothesis.  []

    OK
    ~~~~~~~~~~~~~~~

    We disprove the contrary, [exists n, S n <= n]. 
    Then consider [1 <= 0], which is clearly a contradiction.
    By the exlcuded middle priciple, it must be that [forall n, ~ S n <= n].

    OK?
    [] *)

(** **** Exercise: 1 star, standard, optional (le_Sn_n) *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  intros n Hc.
  induction n as [| n' IHn'].
  * inversion Hc.
  * apply le_S_n in Hc. apply IHn' in Hc. destruct Hc.
Qed.

(** [] *)

(** Reflexivity and transitivity are the main concepts we'll need for
    later chapters, but, for a bit of additional practice working with
    relations in Coq, let's look at a few other common ones... *)

(* ----------------------------------------------------------------- *)
(** *** Symmetric and Antisymmetric Relations *)

(** A relation [R] is _symmetric_ if [R a b] implies [R b a]. *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** **** Exercise: 2 stars, standard, optional (le_not_symmetric) *)

(* 6 min *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* if [not] wraps quantified variables, you can easily prove the goal with
    [assert (falsehood) as Nonsense.] technique. *)
  unfold symmetric. intros Hc.
  (* say [le] is symmetric, then [0 <= 1] implies [1 <= 0]! *)
  assert (1 <= 0) as Nonsense.
  * apply Hc. apply le_S. apply le_n.
  * inversion Nonsense.
Qed.

(** [] *)

(** A relation [R] is _antisymmetric_ if [R a b] and [R b a] together
    imply [a = b] -- that is, if the only "cycles" in [R] are trivial
    ones. *)

(* note: [lt] is _not_ (doubt) antisymmetric, rather it is _asymmetric_. (doubt) *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** Exercise: 2 stars, standard, optional (le_antisymmetric) *)

(* 15 min *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a b H1 H2.
  inversion H1 as [| b' Hb'].
  * reflexivity.
  * rewrite <- H in *. apply (le_trans (S b') a b') in H2.
    + apply le_Sn_n in H2. destruct H2.
    + apply Hb'.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (le_step) *)

(* ~9min - was I supposed to use [antisymmetric]? *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  unfold lt. intros n m p Hnm HmSp.
  apply (le_trans (S n) m (S p)) in Hnm.
  * apply le_S_n in Hnm. apply Hnm.
  * apply HmSp.  Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Equivalence Relations *)

(** A relation is an _equivalence_ if it's reflexive, symmetric, and
    transitive.  *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* ----------------------------------------------------------------- *)
(** *** Partial Orders and Preorders *)

(** A relation is a _partial order_ when it's reflexive,
    _anti_-symmetric, and transitive.  In the Coq standard library
    it's called just "order" for short. *)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** A preorder is almost like a partial order, but doesn't have to be
    antisymmetric. *)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans.  Qed.

(* ################################################################# *)
(** * Reflexive, Transitive Closure *)

(** The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Coq standard library: *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
    (* [clos_refl_trans] relates [x] to itself (provided [x] was in [R]'s domain) *)
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.
    (* if the [clos_refl_trans] relates [x] and [y], and it also
      relates [y] and [z], then it also relates [x] and [z]. *)

(** For example, the reflexive and transitive closure of the
    [next_nat] relation coincides with the [le] relation. *)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step. (* reveals [next_nat] *)
      apply nn. (* [clos_refl_trans] subsumes [next_nat]! *)
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans [x := n, z := m]*)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.

(** The above definition of reflexive, transitive closure is natural:
    it says, explicitly, that the reflexive and transitive closure of
    [R] is the least relation that includes [R] and that is closed
    under rules of reflexivity and transitivity.  But it turns out
    that this definition is not very convenient for doing proofs,
    since the "nondeterminism" of the [rt_trans] rule can sometimes
    lead to tricky inductions.  Here is a more useful definition: *)

(* I suppose the nondetermism lies in the choice of the middle term [y]. *)

Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  (* to see how [t_step] is bundled here, consider the case [y = z] *)
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

(** Our new definition of reflexive, transitive closure "bundles"
    the [rt_step] and [rt_trans] rules into the single rule step.
    The left-hand premise of this step is a single use of [R],
    leading to a much simpler induction principle.

    Before we go on, we should check that the two definitions do
    indeed define the same relation...

    First, we prove two lemmas showing that [clos_refl_trans_1n] mimics
    the behavior of the two "missing" [clos_refl_trans]
    constructors.  *)

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. (* i.e. [apply (rt1n_trans R x y)] *)
  apply H. apply rt1n_refl.   Qed.

Definition clos_nn := clos_refl_trans_1n next_nat.

Example test_rsc1 : clos_nn 42 42.
Proof. apply rt1n_refl.  Qed.

Example test_rsc2 : clos_nn 2 4.
Proof.
  apply rt1n_trans with 3. apply nn.
  apply rt1n_trans with 4. apply nn.
  apply rt1n_refl.  Qed.

Example test_rsc3 : clos_nn 2 4 /\ next_nat 4 5 -> clos_nn 2 5.
Proof.
  intros [H1 H2].
  apply rt1n_trans with 3. apply nn.
  apply rt1n_trans with 4. apply nn.
  apply rt1n_trans with 5. apply H2.
  apply rt1n_refl.  Qed.

(** **** Exercise: 2 stars, standard, optional (rsc_trans) *)

(* 3h+ this is vile; just the fact they rated it 2 stars makes my blood boil (8/2/2024) + solved (8/8/2024) in ~1h5min. Can you do without the auxiliary lemma? *)

Print clos_refl_trans_1n.

Lemma rsc_trans_1 :
  forall (X:Type) (R: relation X) (x y z : X),
    clos_refl_trans_1n R x y ->
    R y z ->
    clos_refl_trans_1n R x z.
Proof.
  intros X R x y z Hxy Hyz.
  induction Hxy as [| x w y Hxw Hrest].
  * apply rsc_R. apply Hyz.
  * apply IHHrest in Hyz. apply (rt1n_trans R x w z) in Hyz. apply Hyz. apply Hxw.
Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros X R x y z Hxy Hyz.
  generalize dependent x.
  induction Hyz as [y | y w z Hyw Hrest IH].
  * (* rt1n_refl: y = z *) 
    (* intros x Hxy. *)
    intros x Hxy. apply Hxy.
  * (* rt1n_trans *)
    intros x Hxy.
    apply (rsc_trans_1 X R x y w) in Hyw.
    - apply IH in Hyw. apply Hyw.
    - apply Hxy.
Qed.

(** [] *)

(** Then we use these facts to prove that the two definitions of
    reflexive, transitive closure do indeed define the same
    relation. *)

(** **** Exercise: 3 stars, standard, optional (rtc_rsc_coincide) *)

Print clos_refl_trans.

(* 11min *)
Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros X R x y. split.
  * intros H. induction H.
    - apply rsc_R in H. apply H.
    - apply rt1n_refl.
    - apply rsc_trans with y.
        apply IHclos_refl_trans1. apply IHclos_refl_trans2.
  * intros H. induction H.
    - apply rt_refl.
    - apply rt_step in Hxy.
      apply (rt_trans R x y z) in Hxy.
      apply Hxy. apply IHclos_refl_trans_1n. 
Qed.

(** [] *)

(* 2023-12-29 17:12 *)
