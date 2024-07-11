Definition ltb (n m : nat) : bool :=
  (* (n <=? m) && (negb (n =? m)). I don't know how you'd do it without using both functions and also without recursion *)
  match minus n m, minus m n with
  | O, O => false
  | O, _ => true
  | _, _ => false
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

(* ================================================================= *)
(** ** Course Late Policies, Formalized *)

(** Suppose that a course has a grading policy based on late days,
    where a student's final letter grade is lowered if they submit too
    many homework assignments late.

    In the next series of problems, we model this situation using the
    features of Coq that we have seen so far and prove some simple
    facts about this grading policy.  *)

Module LateDays.

(** First, we inroduce a datatype for modeling the "letter" component
    of a grade. *)
Inductive letter : Type :=
  | A | B | C | D | F.

(** Then we define the modifiers -- a [Natural] [A] is just a "plain"
    grade of [A]. *)
Inductive modifier : Type :=
  | Plus | Natural | Minus.

(** A full [grade], then, is just a [letter] and a [modifier].

    We might write, informally, "A-" for the Coq value [Grade A Minus],
    and similarly "C" for the Coq value [Grade C Natural]. *)
Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

(** We will want to be able to say when one grade is "better" than
    another.  In other words, we need a way to compare two grades.  As
    with natural numbers, we could define [bool]-valued functions
    [grade_eqb], [grade_ltb], etc., and that would work fine.
    However, we can also define a slightly more informative type for
    comparing two values, as shown below.  This datatype has three
    constructors that can be used to indicate whether two values are
    "equal", "less than", or "greater than" one another. (This
    definition also appears in the Coq standard libary.)  *)

Inductive comparison : Type :=
  | Eq         (* "equal" *)
  | Lt         (* "less than" *)
  | Gt.        (* "greater than" *)

(** Using pattern matching, it is not difficult to define the
    comparison operation for two letters [l1] and [l2] (see below).
    This definition uses two features of [match] patterns: First,
    recall that we can match against _two_ values simultaneously by
    separating them and the corresponding patterns with comma [,].
    This is simply a convenient abbreviation for nested pattern
    matching.  For example, the match expression on the left below is
    just shorthand for the lower-level "expanded version" shown on the
    right:

  match l1, l2 with          match l1 with
  | A, A => Eq               | A => match l2 with
  | A, _ => Gt                      | A => Eq
  end                               | _ => Gt
                                    end
                             end
*)
(** As another shorthand, we can also match one of several
    possibilites by using [|] in the pattern.  For example the pattern
    [C , (A | B)] stands for two cases: [C, A] and [C, B]. *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

(** We can test the [letter_comparison] operation by trying it out on a few
    examples. *)
Compute letter_comparison B A.
(** ==> Lt *)
Compute letter_comparison D D.
(** ==> Eq *)
Compute letter_comparison B F.
(** ==> Gt *)

(** As a further sanity check, we can prove that the
    [letter_comparison] function does indeed give the result [Eq] when
    comparing a letter [l] against itself.  *)
(** **** Exercise: 1 star, standard (letter_comparison) *)
Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
  intros [].
  * reflexivity.
  * reflexivity.
  * reflexivity.
  * reflexivity.
  * reflexivity. 
Qed.
(** [] *)

(** We can follow the same strategy to define the comparison operation
    for two grade modifiers.  We consider them to be ordered as
    [Plus > Natural > Minus]. *)
Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

(** **** Exercise: 2 stars, standard (grade_comparison)

    Use pattern matching to complete the following definition.

    (This ordering on grades is sometimes called "lexicographic"
    ordering: we first compare the letters, and we only consider the
    modifiers in the case that the letters are equal.  I.e. all grade
    variants of [A] are greater than all grade variants of [B].)

    Hint: match against [g1] and [g2] simultaneously, but don't try to
    enumerate all the cases.  Instead do case analysis on the result
    of a suitable call to [letter_comparison] to end up with just [3]
    possibilities. *)

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 => 
    match letter_comparison l1 l2 with
    | Eq => modifier_comparison m1 m2
    | c => c
    end
  end.

Theorem grade_comparison_unfold :
  forall (g1 g2 : grade), grade_comparison g1 g2 =
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 => 
    match letter_comparison l1 l2 with
    | Eq => modifier_comparison m1 m2
    | c => c
    end
  end.
Proof.
  intros. reflexivity.
Qed.

(** The following "unit tests" of your [grade_comparison] function
    should pass once you have defined it correctly. *)

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

(** [] *)

(** Now that we have a definition of grades and how they compare to
    one another, let us implement a late-penalty fuction. *)

(** First, we define what it means to lower the [letter] component of
    a grade.  Since [F] is already the lowest grade possible, we just
    leave it alone.  *)
Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F  (* Can't go lower than [F]! *)
  end.

(** Our formalization can already help us understand some corner cases
    of the grading policy.  For example, we might expect that if we
    use the [lower_letter] function its result will actually be lower,
    as claimed in the following theorem.  But this theorem is not
    provable!  (Do you see why?) *)
Theorem lower_letter_lowers: forall (l : letter),
  letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. (* We get stuck here. *)
Abort.

(** The problem, of course, has to do with the "edge case" of lowering
    [F], as we can see like this: *)
Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

(** With this insight, we can state a better version of the lower
    letter theorem that actually is provable.  In this version, the
    hypothesis about [F] says that [F] is strictly smaller than [l],
    which rules out the problematic case above. In other words, as
    long as [l] is bigger than [F], it will be lowered. *)
(** **** Exercise: 2 stars, standard (lower_letter_lowers)

    Prove the following theorem. *)

Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
  intros [] H.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * rewrite <- H. simpl. reflexivity.
Qed. 

(** [] *)

(** **** Exercise: 2 stars, standard (lower_grade)

    We can now use the [lower_letter] definition as a helper to define
    what it means to lower a grade by one step.  Complete the
    definition below so that it sends a grade [g] to one step lower
    (unless it is already [Grade F Minus], which should remain
    unchanged).  Once you have implemented it correctly, the subsequent
    "unit test" examples should hold trivially.

    Hint: To make this a succinct definition that is easy to prove
    properties about, you will probably want to use nested pattern
    matching. The outer match should not match on the specific letter
    component of the grade -- it should consider only the modifier.
    You should definitely _not_ try to enumerate all of the
    cases.

    Our solution is under 10 lines of code total. *)
Definition lower_grade (g : grade) : grade :=
  match g with
  | Grade l Plus => Grade l Natural
  | Grade l Natural => Grade l Minus
  | Grade F Minus => g
  | Grade l Minus => Grade (lower_letter l) Plus
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
  simpl. reflexivity. Qed.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
  simpl. reflexivity. Qed.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
  simpl. reflexivity. Qed.

Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
  simpl. reflexivity. Qed.

Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
  simpl. reflexivity. Qed.

Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
  simpl. reflexivity. Qed.

Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
  simpl. reflexivity. Qed.

(** Coq makes no distinction between an [Example] and a [Theorem]. We
    state the following as a [Theorem] only as a hint that we will use
    it in proofs below. *)
Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof.
  simpl. reflexivity. Qed.

(* GRADE_THEOREM 0.25: lower_grade_A_Plus *)
(* GRADE_THEOREM 0.25: lower_grade_A_Natural *)
(* GRADE_THEOREM 0.25: lower_grade_A_Minus *)
(* GRADE_THEOREM 0.25: lower_grade_B_Plus *)
(* GRADE_THEOREM 0.25: lower_grade_F_Natural *)
(* GRADE_THEOREM 0.25: lower_grade_twice *)
(* GRADE_THEOREM 0.25: lower_grade_thrice *)
(* GRADE_THEOREM 0.25: lower_grade_F_Minus

    [] *)

(** **** Exercise: 3 stars, standard (lower_grade_lowers)

    Prove the following theorem, which says that, as long as the grade
    starts out above F-, the [lower_grade] option does indeed lower
    the grade.  As usual, destructing everything in sight is _not_ a
    good idea.  Judicious use of [destruct] along with rewriting is a
    better strategy.

    Hint: If you defined your [grade_comparison] function as
    suggested, you will need to rewrite using [letter_comparison_Eq]
    in two cases.  The remaining case is the only one in which you
    need to destruct a [letter].  The case for [F] will probably
    benefit from [lower_grade_F_Minus].  *)

Definition letter_of_grade (g : grade) : letter :=
  match g with
  | Grade l _ => l
  end.

Definition modifier_of_grade (g : grade) : modifier :=
  match g with
  | Grade _ m => m
  end.

Lemma grade_comparison_letter_Eq :
  forall g1 g2, letter_of_grade g1 = letter_of_grade g2 ->
  grade_comparison g1 g2 = modifier_comparison (modifier_of_grade g1) (modifier_of_grade g2).
Proof. Admitted.

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
  intros g. destruct g as [l m] eqn:Eg.
  (* I don't know how to apply letter_comparison_Eq *)
  destruct l eqn:El.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + rewrite lower_grade_F_Minus. intros H. rewrite H. 
        reflexivity.
  Qed.
(** [] *)

(** Now that we have implemented and tested a function that lowers a
    grade by one step, we can implement a specific late-days policy.
    Given a number of [late_days], the [apply_late_policy] function
    computes the final grade from [g], the initial grade.

    This function encodes the following policy:

      # late days     penalty
         0 - 8        no penalty
         9 - 16       lower grade by one step (A+ => A, A => A-, A- => B+, etc.)
        17 - 20       lower grade by two steps
          >= 21       lower grade by three steps (a whole letter)
*)
Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

(** Sometimes it is useful to be able to "unfold" a definition to be
    able to make progress on a proof.  Soon, we will see how to do this
    in a much simpler way automatically, but for now, it is easy to prove
    that a use of any definition like [apply_late_policy] is equal to its
    right hand side just by using reflexivity.

    This result is useful because it allows us to use [rewrite] to
    expose the internals of the definition. *)
Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g  else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
Proof.
  intros. reflexivity.
Qed.

(** Now let's prove some properties about this policy. *)

(** The next theorem states that if a student accrues no more than eight
    late days throughout the semester, their grade is unaffected. It
    is easy to prove: once you use the [apply_late_policy_unfold] you
    can rewrite using the hypothesis. *)

(** **** Exercise: 2 stars, standard (no_penalty_for_mostly_on_time) *)
Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof.
  intros. rewrite apply_late_policy_unfold. rewrite H. reflexivity. 
Qed.
(** [] *)

(** The following theorem states that, if a student has between 9 and
    16 late days, their final grade is lowered by one step. *)

(** **** Exercise: 2 stars, standard (graded_lowered_once) *)
Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (grade_comparison (Grade F Minus) g = Lt) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
  intros late_days g H1 H2 HF. rewrite apply_late_policy_unfold.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(** [] *)
End LateDays.

(* ================================================================= *)
(** ** Binary Numerals *)

(** **** Exercise: 3 stars, standard (binary)

    We can generalize our unary representation of natural numbers to
    the more efficient binary representation by treating a binary
    number as a sequence of constructors [B0] and [B1] (representing 0s
    and 1s), terminated by a [Z]. For comparison, in the unary
    representation, a number is a sequence of [S] constructors terminated
    by an [O].

    For example:

        decimal               binary                          unary
           0                       Z                              O
           1                    B1 Z                            S O
           2                B0 (B1 Z)                        S (S O)
           3                B1 (B1 Z)                     S (S (S O))
           4            B0 (B0 (B1 Z))                 S (S (S (S O)))
           5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
           6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
           7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
           8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))

    Note that the low-order bit is on the left and the high-order bit
    is on the right -- the opposite of the way binary numbers are
    usually written.  This choice makes them easier to manipulate.

    (Comprehension check: What unary numeral does [B0 Z] represent?) *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

(** Complete the definitions below of an increment function [incr]
    for binary numbers, and a function [bin_to_nat] to convert
    binary numbers to unary numbers. *)

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 m' => 2 * (bin_to_nat m')
  | B1 m' => 1 + 2 * (bin_to_nat m') 
  end.

(** The following "unit tests" of your increment and binary-to-unary
    functions should pass after you have defined those functions correctly.
    Of course, unit tests don't fully demonstrate the correctness of
    your functions!  We'll return to that thought at the end of the
    next chapter. *)

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr7 :
        bin_to_nat (B1 (B0 (B0 (B1 Z)))) = 9.
Proof. simpl. reflexivity. Qed.

(** [] *)

(* ################################################################# *)
(** * Testing Your Solutions *)

(** Each SF chapter comes with a test file containing scripts that
    check whether you have solved the required exercises. If you're
    using SF as part of a course, your instructor will likely be
    running these test files to autograde your solutions. You can also
    use these test files, if you like, to make sure you haven't missed
    anything.

    (Important: This step is _optional_: if you've completed all the
    non-optional exercises and Coq accepts your answers, this already
    shows that you are in good shape.)

    The test file for this chapter is [BasicsTest.v]. To run it, make
    sure you have saved [Basics.v] to disk.  Then do this: [[ coqc -Q
    . LF Basics.v coqc -Q . LF BasicsTest.v ]] (Make sure you do this
    in a directory that also contains a file named [_CoqProject]
    containing the single line [-Q . LF].)

    If you accidentally deleted an exercise or changed its name, then
    [make BasicsTest.vo] will fail with an error that tells you the
    name of the missing exercise.  Otherwise, you will get a lot of
    useful output:

    - First will be all the output produced by [Basics.v] itself.  At
      the end of that you will see [COQC BasicsTest.v].

    - Second, for each required exercise, there is a report that tells
      you its point value (the number of stars or some fraction
      thereof if there are multiple parts to the exercise), whether
      its type is ok, and what assumptions it relies upon.

      If the _type_ is not [ok], it means you proved the wrong thing:
      most likely, you accidentally modified the theorem statement
      while you were proving it.  The autograder won't give you any
      points in this case, so make sure to correct the theorem.

      The _assumptions_ are any unproved theorems which your solution
      relies upon.  "Closed under the global context" is a fancy way
      of saying "none": you have solved the exercise. (Hooray!)  On
      the other hand, a list of axioms means you haven't fully solved
      the exercise. (But see below regarding "Allowed Axioms.") If the
      exercise name itself is in the list, that means you haven't
      solved it; probably you have [Admitted] it.

    - Third, you will see the maximum number of points in standard and
      advanced versions of the assignment.  That number is based on
      the number of stars in the non-optional exercises.  (In the
      present file, there are no advanced exercises.)

    - Fourth, you will see a list of "Allowed Axioms".  These are
      unproven theorems that your solution is permitted to depend
      upon, aside from the fundamental axioms of Coq's logic.  You'll
      probably see something about [functional_extensionality] for
      this chapter; we'll cover what that means in a later chapter.

    - Finally, you will see a summary of whether you have solved each
      exercise.  Note that summary does not include the critical
      information of whether the type is ok (that is, whether you
      accidentally changed the theorem statement): you have to look
      above for that information.

    Exercises that are manually graded will also show up in the
    output.  But since they have to be graded by a human, the test
    script won't be able to tell you much about them.  *)

(* 2023-12-29 17:12 *)

