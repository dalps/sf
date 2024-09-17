(** * Types: Type Systems *)

(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    _type preservation_ and _progress_.  In chapter [Stlc] we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq!). *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".

Hint Constructors multi : core.

(* ################################################################# *)
(** * Typed Arithmetic Expressions *)

(** To motivate the discussion of type systems, let's begin as
    usual with a tiny toy language.  We want it to have the potential
    for programs to go wrong because of runtime type errors, so we
    need something a tiny bit more complex than the language of
    constants and addition that we used in chapter [Smallstep]: a
    single kind of data (e.g., numbers) is too simple, but just two
    kinds (numbers and booleans) gives us enough material to tell an
    interesting story.

    The language definition is completely routine. *)

(* ================================================================= *)
(** ** Syntax *)

(** Here is the syntax, informally:

    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
*)
(** And here it is formally: *)
Module TM.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

(** _Values_ are [true], [false], and numeric values... *)
Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

(* ================================================================= *)
(** ** Operational Semantics *)

(** Here is the single-step relation, first informally...

                   -------------------------------                   (ST_IfTrue)
                   if true then t1 else t2 --> t1

                   -------------------------------                  (ST_IfFalse)
                   if false then t1 else t2 --> t2

                               t1 --> t1'
            ------------------------------------------------             (ST_If)
            if t1 then t2 else t3 --> if t1' then t2 else t3

                             t1 --> t1'
                         --------------------                          (ST_Succ)
                         succ t1 --> succ t1'

                           ------------                               (ST_Pred0)
                           pred 0 --> 0

                         numeric value v
                        -------------------                        (ST_PredSucc)
                        pred (succ v) --> v

                              t1 --> t1'
                         --------------------                          (ST_Pred)
                         pred t1 --> pred t1'

                          -----------------                         (ST_IsZero0)
                          iszero 0 --> true

                         numeric value v
                      -------------------------                  (ST_IszeroSucc)
                      iszero (succ v) --> false

                            t1 --> t1'
                       ------------------------                      (ST_Iszero)
                       iszero t1 --> iszero t1'
*)

(** ... and then formally: *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' -> (* No guarantee [c'] will be a [bvalue], eventually. *)
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }> (* Applies to [<{succ (is_zero 0)}>] *)
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(** Notice that the [step] relation doesn't care about whether the
    expression being stepped makes global sense -- it just checks that
    the operation in the _next_ reduction step is being applied to the
    right kinds of operands.  For example, the term [succ true] cannot
    take a step, but the almost as obviously nonsensical term

       succ (if true then true else true)

    can take a step (once, before becoming stuck). *)

(* ================================================================= *)
(** ** Normal Forms and Values *)

(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the [Smallstep]
    chapter fails here.  That is, there are terms that are normal
    forms (they can't take a step) but not values (they are not
    included in our definition of possible "results of reduction").

    Such terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t. (* Normal forms that are _not_ values *)

Hint Unfold stuck : core.

(** **** Exercise: 2 stars, standard (some_term_is_stuck) *)

(* 3:55 min *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists <{ iszero true }>.
  unfold stuck, step_normal_form.
  split; intro Contra;
  solve_by_inverts 3.
Qed.
(** [] *)

(** However, although values and normal forms are _not_ the same in this
    language, the set of values is a subset of the set of normal forms.

    This is important because it shows we did not accidentally define
    things so that some value could still take a step. *)

Print nvalue_ind.
(** **** Exercise: 3 stars, standard (value_is_nf) *)

(* 22:30 min - did without hint! *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  unfold step_normal_form, value.
  intros t Vt. destruct Vt as [Vt | Vt].
  - intro Contra. inversion Vt; destruct Contra; subst; solve_by_invert.
  - induction Vt as [| t' Vt' IH];
    intro Contra; destruct Contra as [t'0 Hstep].
    + solve_by_invert.
    + inversion Hstep; subst.
      (* <{succ t'}> advanced by the rule [ST_Succ],
         whose implications contradict the IH. *)
      apply IH. eauto.
Qed.

(** (Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways.)

    [] *)

(** **** Exercise: 3 stars, standard, optional (step_deterministic)

    Use [value_is_nf] to show that the [step] relation is also
    deterministic. *)

(* 41:49 min *)

Lemma solve_nvalue_contra : forall v t,
  nvalue v -> <{ succ v }> --> t -> False.
Proof.
  intros v t Hv Hstep.
  assert (V : value v) by intuition; clear Hv.
  apply value_is_nf in V.
  inversion Hstep; subst. eauto.
Qed.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros x y1 y2 Hxy1. generalize dependent y2.
  induction Hxy1; intros y2 Hy2;
  (* ST_IfTrue, ST_IfFalse, ST_Pred0, ... *)
  try (inversion Hy2; subst; [reflexivity | solve_by_invert]).
  - (* ST_If *)
    inversion Hy2; subst; try solve_by_invert.
    apply IHHxy1 in H3; subst; reflexivity.
  - (* ST_Succ *)
    inversion Hy2; subst.
    apply IHHxy1 in H0; subst; reflexivity.
  - (* ST_PredSucc *)
    inversion Hy2; subst. (* Looks at [pred] only *)
    + (* ST_PredSucc *) reflexivity.
    + (* ST_Pred (simplifies the argument, but argument is already a value!)*)
      destruct (solve_nvalue_contra v t1' H H1).
  - (* ST_Pred *)
    inversion Hy2; subst; try solve_by_invert.
    + (* ST_PredSucc *)
      destruct (solve_nvalue_contra y2 t1' H0 Hxy1).
    + (* ST_Pred *)
      apply IHHxy1 in H0; subst; reflexivity.
  - (* ST_IszeroSucc *)
    inversion Hy2; subst.
    + reflexivity.
    + destruct (solve_nvalue_contra v t1' H H1).
  - (* ST_Iszero *)
    inversion Hy2; subst; try solve_by_invert.
    + destruct (solve_nvalue_contra v t1' H0 Hxy1).
    + apply IHHxy1 in H0; subst; reflexivity.
Qed.

(* todo: Golf this down with Ltac *)

(** [] *)

(* ================================================================= *)
(** ** Typing *)

(** The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

(** In informal notation, the typing relation is often written
    [|-- t \in T] and pronounced "[t] has type [T]."  The [|--] symbol
    is called a "turnstile."  Below, we're going to see richer typing
    relations where one or more additional "context" arguments are
    written to the left of the turnstile.  For the moment, the context
    is always empty.

    
                           -----------------                   (T_True)
                           |-- true \in Bool

                          ------------------                   (T_False)
                          |-- false \in Bool

           |-- t1 \in Bool    |-- t2 \in T    |-- t3 \in T
           -----------------------------------------------     (T_If)
                   |-- if t1 then t2 else t3 \in T

                             --------------                    (T_0)
                             |-- 0 \in Nat

                            |-- t1 \in Nat
                          -------------------                  (T_Succ)
                          |-- succ t1 \in Nat

                            |-- t1 \in Nat
                          -------------------                  (T_Pred)
                          |-- pred t1 \in Nat

                            |-- t1 \in Nat
                          ----------------------               (T_Iszero)
                          |-- iszero t1 \in Bool
*)

Reserved Notation "'|--' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |-- <{ true }> \in Bool
  | T_False :
       |-- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T, (* Note the quantified type variable *)
       |-- t1 \in Bool ->
       |-- t2 \in T ->
       |-- t3 \in T ->
       |-- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |-- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |-- t1 \in Nat ->
       |-- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |-- t1 \in Nat ->
       |-- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |-- t1 \in Nat ->
       |-- <{ iszero t1 }> \in Bool

where "'|--' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  |-- <{ if false then 0 else (succ 0) }> \in Nat.
Proof.
  apply T_If.
  - apply T_False.
  - apply T_0.
  - apply T_Succ. apply T_0.
Qed.

(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not consider
    what happens when the term is reduced -- in particular, it does
    not calculate the type of its normal form. *)

Example has_type_not :
  ~ ( |-- <{ if false then 0 else true}> \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.

(** **** Exercise: 1 star, standard, optional (succ_hastype_nat__hastype_nat) *)

(* 1:47 min *)
Example succ_hastype_nat__hastype_nat : forall t,
  |-- <{succ t}> \in Nat ->
  |-- t \in Nat.
Proof.
  intros t Hsucc. inversion Hsucc; subst. assumption.  Qed.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental fact that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.

    The first is that well-typed normal forms are not stuck -- or
    conversely, if a term is well typed, then either it is a value or it
    can take at least one step.  We call this _progress_. *)


Print step.

(** **** Exercise: 3 stars, standard (finish_progress) *)
Theorem progress : forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t'.

(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.) *)

(* 30:22 min - worked out mostly informally on paper *)
Proof.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_True and
     T_False, are eliminated immediately by auto *)
  - (* T_If *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists (<{ if t1' then t2 else t3 }>). auto.
  - (* T_Succ *)
    destruct IHHT.
    + (* t1 is a value *)
      left. right. constructor. apply (nat_canonical t1 HT H).
    + (* t1 can take a step *)
      right. destruct H as [t1']. eauto.
  - (* T_Pred *)
    destruct IHHT.
    + (* t1 is a value *)
      destruct (nat_canonical t1 HT H); right; eauto.
    + right. destruct H as [t1']. eauto.
  - (* T_Iszero *)
    destruct IHHT.
    + destruct (nat_canonical t1 HT H); right; eauto.
    + right. destruct H as [t1']. eauto.
Qed.

(** [] *)

(** **** Exercise: 3 stars, advanced (finish_progress_informal)

    Complete the corresponding informal proof: *)

(** _Theorem_: If [|-- t \in T], then either [t] is a value or else
    [t --> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|-- t \in T].

    - If the last rule in the derivation is [T_If], then [t = if t1
      then t2 else t3], with [|-- t1 \in Bool], [|-- t2 \in T] and [|-- t3
      \in T].  By the IH, either [t1] is a value or else [t1] can step
      to some [t1'].

      - If [t1] is a value, then by the canonical forms lemmas
        and the fact that [|-- t1 \in Bool] we have that [t1]
        is a [bvalue] -- i.e., it is either [true] or [false].
        If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
        while if [t1 = false], then [t] steps to [t3] by
        [ST_IfFalse].  Either way, [t] can step, which is what
        we wanted to show.

      - If [t1] itself can take a step, then, by [ST_If], so can
        [t].

    - If the last rule in the derivation is [T_Succ], then [t = succ t1],
      with [|-- t1 \in Nat]. By the IH, either [t1] is a value or else
      [t1] can step to some [t1'].

      - If [t1] is a value, then by [nat_canonical] together with the
        fact that [|-- t1 \in Nat] it is an [nvalue], and by the rule
        [nv_succ] we arrive at the conclusion [succ t1] is a value.

      - If [t1] can take a step, then by the rule [ST_Succ], also
        [succ t1] can take a step.

    - The case where the last rule is [T_Pred] is slightly more subtle.
      Here, [t = pred t1] and [|-- t1 \in Nat], with the IH that [t1]
      is either a value or else it can take a step to some [t1'].

      - If [t1] is a value, then it must be an [nvalue]. 
        There are two additional cases to consider: [t1 = 0] or [t1 = succ t2].
        It easy to see that [pred t1] can take a step in either case by the
        rules [ST_Pred0] and [ST_PredSucc] respectively.
      
      - If [t1] can take a step to some other term [t1'], then so can [pred t1]
        by the rule [ST_Pred].

    - If the last rule in the derivation is [T_Iszero], then [t = iszero t1],
      [|-- t1 \in Nat] and by the IH [t1] is either a value or it can take a
      step.

      - If [t1] is a value, then it must be an [nvalue] by [nat_canonical] and
        the fact [|-- t1 \in Nat]. Therefore, [t1] is either [0] or [succ t2]
        for some [t2]. It is easy to see [iszero t1] can make progress in both
        cases by the rules [ST_Iszero0] and [ST_IszeroSucc].

      - If [t1] can take another step to [t1'], then [iszero t1] can take a
        step to [iszero t1'] by the rule [ST_Iszero].

    - The cases where the last rule in the derivation is [T_True], [T_False] or
      [T_Zero], where [t] is trivially a value, are immediate.        []
 *)

(* Do not modify the following line: *)
Definition manual_grade_for_finish_progress_informal : option (nat*string) := None.
(** [] *)

(** This theorem is more interesting than the strong progress theorem
    that we saw in the [Smallstep] chapter, where _all_ normal forms
    were values.  Here a term can be stuck, but only if it is ill
    typed. *)

(* ================================================================= *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is a well-typed term (of the same type). *)

(** **** Exercise: 2 stars, standard (finish_preservation) *)

(* 11:18 min *)

Theorem preservation : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.

(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    - (* T_Succ *) inversion HE; subst.
        (* ST_Succ *) apply T_Succ. apply IHHT; assumption.
    - (* T_Pred *) inversion HE; subst; clear HE.
      + (* ST_Pred0 *) constructor.
      + (* ST_PredSucc *)
        apply succ_hastype_nat__hastype_nat; assumption.
      + (* ST_Pred *) apply T_Pred. apply IHHT; assumption.
    - (* T_Iszero *) inversion HE; subst; try constructor.
        (* ST_Iszero *) apply IHHT; assumption.
Qed.

(** [] *)

(** **** Exercise: 3 stars, advanced (finish_preservation_informal)

    Complete the following informal proof: *)

(* 38:43 min *)

(** _Theorem_: If [|-- t \in T] and [t --> t'], then [|-- t' \in T]. *)

(** _Proof_: By induction on a derivation of [|-- t \in T].

    - If the last rule in the derivation is [T_If], then [t = if t1
      then t2 else t3], with [|-- t1 \in Bool], [|-- t2 \in T] and [|-- t3
      \in T].

      Inspecting the rules for the small-step reduction relation and
      remembering that [t] has the form [if ...], we see that the
      only ones that could have been used to prove [t --> t'] are
      [ST_IfTrue], [ST_IfFalse], or [ST_If].

      - If the last rule was [ST_IfTrue], then [t' = t2].  But we
        know that [|-- t2 \in T], so we are done.

      - If the last rule was [ST_IfFalse], then [t' = t3].  But we
        know that [|-- t3 \in T], so we are done.

      - If the last rule was [ST_If], then [t' = if t1' then t2
        else t3], where [t1 --> t1'].  We know [|-- t1 \in Bool] so,
        by the IH, [|-- t1' \in Bool].  The [T_If] rule then gives us
        [|-- if t1' then t2 else t3 \in T], as required.

    - If the last rule in the derivation is [T_Succ], then [t = succ t1],
      with [|-- t1 \in Nat] and by the IH,
      [forall t', t1 --> t' -> |-- t' in \Nat].

      The only rule that could have been used to deduct [succ t1 --> t'] is
      [ST_Succ], which implies [t' = succ t1'] for some [t1'] and [t1 --> t1'].
      The IH can be applied to the latter to obtain [|-- t1' \in Nat], then,
      the goal easily follows by the [T_Succ] rule.

    - If the last rule in the derivation is [T_Pred], then [t = pred t1],
      with [|-- t1 \in Nat].

      Inspecting the rules of the small-step relation that could have been
      used to derive [pred t1 --> t'], we see that the only plausible ones are
      [ST_Pred0], [ST_PredSucc] and [ST_Pred].

      - If it was [ST_Pred0], then [t' = 0], which is obviously a [Nat].

      - If the last rule was [ST_PredSucc], then [t1 = succ t1']
        for some [t1'] that is an [nvalue], and [t' = t1']. In other words,
        [t = pred (succ t1')] was reduced to the [nvalue] [t1'].
        We must prove [|-- t1' \in Nat]. This is easy to see, if we
        remember that [|-- t1 \in Nat]. Rewriting [t1 = succ t1'] in
        this fact we get [|-- succ t1' \in Nat], which is sufficient evidence
        to prove [t1'] is also a [Nat].

    - If the last rule in the derivation is [T_Iszero], then [t = iszero t1],
      with [|-- t1 \in Nat]. Knowing [|-- iszero t1 \in Bool ], we must show
      whatever [iszero t1] steps to is still a [Bool].

      There are three cases to consider:

      - If [iszero t1] steps to [t'] by the rule [ST_Iszero0],
        then [t1 = 0] and [t' = true], which is obviously a [Bool].

      - If [iszero t1] steps to [t'] by the rule [ST_IszeroSucc], then
        [t1 = succ v] for some [v] that is an [nvalue], and [t' = false],
        which is obviously a [Bool].

      - If the last step was made by the rule [ST_Iszero], we have that
        [t1 --> t1']. The the goal easily follows from the rule [T_Iszero]
        and the IH.                                                   []

*)
(* Do not modify the following line: *)
Definition manual_grade_for_finish_preservation_informal : option (nat*string) := None.
(** [] *)

Print step.
Print step_ind.
Print has_type.

(** **** Exercise: 3 stars, standard (preservation_alternate_proof)

    Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proofs to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

(* 38:09 min - Had a go at the informal proof too *)
Theorem preservation' : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof with eauto.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT;
  inversion HT; subst;
  try auto using succ_hastype_nat__hastype_nat.
Qed.

(*
  - (* ST_IfTrue *)
    inversion HT; subst; assumption.
  - (* ST_IfFalse *)
    inversion HT; subst; assumption.
  - (* ST_If *)
    inversion HT; subst. constructor; try assumption.
    apply IHHE; assumption.
  - (* ST_Succ *)
    inversion HT; subst. constructor. apply IHHE; assumption.
  - (* ST_Pred0 *)
    inversion HT; subst. constructor.
  - (* ST_PredSucc *) 
    inversion HT; subst. inversion H1; assumption.
  - (* ST_Pred *)
    inversion HT; subst. constructor. apply IHHE; assumption. *)

(** [] *)

(** _Theorem_: If [|-- t \in T] and [t --> t'], then [|-- t' \in T].

    _Proof_: By induction on a derivation of [t --> t'].

    - If the last rule in the derivation is [ST_IfTrue], [t = if true then t1
      else t2] for some [t1] and [t2], and we must show [|-- t1 \in T].

      Inspecting the possible rules of the typing relation, we see that the
      only one that could have been used to prove [|-- if ... \in T], is
      [T_If]. One of the implications of this rule is that [|-- t1 \in T],
      which is exactly what we're after.

    - The case of [ST_IfFalse] is identical.

    - If the last rule in the derivation is [ST_If],
      then [t = if t1 then t2 else t3], [t' = if t1' then t2 else t3],
      [t1 --> t1'] and the IH asserting that the type of [t1] is preserved.

      By reasoning with the assumptions of the typing derivation of [t],
      we get that [|-- t1 \in Bool], [|-- t2 \in T] and [|-- t3 \in T].
      
      In order to prove [|-- if t1' then t2 else t3 \in T], we apply the
      rule [T_If], which leaves us to show [|-- t1' \in Bool].
      But this follows from the IH and the fact that [|-- t1 \in Bool],
      and we're done.

    - ... (tedious, you get the gist.)                                  []
*)

(** The preservation theorem is often called _subject reduction_,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

(* ================================================================= *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |-- t \in T ->
  t -->* t' ->
  ~(stuck t').

(* 18:54 min - personal attempt
  Proof.
    intros t t' T HT HE. unfold stuck.
    intros [NF NotV].
    induction HE as [t | t t0 t' Hone Hmany]; subst.
    - destruct (progress t T HT); contradiction.
    - eapply preservation in Hone; eauto.
  Qed. *)

Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + unfold stuck. split; auto.
Qed.

(* ================================================================= *)
(** ** Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (subject_expansion)

    Having seen the subject reduction property, one might
    wonder whether the opposite property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t --> t']
    and [|-- t' \in T], then [|-- t \in T]?  If so, prove it.  If
    not, give a counter-example.

    (* FILL IN HERE *)
*)

(** [t'] is well typed and it has a predecessor [t],
    but [t] is not well-typed. This happens, for example,
    when the expansion introduces new terms. *)
Example sub_exp_counter :
  <{ if true then 0 else true }> --> <{ 0 }>.
Proof. auto.  Qed.

Print step.

(* 36:10 min *)
Theorem subject_expansion:
  (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T)
  \/
  ~ (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T).
Proof.
  right. intro C.
  assert (H : <{ if true then 0 else true }> --> <{ 0 }> /\
              |-- <{ 0 }> \in Nat) by auto.
  apply C in H. solve_by_inverts 2.
Qed.

(** [] *)

Example step_succbool :
  <{ succ (iszero 0) }> -->* <{ succ true }>.
Proof.
  eapply multi_step; auto.  Qed.

Example step_succ1 :
  <{ succ (if true then 0 else succ 0) }> -->* <{ succ 0 }>.
Proof.
  eapply multi_step; auto.  Qed.

Check progress.
Check preservation.
Print has_type.

(** **** Exercise: 2 stars, standard (variation1)

(* 21:38 min *)

    Suppose that we add this new rule to the typing relation:

      | T_SuccBool : forall t,
           |-- t \in Bool ->
           |-- <{ succ t }> \in Bool

   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]
            remains true. [step] is unaltered.
            
      - Progress
            becomes false.

            Counterexample: [succ (iszero 0)] is well-typed,
            however it gets stuck after reaching [succ true],
            which is not a value.

      - Preservation
            remains true. If [succ ...] has type [Bool], by the new rule
            its argument must also have type Bool. If [succ ...] has type
            [Nat], by [T_Succ] its argument must have type [Nat].
            The new rule doesn't interfere with [T_Succ].
*)
(* Do not modify the following line: *)
Definition manual_grade_for_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (variation2)

(* ~ 15 min *)

    Suppose, instead, that we add this new rule to the [step] relation:

      | ST_Funny1 : forall t2 t3,
           (<{ if true then t2 else t3 }>) --> t3

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
        - Determinism of [step]
            becomes false. Both [ST_IfTrue] and [ST_Funny1] apply to
            a term of the form [if true then ...], with branching results.

            For example, we have both:
            - if true then 0 else succ 0 --> 0        by [ST_IfTrue], and
            - if true then 0 else succ 0 --> succ 0   by [ST_Funny1]
            
      - Progress
            remains true.

      - Preservation
            remains true. The typing rule for if-then-else ensures that
            [t2] and [t3] have the same type. So if a term of the form
            [if true ...] is typable, then its branches must have the
            same type no matter which step choice is taken. This is
            the type of whole conditional.
*)
(* Do not modify the following line: *)
Definition manual_grade_for_variation2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation3)

(* 7:19 min *)

    Suppose instead that we add this rule:

      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 --> t2' ->
           (<{ if t1 then t2 else t3 }>) --> (<{ if t1 then t2' else t3 }>)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
      - Determinism of [step]
            becomes false.

            For example, we have both:
            - if false then pred succ 0 else succ 0 --> 0     by [ST_IfFalse]
            - if false then pred succ 0 else succ 0 -->
                if false then 0 else succ 0                   by [ST_Funny2]
            
      - Progress
            remains true.

      - Preservation
            remains true. The typing rule for if-then-else ensures that
            [t2] and [t3] have the same type.
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation4)

(* ~ 15 min *)

    Suppose instead that we add this rule:

      | ST_Funny3 :
          (<{pred false}>) --> (<{ pred (pred false)}>)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
      - Determinism of [step]
          remains true. No old rule of [step] applies to [pred false]
          prior to introducing [ST_Funny3]. Moreover, there's at most one
          rule that can be applied to [pred (pred false)], which is [ST_Pred].

      - Progress
          remains true, because [pred false] is ill-typed.
          Progress concerns only well-typed terms, saying that they
          are either values or the can make progress. It does not warrant
          the same property for ill-typed terms. The fact that [pred false]
          and its derivatives can make progress is just a coincidence.

          vvv WRONG REASON vvv
          By [ST_Funny3], [pred false] takes a step to [pred (pred false)].
          Then, by [ST_Pred] first and [ST_Funny3],
          [pred (pred false)] can take a step to [pred (pred (pred false))].
          This process can be repeated infinite times, applying [ST_Pred]
          repeatedly to reach a node where [ST_Funny3] applies.
          Such a term does not converge to a value.
            
      - Preservation
          remains true, because [pred false] is ill-typed.
*)

Check progress.
Print step.
Check bool_canonical.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation5)

(* ~16 min *)

    Suppose instead that we add this rule:

      | T_Funny4 :
            |-- <{ 0 }> \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
      - Determinism of [step]
          remains true. [step] is unaltered.
          
      - Progress
          remains true, since we can still prove [value 0].

          vvv WRONG vvv
          becomes false, because it goes against [bool_canonical]:

          [0] can be typed to [Bool], and it also a value. By applying [bool_canonical] we have that it is also a [bvalue], which is
          impossible.
          
      - Preservation
          remains true. One of the hypotheses, namely [0 --> t'],
          doesn't hold for any choice of [t'].
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation6)

(* ~ 10 min *)

    Suppose instead that we add this rule:

      | T_Funny5 :
            |-- <{ pred 0 }> \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
      - Determinism of [step]
          remains true. [step] is unaltered.

      - Progress
          remains true. [pred 0] may still take a step to [0].

      - Preservation
          becomes false. In fact [pred 0 --> 0] by rule [ST_Pred0],
          but [0] has type [Nat]!
*)
(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_variations)

    Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
*)
(*

  35:30 min - sooner or later I'll fact-check my answers
  
    Suppose we want to add this rule:

      | T_Bogus1: forall t1 t2 t3,
          |-- t1 \in Bool ->
          |-- t2 \in Nat  ->
          |-- t3 \in Bool ->
            |-- if t1 then t2 else t3 \in Bool

    Then:
      - Determinism of [step]
          remains true. [step] is unaltered.

      - Progress
          remains true. Thanks to the typing constraint of the
          guard, the rules [ST_IfTrue] and [ST_IfFalse] and
          [ST_If] still apply normally.

      - Preservation
          becomes false. For example, we have
          [|-- if true then 0 else false \in Bool] holds, and
          [if true then 0 else false --> 0], however
          the type of [0] is not [Bool].

    ###

    Suppose we want to add this rule:

      | T_Bogus2: forall t1 t2 t3 T1 T2 T3,
          |-- t1 \in Bool ->
          |-- t2 \in T1  ->
          |-- t3 \in T2 ->
            |-- if t1 then t2 else t3 \in T3

    Then:
      - Determinism of [step]
          remains true. [step] is unaltered.

      - Progress
          remains true. As long as the guard of if-then-else has type [Bool],
          we are guaranteed it will reach either [true] or [false] and
          therefore one of small-step relation rules for if-then-else will
          always apply.

      - Preservation
          becomes false. For the term [if true then 0 else false], which
          reduces to [0], we can choose [T3] to be [Bool] to have a
          contradiction.

    ###

    Suppose we want to add this rule:

      | T_Bogus3: forall t1 t2 t3 T1 T2 T3,
          |-- t1 \in T1 ->
          |-- t2 \in T2  ->
          |-- t3 \in T3 ->
            |-- if t1 then t2 else t3 \in T2

    Then:
      - Determinism of [step]
          remains true. [step] is unaltered and its
          determinism doesn't depend on types.

      - Progress
          becomes false. There's no guarantee that the guard will reach
          - or is - a boolean value, therefore a well-typed if-then-else
          may be stuck. Consider [if 0 then true else false] for example.

      - Preservation
          becomes false.
          For example, [|-- if false then 0 else false \in Nat] holds by
          [T_Bogus3] and it also rewrites to [false] by [ST_IfFalse],
          despite this [|-- false \in Nat] can't be proved.

    ###

    Suppose we want to add this rule:

      | T_Bogus4: forall t1 t2 t3 T2 T3,
          |-- t1 \in Bool ->
          |-- t2 \in T2  ->
          |-- t3 \in T3 ->
            |-- if t1 then t2 else t3 \in T2

    Then:
      - Determinism of [step]
          remains true. [step] is unaltered.

      - Progress
          remains true. It suffices the guard of an if-then-else
          reaches a [Bool] for it to make progress.

      - Preservation
          becomes false.
          For example, [|-- if false then 0 else false \in Nat] holds by
          [T_Bogus4] and it also rewrites to [false] by [ST_IfFalse],
          despite this [|-- false \in Nat] can't be proved.
    [] *)

Print tm.
Print has_type.

(** **** Exercise: 1 star, standard (remove_pred0)

  10:39 min

    The reduction rule [ST_Pred0] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of [0] to
    be undefined, rather than being defined to be [0].  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere?

    Yes, only removing it from the small-step relation would create problems.
    For one, [progress] becomes false, since [|-- pred 0 \in Nat] holds,
    but [pred 0] is a stuck term now.

    Removing the typing rule [T_Pred] in addition to this wouldn't be a
    sensible move either, as we wouldn't be able to type-check [pred (succ 0)],
    for example.

    The best way to go about this is to create a new type that denotes
    "natural numbers without 0" and restrict the type assumption of the
    [T_Pred] rule to this domain.
*)
(* Do not modify the following line: *)
Definition manual_grade_for_remove_pred0  : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (prog_pres_bigstep)

    Suppose our evaluation relation is defined in the big-step style.
    State appropriate analogs of the progress and preservation
    properties. (You do not need to prove them.)

    Can you see any limitations of either of your properties?  Do they
    allow for nonterminating programs?  Why might we prefer the
    small-step semantics for stating preservation and progress?

  ~ 1:30 hour (experimenting and lots of distractions in the way)

    Answer:

      - The [progress] property is restated as:

        forall t T, |-- t \in T -> exists v, t ==>b v.

        To paraphrase it, if a term [t] is well-typed, then it will
        evaluate to a value by the big-step relation. [progress] is
        not an appropriate name for this property, I'd rename it to
        [termination].

        This property has the shortcoming that it doesn't hold
        if the big-step relation allows for nonterminating programs.
        
        In fact, while a nonterminating program can be successfully
        typed by static analysis, there is no definite value ==>b can
        reduce it to.

        Conversely, a small-step relation is always able to make
        progress in a non-terminating program and compute the next
        term in its execution.

      - The [preservation] property is restated as:

        forall t v T, |-- t \in T -> t ==>b v -> |--b v \in T.

        It says that if a program [t] has a type [T] and it
        evaluates to a value [v], then [v] "agrees with" [T].

        A weakness of this property is that it requires a secondary
        typing relation to connect the values to types.

      Proving the properties for the big-step relations is more hacky,
      also it's harder to rework the proofs if we were to extend the
      language with new types or new functionality.
*)

Check value.
Print tm.

Reserved Notation "t '==>b' t'" (at level 40, t' at level 39).

Inductive result :=
  | Rbool (b : bool)
  | Rnat (n : nat).

(* 34:13 min *)

Inductive eval : tm -> result -> Prop :=
  | BS_0 : <{ 0 }> ==>b Rnat 0
  | BS_True : <{ true }> ==>b Rbool true
  | BS_False : <{ false }> ==>b Rbool false
  | BS_IfTrue : forall t1 t2 t3 v,
      t1 ==>b Rbool true  ->
      t2 ==>b v           -> <{ if t1 then t2 else t3 }> ==>b v
  | BS_IfFalse : forall t1 t2 t3 v,
      t1 ==>b Rbool false ->
      t3 ==>b v           -> <{ if t1 then t2 else t3 }> ==>b v
  | BS_Succ : forall t1 n,
      t1 ==>b Rnat n      -> <{ succ t1 }> ==>b Rnat (1+n)
  | BS_Pred : forall t1 n,
      t1 ==>b Rnat n      -> <{ pred t1 }> ==>b Rnat (Nat.pred n)
  | BS_Iszero : forall t1 n,
      t1 ==>b Rnat n      -> <{ iszero t1 }> ==>b Rbool (n =? 0)
where "t '==>b' t'" := (eval t t').

Hint Constructors eval : core.

Example eval_test_1 :
  <{ if iszero (pred (succ 0)) then succ 0 else succ (succ 0) }>
    ==>b Rnat 1.
Proof.
  apply BS_IfTrue; try auto.
  replace true with (0 =? 0) by reflexivity.
  apply BS_Iszero.
  replace 0 with (Nat.pred 1) by reflexivity.
  auto.
Qed.

Theorem progress_bool : forall t,
  |-- t \in Bool -> exists b, t ==>b Rbool b.
Proof.
  intros t HT.
  remember Bool as T.
  induction HT; eauto; try solve_by_invert.
  - (* T_If *) destruct IHHT1 as [[]]; try reflexivity.
    + destruct IHHT2 as [b2]; eauto.
    + destruct IHHT3 as [b3]; eauto.
  - (* T_Iszero *) clear IHHT.
    (* I'm in trouble... I need mutually recursive theorems! *)
Abort.

Theorem progress_r : forall t T,
  |-- t \in T ->
  exists v, t ==>b v.
Proof.
  intros t T HT.
  induction HT; eauto.
  - (* T_If *) destruct IHHT1 as [[[] | n]].
    + destruct IHHT2 as [v2]. exists v2; auto.
    + destruct IHHT3 as [v3]. exists v3; auto.
    + inversion H; subst.
Abort.

Inductive result_ty : result -> ty -> Prop :=
  | Rbool__Bool : forall b, result_ty (Rbool b) Bool
  | Rnat__Nat : forall n, result_ty (Rnat n) Nat.

Notation "'|--b' r '\in' T" := (result_ty r T) (at level 40).

Theorem preservation_r : forall t T v,
  |-- t \in T ->
  t ==>b v ->
  |--b v \in T.
Proof. Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_prog_pres_bigstep : option (nat*string) := None.
(** [] *)
End TM.

(* 2024-01-03 15:04 *)
