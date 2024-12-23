(** * Sub: Subtyping *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Concepts *)

(** We now turn to _subtyping_, a key feature of -- in
    particular -- object-oriented programming languages. *)

(* ================================================================= *)
(** ** A Motivating Example *)

(** Suppose we are writing a program involving two record types
    defined as follows:

      Person  = {name:String, age:Nat}
      Student = {name:String, age:Nat, gpa:Nat}
*)

(** In the simply typed lamdba-calculus with records, the term

      (\r:Person, (r.age)+1) {name="Pat",age=21,gpa=1}

   is not typable, since it applies a function that wants a two-field
   record to an argument that actually provides three fields, while the
   [T_App] rule demands that the domain type of the function being
   applied must match the type of the argument precisely.

   But this is silly: we're passing the function a _better_ argument
   than it needs!  The only thing the body of the function can
   possibly do with its record argument [r] is project the field [age]
   from it: nothing else is allowed by the type, and the presence or
   absence of an extra [gpa] field makes no difference at all.  So,
   intuitively, it seems that this function should be applicable to
   any record value that has at least an [age] field. (* note: even the parameter type is too strong, the body is typable with whatever record type specifying an [age] field *)

   More generally, a record with more fields is "at least as good in
   any context" as one with just a subset of these fields, in the
   sense that any value belonging to the longer record type can be
   used _safely_ in any context expecting the shorter record type.  If
   the context expects something with the shorter type but we actually
   give it something with the longer type, nothing bad will
   happen (formally, the program will not get stuck).

   The principle at work here is called _subtyping_.  We say that "[S]
   is a subtype of [T]", written [S <: T], if a value of type [S] can
   safely be used in any context where a value of type [T] is
   expected.  The idea of subtyping applies not only to records, but
   to all of the type constructors in the language -- functions,
   pairs, etc. *)

(** Safe substitution principle:

       - [S] is a subtype of [T], written [S <: T], if a value of type
         [S] can safely be used in any context where a value of type
         [T] is expected.
*)

(* ================================================================= *)
(** ** Subtyping and Object-Oriented Languages *)

(** Subtyping plays a fundamental role in many programming
    languages -- in particular, it is central to the design of
    object-oriented languages and their libraries.

    An _object_ in Java, C[#], etc. can be thought of as a record,
    some of whose fields are functions ("methods") and some of whose
    fields are data values ("fields" or "instance variables").
    Invoking a method [m] of an object [o] on some arguments [a1..an]
    roughly consists of projecting out the [m] field of [o] and
    applying it to [a1..an].

    The type of an object is called a _class_ -- or, in some
    languages, an _interface_.  It describes which methods and which
    data fields the object offers.  Classes and interfaces are related
    by the _subclass_ and _subinterface_ relations.  An object
    belonging to a subclass (or subinterface) is required to provide
    all the methods and fields of one belonging to a superclass (or
    superinterface), plus possibly some more.

    The fact that an object from a subclass can be used in place of
    one from a superclass provides a degree of flexibility that is
    extremely handy for organizing complex libraries.  For example, a
    GUI toolkit like Java's Swing framework might define an abstract
    interface [Component] that collects together the common fields and
    methods of all objects having a graphical representation that can
    be displayed on the screen and interact with the user, such as the
    buttons, checkboxes, and scrollbars of a typical GUI.  A method
    that relies only on this common interface can now be applied to
    any of these objects.

    Of course, real object-oriented languages include many other
    features besides these.  For example, fields can be updated.
    Fields and methods can be declared "private".  Classes can give
    _initializers_ that are used when constructing objects.  Code in
    subclasses can cooperate with code in superclasses via
    _inheritance_.  Classes can have static methods and fields.  Etc.,
    etc.

    To keep things simple here, we won't deal with any of these
    issues -- in fact, we won't even talk any more about objects or
    classes.  (There is a lot of discussion in [Pierce 2002] (in Bib.v), if
    you are interested.)  Instead, we'll study the core concepts
    behind the subclass / subinterface relation in the simplified
    setting of the STLC. *)

(* ================================================================= *)
(** ** The Subsumption Rule *)

(** Our goal for this chapter is to add subtyping to the simply typed
    lambda-calculus (with some of the basic extensions from [MoreStlc]).
    This involves two steps:

      - Defining a binary _subtype relation_ between types.

      - Enriching the typing relation to take subtyping into account.

    The second step is actually very simple.  We add just a single rule
    to the typing relation: the so-called _rule of subsumption_:

                         Gamma |-- t1 \in T1     T1 <: T2
                         --------------------------------           (T_Sub)
                               Gamma |-- t1 \in T2

    This rule says, intuitively, that it is OK to "forget" some of
    what we know about a term. *) (* [T1] is weakened to [T2] *)

(** For example, we may know that [t1] is a record with two
    fields (e.g., [T1 = {x:A->A, y:B->B}]), but choose to forget about
    one of the fields ([T2 = {y:B->B}]) so that we can pass [t1] to a
    function that requires just a single-field record. *)

(* ================================================================= *)
(** ** The Subtype Relation *)

(** The first step -- the definition of the relation [S <: T] -- is
    where all the action is.  Let's look at each of the clauses of its
    definition.  *)

(* ----------------------------------------------------------------- *)
(** *** Structural Rules *)

(** To start off, we impose two "structural rules" that are
    independent of any particular type constructor: a rule of
    _transitivity_, which says intuitively that, if [S] is
    better (richer, safer) than [U] and [U] is better than [T],
    then [S] is better than [T]...

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

    ... and a rule of _reflexivity_, since certainly any type [T] is
    as good as itself:

                                   ------                              (S_Refl)
                                   T <: T
*)

(* ----------------------------------------------------------------- *)
(** *** Products *)

(** Now we consider the individual type constructors, one by one,
    beginning with product types.  We consider one pair to be a subtype
    of another if each of its components is.

                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                             S1 * S2 <: T1 * T2
*)

(* ----------------------------------------------------------------- *)
(** *** Arrows *)

(** The subtyping rule for arrows is a little less intuitive.
    Suppose we have functions [f] and [g] with these types:

       f : C -> Student
       g : (C->Person) -> D

    That is, [f] is a function that yields a record of type [Student],
    and [g] is a (higher-order) function that expects its argument to be
    a function yielding a record of type [Person].  Also suppose that
    [Student] is a subtype of [Person].  Then the application [g f] is
    safe even though their types do not match up precisely, because
    the only thing [g] can do with [f] is to apply it to some
    argument (of type [C]); the result will actually be a [Student],
    while [g] will be expecting a [Person], but this is safe because
    the only thing [g] can then do is to project out the two fields
    that it knows about ([name] and [age]), and these will certainly
    be among the fields that are present.

    This example suggests that the subtyping rule for arrow types
    should say that two arrow types are in the subtype relation if
    their results are:

                                  S2 <: T2
                              ----------------                     (S_Arrow_Co)
                            S1 -> S2 <: S1 -> T2


    (*
       f : Student -> C
       g : (Person->C) -> D

       Is the application [g f] safe? NO!

       e.g. f := \s:Student, s.gpa : Student -> Nat
            g := \fp:Person->Nat, fp {name="Xavier",age=33} + 3

            g f --> (\s:Student, s.gpa) {name="Xavier",age=33} + 3
                --> {name="Xavier",age=33}.gpa + 3
                -/-> (* stuck *)

            The argument of [f] is too strong for what [g] offers.

       Instead:

       f : Person -> C
       g : (Student->C) -> D

       Is the application [g f] safe? Yes!
       Any [Student] [g] passes to [f] can be safely handled by [f], because
       any [Student] is as good as a [Person].
    *)

    We can generalize this to allow the arguments of the two arrow
    types to be in the subtype relation as well:

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

    (* paraphrase: the arrow type [S1 -> S2] is a subtype of [T1 -> T2] if
       the argument type of [T1 -> T2] is a subtype of the argument type of
       [S1 -> S2], and the return type of [S1 -> S2] is a subtype of the return
       type of [T1 -> T2].

       Notice the similarity with the [hoare_consequence] rule!
       The subtype of the [<:] relation "inserts" itself inbetwixt the
       arms of the supertype.
    *)

    But notice that the argument types are subtypes "the other way round":
    in order to conclude that [S1->S2] to be a subtype of [T1->T2], it
    must be the case that [T1] is a subtype of [S1].  The arrow
    constructor is said to be _contravariant_ in its first argument
    and _covariant_ in its second.

    Here is an example that illustrates this:

       f : Person -> C
       g : (Student -> C) -> D

    The application [g f] is safe, because the only thing the body of
    [g] can do with [f] is to apply it to some argument of type
    [Student].  Since [f] requires records having (at least) the
    fields of a [Person], this will always work. So [Person -> C] is a
    subtype of [Student -> C] since [Student] is a subtype of
    [Person].

    The intuition is that, if we have a function [f] of type [S1->S2],
    then we know that [f] accepts elements of type [S1]; clearly, [f]
    will also accept elements of any subtype [T1] of [S1]. The type of
    [f] also tells us that it returns elements of type [S2]; we can
    also view these results belonging to any supertype [T2] of
    [S2]. That is, any function [f] of type [S1->S2] can also be
    viewed as having type [T1->T2]. *)          (* under these conditions, the type [T1->T2] subsumes [S1->S2]. *)

(* ----------------------------------------------------------------- *)
(** *** Records *)

(** What about subtyping for record types? *)

(** The basic intuition is that it is always safe to use a "bigger"
    record in place of a "smaller" one.  That is, given a record type,
    adding extra fields will always result in a subtype.  If some code
    is expecting a record with fields [x] and [y], it is perfectly safe
    for it to receive a record with fields [x], [y], and [z]; the [z]
    field will simply be ignored.  For example,

    {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}
    {name:String, age:Nat} <: {name:String}
    {name:String} <: {}

    This is known as "width subtyping" for records. *)

(** We can also create a subtype of a record type by replacing the type
    of one of its fields with a subtype.  If some code is expecting a
    record with a field [x] of type [T], it will be happy with a record
    having a field [x] of type [S] as long as [S] is a subtype of
    [T]. For example,                                                           (* note: whatever it may do with [T], it can also do with [S] *)

    {x:Student} <: {x:Person}

    This is known as "depth subtyping". *)

(** Finally, although the fields of a record type are written in a
    particular order, the order does not really matter. For example,

    {name:String,age:Nat} <: {age:Nat,name:String}

    This is known as "permutation subtyping". *)

(** We _could_ formalize these requirements in a single subtyping rule
    for records as follows:

                        forall jk in j1..jn,
                    exists ip in i1..im, such that
                          jk=ip and Sp <: Tk
                  ----------------------------------                    (S_Rcd)
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn}

    That is, the record on the left should have all the field labels of
    the one on the right (and possibly more), while the types of the
    common fields should be in the subtype relation.

    However, this rule is rather heavy and hard to read, so it is often
    decomposed into three simpler rules, which can be combined using
    [S_Trans] to achieve all the same effects. *)

(** First, adding fields to the end of a record type gives a subtype:

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}                             (* same order, same types, different lengths *)

    We can use [S_RcdWidth] to drop later fields of a multi-field
    record while keeping earlier fields, showing for example that
    [{age:Nat,name:String} <: {age:Nat}]. *)

(** Second, subtyping can be applied inside the components of a compound
    record type:

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}                            (* same length, same order, different types. Each type of the left record type must be subsumed by the respective type in the right record type. *)

    For example, we can use [S_RcdDepth] and [S_RcdWidth] together to
    show that [{y:Student, x:Nat} <: {y:Person}]. *)

(** Third, subtyping can reorder fields.  For example, we
    want [{name:String, gpa:Nat, age:Nat} <: Person], but we
    haven't quite achieved this yet: using just [S_RcdDepth] and
    [S_RcdWidth] we can only drop fields from the _end_ of a record
    type.  So we add:

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}                            (* same length, same types, different order. The permutation relation ensures that there are no unmatched types. *)
*)

(** It is worth noting that full-blown language designs may choose not
    to adopt all of these subtyping rules. For example, in Java:

    - Each class member (field or method) can be assigned a single
      index, adding new indices "on the right" as more members are
      added in subclasses (i.e., no permutation for classes).

    - A class may implement multiple interfaces -- so-called "multiple
      inheritance" of interfaces (i.e., permutation is allowed for
      interfaces).

    - In early versions of Java, a subclass could not change the
      argument or result types of a method of its superclass (i.e., no
      depth subtyping or no arrow subtyping, depending how you look at
      it). *)

(** **** Exercise: 2 stars, standard, especially useful (arrow_sub_wrong)

    Suppose we had incorrectly defined subtyping as covariant on both
    the right and the left of arrow types:

                            S1 <: T1    S2 <: T2
                            --------------------                (S_Arrow_wrong)
                            S1 -> S2 <: T1 -> T2

    Give a concrete example of functions [f] and [g] with the following
    types...

       f : Student -> Nat
       g : (Person -> Nat) -> Nat

    ... such that the application [g f] will get stuck during
    execution.  (Use informal syntax.  No need to prove formally that
    the application gets stuck.)

    (3:24 min - I anticipated the exercise for while reading)

    Here it is:
       e.g. f := \s:Student, s.gpa : Student -> Nat
            g := \fp:Person->Nat, fp {name="Xavier",age=33} + 3

            g f --> (\fp:Person->Nat, fp {name="Xavier",age=33} + 3)
                      (\s:Student, s.gpa : Student -> Nat)
                --> (\s:Student, s.gpa) {name="Xavier",age=33} + 3
                --> {name="Xavier",age=33}.gpa + 3
                -/-> (* stuck *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_arrow_sub_wrong : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Top *)

(** Finally, it is convenient to give the subtype relation a maximum
    element -- a type that lies above every other type and is
    inhabited by all (well-typed) values.  We do this by adding to the
    language one new type constant, called [Top], together with a
    subtyping rule that places it above every other type in the
    subtype relation:

                                   --------                             (S_Top)
                                   S <: Top                                     (* much like [True] for propositions and the implication relation *)

    The [Top] type is an analog of the [Object] type in Java and C#. *)

(* Is there a minimum element? The strongest type of them all? *)

(* ----------------------------------------------------------------- *)
(** *** Summary *)

(** In summary, we form the STLC with subtyping by starting with the
    pure STLC (over some set of base types) and then...

    - adding a base type [Top],

    - adding the rule of subsumption

                         Gamma |-- t1 \in T1     T1 <: T2
                         --------------------------------            (T_Sub)
                               Gamma |-- t1 \in T2                              (* wherever a term of type [T2] is expected, a term of type [T1], where [T1] is a subtype of [T2], will do just fine. *)

      to the typing relation, and

    - defining a subtype relation as follows:

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

                                   ------                              (S_Refl)
                                   T <: T

                                   --------                             (S_Top)
                                   S <: Top

                            S1 <: T1    S2 <: T2
                            --------------------                       (S_Prod)
                             S1 * S2 <: T1 * T2

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
*)

(* ================================================================= *)
(** ** Exercises *)

(** The following "thought exercises" are repeated later as formal
    exercises. *)

(** **** Exercise: 1 star, standard, optional (subtype_instances_tf_1)

    Suppose we have types [S], [T], [U], and [V] with [S <: T]
    and [U <: V].  Which of the following subtyping assertions
    are then true?  Write _true_ or _false_ after each one.
    ([A], [B], and [C] here are base types like [Bool], [Nat], etc.)

    (* 14:42 min + 13:47 min to do pretty trees *)
    note: apply the rules and check if premises are satisfiable

    - [T->S <: T->S]
      true by [S_Refl]

    - [Top->U <: S->Top]
      true by [S_Arrow]

        -------- [S_Top]    -------- [S_Top]
        S <: Top            U <: Top
        ---------------------------- [S_Arrow]
              Top->U <: S->Top

    - [(C->C) -> (A*B)  <:  (C->C) -> (Top*B)]
      true

                                    --------    ------ [S_Top] [S_Refl]
                                    A <: Top    B <: B
      ---------------- [S_Refl]     ------------------ [S_Pair]
      (C->C) <: (C->C)               (A*B) <: (Top*B)
      ------------------------------------------------ [S_Arrow]
          (C->C) -> (A*B)  <:  (C->C) -> (Top*B)

    - [T->T->U <: S->S->V]
      true ([->] is right associative)

    - [(T->T)->U <: (S->S)->V]
      false ([T <: S] is false)

      ==//==
      T <: S    S <: T (assumption)
      ---------------- [S_Arrow]
        S->S <: T->T             U <: V (assumption)
      --------------------------------- [S_Arrow]
            (T->T)->U <: (S->S)->V

    - [((T->S)->T)->U <: ((S->T)->S)->V]
      false ([T <: S] is false)
      ^^^ WRONG - did not keep track of shuffling ^^^

      true

      S <: T    S <: T (x2 assumption)
      ---------------- [S_Arrow]
        T->S <: S->T             S <: T (assumption)
      --------------------------------- [S_Arrow]
           (S->T)->S <: (T->S)->T                 U <: V (assumption)
      -------------------------------------------------- [S_Arrow]
                ((T->S)->T)->U <: ((S->T)->S)->V

      Student (S) <: Person (T)
      Person->Student <: Student->Person

    - [S*V <: T*U]
      false ([V <: U] is false)

                              ==//==
      S <: T (assumption)     V <: U
      ------------------------------ [S_Pair]
                S*V <: T*U

    [] *)

(** **** Exercise: 2 stars, standard (subtype_order)

    The following types happen to form a linear order with respect to subtyping:
    - [Top]
    - [Top -> Student]
    - [Student -> Person]
    - [Student -> Top]
    - [Person -> Student]

(* 5:36 min *)
Write these types in order from the most specific to the most general.

    1. [Top]
    2. [Student -> Top]
    3. [Student -> Person]
    4. [Person -> Student]
    5. [Top -> Student]

(* 21:50 min *)
Where does the type [Top->Top->Student] fit into this order?
That is, state how [Top -> (Top -> Student)] compares with each
of the five types above. It may be unrelated to some of them.                   (* [<:] is not a total relation! *)

    1. [Top]
    2. [Student->Top]
    3. [Top->Top->Student]

    [Top -> (Top -> Student)] is only comparable with [Top] and [Student->Top],
    being stronger that both.
    Since [Student->Top] ranks higher than the other three types, we can't
    even use transitivity to compare [Top -> (Top -> Student)] to any of
    the three other types .

    --------------    -------------------
    Student <: Top    Top->Student <: Top
    -------------------------------------
     Top->(Top->Student) <: Student->Top

                      ==========//==========
    Student <: Top    Person <: Top->Student
    ----------------------------------------
    Top->(Top->Student) <: Student -> Person (viceversa implies [Top <: Student])

    ==============//========//==============
    Top->(Top->Student) <: Person -> Student (neither viceversa)

                     ===========//==========
    Top <: Top       Top->Student <: Student (neither viceversa)
    ----------------------------------------
    Top->(Top->Student) <: Top->Student
*)

(* Do not modify the following line: *)
Definition manual_grade_for_subtype_order : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard (subtype_instances_tf_2)

(* 22:41 min *)

    Which of the following statements are true?  Write _true_ or
    _false_ after each one.

      forall S T,
          S <: T  ->
          S->S   <:  T->T
      >> Absolutely false

      forall S,
           S <: A->A ->
           exists T,
              S = T->T  /\  T <: A
      >> false: [S] need not necessarily be of the form [T->T]
         
         X := {age:Nat}
         A := Person
         Y := Student
         S = X->Y

         A <: X    Y <: A
         ----------------
           X->Y <: A->A

      forall S T1 T2,
           (S <: T1 -> T2) ->
           exists S1 S2,
              S = S1 -> S2  /\  T1 <: S1  /\  S2 <: T2 
      >> true

      exists S,
           S <: S->S 
      >> false: [S->S] is necessarily stronger than [S]

      [Top <: Top->Top] nope
      [Top->Top <: (Top->Top)->(Top->Top)] nope
      ...

      exists S,
           S->S <: S  
      >> true (witness: [Top])

      --------------- [S_Top]
      Top->Top <: Top

      forall S T1 T2,
           S <: T1*T2 ->
           exists S1 S2,
              S = S1*S2  /\  S1 <: T1  /\  S2 <: T2  
      >> true
*)

(* Do not modify the following line: *)
Definition manual_grade_for_subtype_instances_tf_2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard (subtype_concepts_tf)

(* 23:28 min *)

    Which of the following statements are true, and which are false?
    - There exists a type that is a supertype of every other type.

      true: [Top]

    - There exists a type that is a subtype of every other type.

      false: unless defined, such type would be infinitely large,
        combining all type constructors to make it as strong as possible.

    - There exists a pair type that is a supertype of every other
      pair type.

      true: [Top*Top]

    - There exists a pair type that is a subtype of every other
      pair type.

      false: for the same reason there isn't a minimum type.

    - There exists an arrow type that is a supertype of every other
      arrow type.

      false: such arrow type would have [Top] as the result type and
        the minimum as the argument type, but the minimum doesn't exist.

    - There exists an arrow type that is a subtype of every other
      arrow type.

      false: flip the previous reason; [Top->Bot], but [Bot] doesn't exist.

    - There is an infinite descending chain of distinct types in the
      subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a subtype of [Si].

      true: consider this chain:

      Si = {a0:Nat,...,ai:Nat}
           ...
      S2 = {a0:Nat,a1:Nat,a2:Nat}
      S1 = {a0:Nat,a1:Nat}
      S0 = {a0:Nat}

    - There is an infinite _ascending_ chain of distinct types in
      the subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a supertype of [Si].

      false: starting off such a sequence would require the strongest
        type ever possible.

*)

(* Do not modify the following line: *)
Definition manual_grade_for_subtype_concepts_tf : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (proper_subtypes)

    Is the following statement true or false?  Briefly explain your
    answer.  (Here [Base n] stands for a base type, where [n] is
    a string standing for the name of the base type.  See the
    Syntax section below.)

(* 14:47 min *)

    forall T,
         ~(T = Bool \/ exists n, T = Base n) ->                                 (* [T] is neither a [Bool] nor a base type - could still be a [Unit]! *)
         exists S,
            S <: T  /\  S <> T

    false: consider [T = Unit]. According to the below syntax, [Unit]
      is a type, distinct from [Bool] and [Base n]. But [Unit] can't be
      a supertype of anything.

      [{}->{}] is not a compelling counterexample. There are many arrow types
      [R->T] that satisfy [{}<:R] and [Q<:{}]. For example, [R] could be
      [Top] and [Q] could be any record type.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_proper_subtypes : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (small_large_1)
   - What is the _smallest_ type [T] ("smallest" in the subtype
     relation) that makes the following assertion true?  (Assume we
     have [Unit] among the base types and [unit] as a constant of this
     type.)

(* 25:04 min + 30:41 min + 41:10 min + 28:43 min -
   as if I didn't understand crap. I'm stuck in a mental loop in this one,
   I can't convince myself that [A->A] is the only valid choice for both.
   Isn't it!? I'm going nuts. So much for a well spent morning *)

       empty |-- (\p:T*Top, p.fst) ((\z:A,z), unit) \in A->A

       A->A * Unit
          T * Top  -> T

       The smallest type [T] is [Top->A].

       This can be generalized after the application to [A->A]
       by the rule [T_Sub], giving us the assertion.
       ^^^ WRONG ^^^

       The smallest type is [A->A].
       
       The base for [T] is determined by the argument [((\z:A,z), unit)],
       which has type [(A->A)*Unit] and may be weakened to [(A->Top)*Top] (but that is irrelevant).

       It cannot be smaller than [A->A], such as [Top->A], otherwise it would
       return a function [Top->A].       

   - What is the _largest_ type [T] that makes the same assertion true?

       A <: Top    A <: A            A <: A    A <: Top
       ------------------            ------------------
         Top->A <: A->A                A->A <: A->Top
        
       The largest type [T] is yet [A->Top].

       (p |-> (Top->A)*Top) p
                                                                        (z |-> A) z = A 
       ---------------------------------- [T_Var]                 ---------------------------    ----------------------
       (p |-> (Top->A)*Top) |-- p \in (Top->A)*Top                         (z |-> A) |-- z \in A          empty |-- unit in Unit    Unit <: Top
       ---------------------------------- [T_Fst]                 ---------------------------    ------------------------------------- [T_Sub]
       (p |-> (Top->A)*Top) |-- p.fst \in Top->A                           empty |-- (\z:A,z) \in Top->A    empty |-- unit \in Top
       ----------------------------------------------- [T_Abs]    -------------------------------------------------- [T_Pair]
       empty |-- (\p:(Top->A)*Top, p.fst) \in (T*Top)->(Top->A)            empty |-- ((\z:A,z), unit) \in (Top->A)*Top
       ----------------------------------------------------------------------------------------------- [T_App]
              empty |-- (\p:(Top->A)*Top, p.fst) ((\z:A,z), unit) \in Top->A            Top->A <: A->A
       ----------------------------------------------------------------------------------------------- [T_Sub]
                            empty |-- (\p:(Top->A)*Top, p.fst) ((\z:A,z), unit) \in A->A
*)

(* Do not modify the following line: *)
Definition manual_grade_for_small_large_1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (small_large_2)
   - What is the _smallest_ type [T] that makes the following
     assertion true?

(* ~5 min *)

       empty |-- (\p:(A->A * B->B), p) ((\z:A,z), (\z:B,z)) \in T

     The smallest type is [A->A * B->B].

   - What is the _largest_ type [T] that makes the same assertion true?

     The largest type is [A->Top * B->Top]

*)

(* Do not modify the following line: *)
Definition manual_grade_for_small_large_2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (small_large_3)

(* 7:48 min *)

   - What is the _smallest_ type [T] that makes the following
     assertion true?

       a:A |-- (\p:(A*T), (p.snd) (p.fst)) (a, \z:A,z) \in A

     The smallest type is [Top->A].
     ^^^ WRONG ^^^ A function [Top->A] accepts a [B<>A] as argument, upon
     which [\z:A,z] would get stuck.

     So smallest type is yet [A->A].
     

   - What is the _largest_ type [T] that makes the same assertion true?

     The largest type is [A->A].

    [] *)



(** **** Exercise: 2 stars, standard (small_large_4)

(* 6:06 min *)

   - What is the _smallest_ type [T] (if one exists) that makes the
     following assertion true?

       exists S,
         empty |-- (\p:(A*T), (p.snd) (p.fst)) \in S

     The smallest type exist and it is [Top->S].

   - What is the _largest_ type [T] that makes the same
     assertion true?

     The largest type is [A->S].
*)

(* Do not modify the following line: *)
Definition manual_grade_for_small_large_4 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (smallest_1)

(* 4:58 min *)

    What is the _smallest_ type [T] (if one exists) that makes
    the following assertion true?

      exists S t,
        empty |-- (\x:T, x x) t \in S

    There's no such [T], as the term (\x:T, x x) notoriously gets stuck.
    For [x x] to be typeable, [x] must have types [X -> Y] and [X] at the
    same time (by the rule [T_App]). These types are inconcilable, and
    since the typing relation is deterministic, this is impossible.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_smallest_1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (smallest_2)

(* ~5 min *)

    What is the _smallest_ type [T] that makes the following
    assertion true?

      empty |-- (\x:Top, x) ((\z:A,z) , (\z:B,z)) \in T

    The smallest type possible is [Top]. There's no way to recover the
    type of the argument after it has been fed to the left term.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_smallest_2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (count_supertypes)

(* 16:30 min *)

    How many supertypes does the record type [{x:A, y:C->C}] have?  That is,
    how many different types [T] are there such that [{x:A, y:C->C} <:
    T]?  (We consider two types to be different if they are written
    differently, even if each is a subtype of the other.  For example,
    [{x:A,y:B}] and [{y:B,x:A}] are different.)

    Trivial (1):
      Top

    By permutation (1):
      {y:C->C, x:A}

    By width (3):
      {x:A}
      {y:C->C}
      {}

    By depth (infinitely many?):
      {x:A', y:C->C} forall A' such that A <: A'
      {x:A, y:C->C'} forall C' such that C <: C'
      {x:A', y:C->C'} forall A' C' such that A <: A' and C <: C'

    By depth + permutation (infinitely many):
      {y:C->C, x:A'} forall A' such that A <: A'
      {y:C->C', x:A} forall C' such that C <: C'
      {y:C->C', x:A'} forall A' C' such that A <: A' and C <: C'

    By width + depth (infinitely many):
      {x:A'} forall A' such that A <: A'
      {y:C->C'} forall C' such that C <: C'

    I think that's about it.
    [] *)

(** **** Exercise: 2 stars, standard (pair_permutation)

(* 16:12 min *)

    The subtyping rule for product types

                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                               S1*S2 <: T1*T2

    intuitively corresponds to the "depth" subtyping rule for records.
    Extending the analogy, we might consider adding a "permutation" rule

                                   --------------
                                   T1*T2 <: T2*T1

    for products.  Is this a good idea? Briefly explain why or why not.

    No, it's not. Record access is invariant of field order, that's why a
    permutation rule makes sense for record types. Access to values of 
    product types, on the other hand, is sensible to component order.
    
    For example, the value [(a, \z:A,z)] would not be typaple.

      (a:A) a = A->A ==> A = A->A (impossible!)
    ------------------
    a:A |-- a \in A->A      ...
    --------------------------------    --------------------
    a:A |-- (a, \z:A,z) \in (A->A)*A    (A->A)*A <: A*(A->A)
    --------------------------------------------------------
              a:A |-- (a, \z:A,z) \in A*(A->A)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_pair_permutation : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Formal Definitions *)

Module STLCSub.

(** Most of the definitions needed to formalize what we've discussed
    above -- in particular, the syntax and operational semantics of
    the language -- are identical to what we saw in the last chapter.
    We just need to extend the typing relation with the subsumption
    rule and add a new [Inductive] definition for the subtyping
    relation.  Let's first do the identical bits. *)

(** We include products in the syntax of types and terms, but not,
    for the moment, anywhere else; the [products] exercise below will
    ask you to extend the definitions of the value relation, operational
    semantics, subtyping relation, and typing relation and to extend
    the proofs of progress and preservation to fully support products. *)

(* ================================================================= *)
(** ** Core Definitions *)

(* ----------------------------------------------------------------- *)
(** *** Syntax *)

(** In the rest of the chapter, we formalize just base types,
    booleans, arrow types, [Unit], and [Top], omitting record types
    and leaving product types as an exercise.  For the sake of more
    interesting examples, we'll add an arbitrary set of base types
    like [String], [Float], etc.  (Since they are just for examples,
    we won't bother adding any operations over these base types, but
    we could easily do so.) *)

Inductive ty : Type :=
  | Ty_Top   : ty
  | Ty_Bool  : ty
  | Ty_Base  : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Unit  : ty
  | Ty_Prod : ty -> ty -> ty
.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_unit : tm
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'Base' x" := (Ty_Base x) (in custom stlc at level 0).

Notation "'Top'" := (Ty_Top) (in custom stlc at level 0).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 1).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 1).

Notation "{ x }" := x (in custom stlc at level 1, x constr).

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

(** The definition of substitution remains exactly the same as for the
    pure STLC. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{unit}> =>
      <{unit}>
  | <{ (t1, t2) }> =>
      <{( [x:=s] t1, [x:=s] t2 )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

(** Likewise the definitions of [value] and [step]. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_unit :
      value <{unit}>
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1,v2)}>
.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Pair1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{(t1,t2)}> --> <{(t1',t2)}>
  | ST_Pair2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{(v1,t2)}> --> <{(v1,t2')}>
  | ST_Fst1 : forall t1 t1',
      t1 --> t1' ->
      <{t1.fst}> --> <{t1'.fst}>
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{(v1,v2).fst}> --> <{v1}>
  | ST_Snd1 : forall t1 t1',
      t1 --> t1' ->
      <{t1.snd}> --> <{t1'.snd}>
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{(v1,v2).snd}> --> <{v2}>
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(* ================================================================= *)
(** ** Subtyping *)

(** Now we come to the interesting part.  We begin by defining
    the subtyping relation and developing some of its important
    technical properties. *)

(** The definition of subtyping is just what we sketched in the
    motivating discussion. *)

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{Top}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{S1->S2}> <: <{T1->T2}>
  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{S1*S2}> <: <{T1*T2}>
where "T '<:' U" := (subtype T U).

(** Note that we don't need any special rules for base types ([Bool]
    and [Base]): they are automatically subtypes of themselves (by
    [S_Refl]) and [Top] (by [S_Top]), and that's all we want. *)                (* NB: [subtype] is not total: neither [Bool <: Unit] or [Unit <: Bool] hold *)

Hint Constructors subtype : core.

Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".

Notation A := <{Base "A"}>.
Notation B := <{Base "B"}>.
Notation C := <{Base "C"}>.

Notation String := <{Base "String"}>.
Notation Float := <{Base "Float"}>.
Notation Integer := <{Base "Integer"}>.

Example subtyping_example_0 :
  <{C->Bool}> <: <{C->Top}>.
Proof. auto. Qed.

(** **** Exercise: 2 stars, standard, optional (subtyping_judgements)

(* 6:37 min *)

    (Leave this exercise [Admitted] until after you have finished adding product
    types to the language -- see exercise [products] -- at least up to
    this point in the file).

    Recall that, in chapter [MoreStlc], the optional section
    "Encoding Records" describes how records can be encoded as pairs.
    Using this encoding, define pair types representing the following
    record types:

    Person := { name : String }
    Student := { name : String ; gpa : Float }
    Employee := { name : String ; ssn : Integer }
*)

(* I'm going to adopt this naming convention: name := "a", gpa, ssn := "b" *)

Definition Person : ty := <{String * Top}>. (* trailing [Top] for proper subtyping *)
Definition Student : ty := <{String * (Float * Top)}>.
Definition Employee : ty := <{String * (Integer * Top)}>.

(** Now use the definition of the subtype relation to prove the following: *)

Hint Unfold Person Student Employee : core.

Example sub_student_person :
  Student <: Person.
Proof with auto. apply S_Prod...  Qed.

Example sub_employee_person :
  Employee <: Person.
Proof with auto. apply S_Prod...  Qed.
(** [] *)

(** The following facts are mostly easy to prove in Coq.  To get
    full benefit from the exercises, make sure you also
    understand how to prove them on paper! *)

(** **** Exercise: 1 star, standard, optional (subtyping_example_1) *)

(* ~1 min *)
Example subtyping_example_1 :
  <{Top->Student}> <:  <{(C->C)->Person}>.
Proof with eauto.
  apply S_Arrow...
  apply sub_student_person.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (subtyping_example_2) *)

(* 1:28 min *)
Example subtyping_example_2 :
  <{Top->Person}> <: <{Person->Top}>.
Proof with eauto.
  apply S_Arrow...
Qed.
(** [] *)

End Examples.

(* ================================================================= *)
(** ** Typing *)

(** The only change to the typing relation is the addition of the rule
    of subsumption, [T_Sub]. *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->    (* If we know [t1:T1]... *)
      T1 <: T2 ->               (* and we have a type [T2] weaker than [T1]... *)
      Gamma |-- t1 \in T2       (* then we can weaken the type of [t1] to [T2]. *)

  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1,t2) \in (T1 * T2)
  | T_Fst : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in (T1 * T2) ->
      Gamma |-- t1.fst \in T1
  | T_Snd : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in (T1 * T2) ->
      Gamma |-- t1.snd \in T2

(* NB: [T_Sub] makes [has_type] nondeterministic!!!
   Inverting a typing statement to its causes is trickier now. *)

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Module Examples2.
Import Examples.

(** Do the following exercises after you have added product types to
    the language.  For each informal typing judgement, write it as a
    formal statement in Coq and prove it. *)

(* 13:37 min all three *)

(** **** Exercise: 1 star, standard, optional (typing_example_0) *)
(* empty |-- ((\z:A,z), (\z:B,z)) \in (A->A * B->B) *)

Example typing_example_0 : forall z A B,
  empty |-- ((\z:A,z), (\z:B,z)) \in ((A->A) * (B->B)).
Proof. auto. Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (typing_example_1) *)
(* empty |-- (\x:(Top * B->B), x.snd) ((\z:A,z), (\z:B,z))
         \in B->B *)

Example typing_example_1 : forall x z A B,
  empty |-- (\x:(Top * (B->B)), x.snd) ((\z:A,z), (\z:B,z))
         \in (B->B).
Proof with eauto.
  intros.
  apply T_App with <{Top * (B->B)}>...
  apply T_Pair...
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (typing_example_2) *)
(* empty |-- (\z:(C->C)->(Top * B->B), (z (\x:C,x)).snd)
              (\z:C->C, ((\z:A,z), (\z:B,z)))
         \in B->B *)

Example typing_example_2 : forall x z A B C,
  empty |-- (\z:(C->C)->(Top * (B->B)), (z (\x:C,x)).snd)
              (\z:C->C, ((\z:A,z), (\z:B,z)))
         \in (B->B).
Proof with eauto.
  intros.
  eapply T_App...
  - apply T_Abs...
    eapply T_Snd...
  - apply T_Abs...
    apply T_Pair...
Qed.

(** [] *)

End Examples2.

(* ################################################################# *)
(** * Properties *)

(** The fundamental properties of the system that we want to
    check are the same as always: progress and preservation.  Unlike
    the extension of the STLC with references (chapter [References]),
    we don't need to change the _statements_ of these properties to
    take subtyping into account.  However, their proofs do become a
    little bit more involved. *)      (* note: subtyping is integrated seamlessly into these properties, but not their proofs. *)

(* ================================================================= *)
(** ** Inversion Lemmas for Subtyping *)

(** Before we look at the properties of the typing relation, we need
    to establish a couple of critical structural properties of the
    subtype relation:
       - [Bool] is the only subtype of [Bool], and
       - every subtype of an arrow type is itself an arrow type. *)

(** These are called _inversion lemmas_ because they play a
    similar role in proofs as the built-in [inversion] tactic: given a
    hypothesis that there exists a derivation of some subtyping
    statement [S <: T] and some constraints on the shape of [S] and/or          (* note: shape helps narrow down the set of rules that could have been used to derive the hypothesis *)
    [T], each inversion lemma reasons about what this derivation must
    look like to tell us something further about the shapes of [S] and
    [T] and the existence of subtype relations between their parts. *)

(** **** Exercise: 2 stars, standard, optional (sub_inversion_Bool) *)

(* 5:23 min *)
Lemma sub_inversion_Bool : forall U,
     U <: <{Bool}> ->
     U = <{Bool}>.
Proof with auto.
  intros U Hs.
  remember <{Bool}> as V.
  induction Hs; subst;
  try solve_by_invert...

    (* S_Trans *)
    rewrite IHHs2 in IHHs1...
Qed.
(** [] *)

Print subtype.

(** **** Exercise: 3 stars, standard (sub_inversion_arrow) *)

(* 15:46 min *)
Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{V1->V2}> ->
     exists U1 U2,
     U = <{U1->U2}> /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{V1->V2}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs as [| U S V HUS IHUS HSV IHSV | | | ]; intros V1 V2 HeqV; subst...

  - (* S_Trans *)
    destruct (IHSV V1 V2) as [S1 [S2 [HeqS [HV1S1 HS2V2]]]];
    subst; clear IHSV...
    destruct (IHUS S1 S2) as [U1 [U2 [HeqU [HS1U1 HU2S2]]]];
    subst; clear IHUS...
    exists U1, U2...

  - (* S_Top *)
    solve_by_invert.

  - (* S_Arrow *)
    inversion HeqV; subst... (* [U] is already an arrow type, duh *)

  - (* S_Prod *)
    solve_by_invert.
Qed.

(** [] *)

(** There are additional _inversion lemmas_ for the other types:
       - [Unit] is the only subtype of [Unit], and
       - [Base n] is the only subtype of [Base n], and
       - [Top] is the only supertype of [Top]. *)

Print subtype.
(* (Exercise: products)
       - every subtype of a pair type is itself a pair type *)

(* 11:54 min *)
Lemma sub_inversion_product : forall U V1 V2,
    U <: <{V1 * V2}> ->
    exists U1 U2,
    U = <{U1 * U2}> /\ U1 <: V1 /\ U2 <: V2.
Proof with eauto.
  intros ? ? ? Hs.
  remember <{V1 * V2}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs as [ | U S V | | | ]; intros ? ? Heq;
    try solve_by_invert; subst...

  - (* S_Trans *)
    destruct (IHHs2 V1 V2) as [S1 [S2 [EqU [HS1V1 HS2V2]]]]; subst...
    destruct (IHHs1 S1 S2) as [U1 [U2 [EqU [HU1S1 HU2S2]]]]; subst...
    exists U1, U2...

  - (* S_Pair *)
    inversion Heq; subst...
Qed.

(** **** Exercise: 2 stars, standard, optional (sub_inversion_Unit) *)

(* 2:38 min *)
Lemma sub_inversion_Unit : forall U,
     U <: <{Unit}> ->
     U = <{Unit}>.
Proof with auto.
  intros U Hs.
  remember <{Unit}> as V.
  induction Hs; subst;
  try solve_by_invert...
  rewrite IHHs2 in IHHs1...
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (sub_inversion_Base) *)

(* ~1 min *)
Lemma sub_inversion_Base : forall U s,
     U <: <{Base s}> ->
     U = <{Base s}>.
Proof with auto.
  intros U s Hs.
  remember <{Base s}> as V.
  induction Hs; subst;
  try solve_by_invert...
  rewrite IHHs2 in IHHs1...
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (sub_inversion_Top) *)

(* ~1 min *)
Lemma sub_inversion_Top : forall U,
     <{ Top }> <: U ->
     U = <{ Top }>.
Proof with auto.
  intros U Hs.
  remember <{Top}> as V.
  induction Hs; subst; try solve_by_invert...

    (* S_Trans *)
    rewrite IHHs1 in IHHs2...
Qed.
(** [] *)

(* ================================================================= *)
(** ** Canonical Forms *)

(** The proof of the progress theorem -- that a well-typed
    non-value can always take a step -- doesn't need to change too
    much: we just need one small refinement.  When we're considering
    the case where the term in question is an application [t1 t2]
    where both [t1] and [t2] are values, we need to know that [t1] has
    the _form_ of a lambda-abstraction, so that we can apply the
    [ST_AppAbs] reduction rule.  In the ordinary STLC, this is
    obvious: we know that [t1] has a function type [T11->T12], and
    there is only one rule that can be used to give a function type to
    a value -- rule [T_Abs] -- and the form of the conclusion of this
    rule forces [t1] to be an abstraction.                                      (* however we change the type of the abstraction, it must still be an arrow type in order to have a valid derivation for the overall application. *)

    In the STLC with subtyping, this reasoning doesn't quite work
    because there's another rule that can be used to show that a value
    has a function type: subsumption.  Fortunately, this possibility
    doesn't change things much: if the last rule used to show [Gamma
    |-- t1 \in T11->T12] is subsumption, then there is some
    _sub_-derivation whose subject is also [t1], and we can reason by
    induction until we finally bottom out at a use of [T_Abs].

    This bit of reasoning is packaged up in the following lemma, which
    tells us the possible "canonical forms" (i.e., values) of function
    type. *)

(** **** Exercise: 3 stars, standard, optional (canonical_forms_of_arrow_types) *)

(* ~30 min *)

Print has_type.
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |-- s \in (T1->T2) ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
Proof with eauto.
  intros ? ? ? ? has_type.
  remember <{T1->T2}> as A.
  generalize dependent T2.
  generalize dependent T1.

  induction has_type;
  intros A1 A2 HeqA Hvalue; subst;

  (* Other base types *)
  try (inversion HeqA; subst; clear HeqA);

  (* T_Var, T_App, T_If *)
  try (solve [inversion Hvalue])...

  (* T_Sub *)
  destruct (sub_inversion_arrow _ _ _ H) as [U1 [U2 [Heq _]]]...
Qed.

Print step.

(** [] *)

(** Similarly, the canonical forms of type [Bool] are the constants
    [tm_true] and [tm_false]. *)

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |-- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{Bool}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

(* note: these two canonical lemmas suffice for proving [progress]
  (products exercise) Not anymore after adding pair values, operational semantics and typing rules for products.
*)

(* 21:23 min *)
Lemma canonical_forms_of_product_types : forall Gamma s V1 V2,
  Gamma |-- s \in (V1 * V2) ->
  value s ->
  exists v1 v2,
    s = <{(v1,v2)}>
    /\ value v1 /\ Gamma |-- v1 \in V1
    /\ value v2 /\ Gamma |-- v2 \in V2.
Proof with eauto.
  intros ? ? ? ? Hty.
  remember <{V1 * V2}> as T.
  generalize dependent V2.
  generalize dependent V1.
  induction Hty;
    intros ? ? Heq Hvalue;
    try solve_by_invert; subst...

  - (* T_Sub *)
    destruct (sub_inversion_product _ _ _ H)
      as [U1 [U2 [Heq [HU1V1 HU2V2]]]].
    destruct (IHHty U1 U2 Heq Hvalue)
      as [v1 [v2 [Heqv [Hvalue1 [Htv1 [Hvalue2 Htv2]]]]]]; subst...
    exists v1, v2; intuition; eapply T_Sub...

  - (* T_Pair *)
    inversion Heq; subst; clear Heq;
    inversion Hvalue; subst; clear Hvalue.
    exists t1, t2...
Qed.

(* ================================================================= *)
(** ** Progress *)

(** The proof of progress now proceeds just like the one for the
    pure STLC, except that in several places we invoke canonical forms
    lemmas...

    _Theorem_ (Progress): For any term [t] and type [T], if [empty |--
    t \in T] then [t] is a value or [t --> t'] for some term [t'].

    _Proof_: Let [t] and [T] be given, with [empty |-- t \in T].
    Proceed by induction on the typing derivation.

    The cases for [T_Abs], [T_Unit], [T_True] and [T_False] are
    immediate because abstractions, [unit], [true], and
    [false] are already values.  The [T_Var] case is vacuous
    because variables cannot be typed in the empty context.  The
    remaining cases are more interesting:

    - If the last step in the typing derivation uses rule [T_App],
      then there are terms [t1] [t2] and types [T1] and [T2] such that
      [t = t1 t2], [T = T2], [empty |-- t1 \in T1 -> T2], and [empty
      |-- t2 \in T1].  Moreover, by the induction hypothesis, either
      [t1] is a value or it steps, and either [t2] is a value or it
      steps.  There are three possibilities to consider:

      - First, suppose [t1 --> t1'] for some term [t1'].  Then [t1
        t2 --> t1' t2] by [ST_App1].

      - Second, suppose [t1] is a value and [t2 --> t2'] for some term
        [t2'].  Then [t1 t2 --> t1 t2'] by rule [ST_App2] because [t1]
        is a value.

      - Third, suppose [t1] and [t2] are both values.  By the
        canonical forms lemma for arrow types, we know that [t1] has
        the form [\x:S1,s2] for some [x], [S1], and [s2].  But then
        [(\x:S1,s2) t2 --> [x:=t2]s2] by [ST_AppAbs], since [t2] is a
        value.

    - If the final step of the derivation uses rule [T_If], then
      there are terms [t1], [t2], and [t3] such that [t = if t1
      then t2 else t3], with [empty |-- t1 \in Bool] and with [empty
      |-- t2 \in T] and [empty |-- t3 \in T].  Moreover, by the
      induction hypothesis, either [t1] is a value or it steps.

       - If [t1] is a value, then by the canonical forms lemma for
         booleans, either [t1 = true] or [t1 = false].  In
         either case, [t] can step, using rule [ST_IfTrue] or
         [ST_IfFalse].

       - If [t1] can step, then so can [t], by rule [ST_If].

    - If the final step of the derivation is by [T_Sub], then there is
      a type [T2] such that [T1 <: T2] and [empty |-- t1 \in T1].  The
      desired result is exactly the induction hypothesis for the
      typing subderivation. *)

(** Formally: *)

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto. 

  (* pairs *)
  (* 14:05 min *)
  - (* T_Pair *)
    destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      destruct H0 as [t2' Hstp]...
    + (* t1 steps *)
      destruct H...
  - (* T_Fst *)
    destruct IHHt...
    + destruct (canonical_forms_of_product_types _ _ _ _ Ht H).
      destruct H0 as [? [? [? [_ [? _]]]]]; subst...
    + destruct H...
  - (* T_Snd *)
    destruct IHHt...
    + destruct (canonical_forms_of_product_types _ _ _ _ Ht H).
      destruct H0 as [? [? [? [_ [? _]]]]]; subst...
    + destruct H...
Qed.

(* ================================================================= *)
(** ** Inversion Lemmas for Typing *)

(** The proof of the preservation theorem also becomes a little more
    complex with the addition of subtyping.  The reason is that, as
    with the "inversion lemmas for subtyping" above, there are a
    number of facts about the typing relation that are immediate from
    the definition in the pure STLC (formally: that can be obtained
    directly from the [inversion] tactic) but that require real proofs
    in the presence of subtyping because there are multiple ways to
    derive the same [has_type] statement.

    The following inversion lemma tells us that, if we have a
    derivation of some typing statement [Gamma |-- \x:S1,t2 \in T] whose
    subject is an abstraction, then there must be some subderivation
    giving a type to the body [t2]. *)

(** _Lemma_: If [Gamma |-- \x:S1,t2 \in T], then there is a type [S2]
    such that [x|->S1; Gamma |-- t2 \in S2] and [S1 -> S2 <: T].

    Notice that the lemma does _not_ say, "then [T] itself is an arrow
    type" -- this is tempting, but false!  (Why?) *)      (* [T] can be [Top], which is not an arrow type. Otherwise, it is an arrow type. *)

(** _Proof_: Let [Gamma], [x], [S1], [t2] and [T] be given as
     described.  Proceed by induction on the derivation of [Gamma |--
     \x:S1,t2 \in T].  The cases for [T_Var] and [T_App] are vacuous
     as those rules cannot be used to give a type to a syntactic
     abstraction.

     - If the last step of the derivation is a use of [T_Abs] then
       there is a type [T12] such that [T = S1 -> T12] and [x:S1;
       Gamma |-- t2 \in T12].  Picking [T12] for [S2] gives us what we
       need, since [S1 -> T12 <: S1 -> T12] follows from [S_Refl].

     - If the last step of the derivation is a use of [T_Sub] then
       there is a type [S] such that [S <: T] and [Gamma |-- \x:S1,t2
       \in S].  The IH for the typing subderivation tells us that there
       is some type [S2] with [S1 -> S2 <: S] and [x:S1; Gamma |-- t2
       \in S2].  Picking type [S2] gives us what we need, since [S1 ->
       S2 <: T] then follows by [S_Trans]. *)

(** Formally: *)

(* note: as for the parameter type, we can't do better than [S1].
   We can only weaken the type of the whole abstraction by leveraging on
   covariance of the result type.
   
   Can you prove a similar theorem, that instead strengthens the argument type?
   
     Gamma |-- \x:T,t2 \in S2 ->
     exists S1,
       <{S1->S2}> <: T
       /\ (x |-> S1 ; Gamma) |-- t2 \in S2.
   *)

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |-- \x:S1,t2 \in T ->
     exists S2,
       <{S1->S2}> <: T
       /\ (x |-> S1 ; Gamma) |-- t2 \in S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{\x:S1,t2}> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T1...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
  Qed.


(* Person->A <: Student->A  *)

(** **** Exercise: 3 stars, standard, optional (typing_inversion_var) *)

(* ~15 min *)
Lemma typing_inversion_var : forall Gamma (x:string) T,
  Gamma |-- x \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros Gamma x T H.
  remember (x:tm) as t. (* Uncoerce!!! Took 10:17 mins to figure out the annotation. (Could have also achieved the correct equation using [tm_var x]) *)
  induction H;
    inversion Heqt; subst...

  - (* T_Sub *)
    clear H1.
    destruct IHhas_type as [S [HGamma Hsub]]...
    (* exists S... *)
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (typing_inversion_app) *)

(* 15:10 min *)
Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |-- t1 t2 \in T2 ->
  exists T1,
    Gamma |-- t1 \in (T1->T2) /\
    Gamma |-- t2 \in T1.      (* note: subtyping assertion missing *)
Proof with eauto.
  intros Gamma t1 t2 T2 H.
  remember <{t1 t2}> as t.
  induction H;
    inversion Heqt; subst...

  - (* T_Sub - return type has been weakened *)
    clear H1 H.
    destruct IHhas_type as [S1 [Hfun Harg]]...
    (* + auto.
    + exists S1. split; try assumption.
      eapply T_Sub.
      * apply Hfun.
      * apply S_Arrow... *)
Qed.

(** [] *)

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |-- unit \in T ->
    <{Unit}> <: T.
Proof with eauto.
  intros Gamma T Htyp. remember <{ unit }> as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

(** The inversion lemmas for typing and for subtyping between arrow
    types can be packaged up as a useful "combination lemma" telling
    us exactly what we'll actually require below. *)

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |-- \x:S1,s2 \in (T1->T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |-- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst...  Qed.

(** products exercise
    ~5 min *)

Lemma typing_inversion_product : forall Gamma t1 t2 T,
  Gamma |-- (t1, t2) \in T ->
  exists T1 T2,
    <{T1*T2}> <: T /\
    Gamma |-- t1 \in T1 /\ Gamma |-- t2 \in T2.
Proof with eauto.
  intros ? ? ? ? Ht.
  remember <{(t1,t2)}> as t.
  induction Ht;
    inversion Heqt; subst...

  - (* T_Sub *)
    destruct IHHt as [S1 [S2 [Hsub [Ht1 Ht2]]]]...
    eapply S_Trans with (T:=T2) in Hsub...
Qed.

(* ================================================================= *)
(** ** Weakening *)

(** The weakening lemma is proved as in pure STLC. *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.

  (* 8: (* T_Sub*)
        intros; apply IHHt in H0; eapply T_Sub; eassumption. *)
Qed.

Corollary weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ================================================================= *)
(** ** Substitution *)

(** When subtyping is involved proofs are generally easier
    when done by induction on typing derivations, rather than on terms.
    The _substitution lemma_ is proved as for pure STLC, but using
    induction on the typing derivation this time (see Exercise
    substitution_preserves_typing_from_typing_ind in StlcProp.v). *)

Print has_type.

(* 2:15 min - copy-pasted my solution *)
Lemma substitution_preserves_typing : forall Gamma x U t v T,
   (x |-> U ; Gamma) |-- t \in T ->
   empty |-- v \in U   ->
   Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
 
  - (* T_Var *)
    destruct (eqb_spec x x0); subst.
    + rewrite update_eq in H.
      injection H as H; subst.
      apply weakening_empty; auto.

    + rewrite update_neq in H; auto.

  - (* T_Abs *)
    destruct (eqb_spec x x0); subst.

    + rewrite update_shadow in Ht; auto.

    + constructor.
      apply IHHt with (Gamma := x0 |-> T2; Gamma').
      rewrite update_permute; auto.
Qed.

(* ================================================================= *)
(** ** Preservation *)

(** The proof of preservation now proceeds pretty much as in earlier
    chapters, using the substitution lemma at the appropriate point
    and the inversion lemma from above to extract structural
    information from typing assumptions. *)

(** _Theorem_ (Preservation): If [t], [t'] are terms and [T] is a type
    such that [empty |-- t \in T] and [t --> t'], then [empty |-- t'
    \in T].

    _Proof_: Let [t] and [T] be given such that [empty |-- t \in T].
    We proceed by induction on the structure of this typing
    derivation. The [T_Abs], [T_Unit], [T_True], and [T_False] cases
    are vacuous because abstractions and constants don't step.  Case
    [T_Var] is vacuous as well, since the context is empty.

     - If the final step of the derivation is by [T_App], then there
       are terms [t1] and [t2] and types [T1] and [T2] such that [t =
       t1 t2], [T = T2], [empty |-- t1 \in T1 -> T2], and [empty |--
       t2 \in T1].

       By the definition of the step relation, there are three ways
       [t1 t2] can step.  Cases [ST_App1] and [ST_App2] follow
       immediately by the induction hypotheses for the typing
       subderivations and a use of [T_App].

       Suppose instead [t1 t2] steps by [ST_AppAbs].  Then [t1 =
       \x:S,t12] for some type [S] and term [t12], and [t' =
       [x:=t2]t12].

       By lemma [abs_arrow], we have [T1 <: S] and [x:S1 |-- s2 \in
       T2].  It then follows by the substitution
       lemma ([substitution_preserves_typing]) that [empty |-- [x:=t2]
       t12 \in T2] as desired.

     - If the final step of the derivation uses rule [T_If], then
       there are terms [t1], [t2], and [t3] such that [t = if t1 then
       t2 else t3], with [empty |-- t1 \in Bool] and with [empty |--
       t2 \in T] and [empty |-- t3 \in T].  Moreover, by the induction
       hypothesis, if [t1] steps to [t1'] then [empty |-- t1' : Bool].
       There are three cases to consider, depending on which rule was
       used to show [t --> t'].

          - If [t --> t'] by rule [ST_If], then [t' = if t1' then t2
            else t3] with [t1 --> t1'].  By the induction hypothesis,
            [empty |-- t1' \in Bool], and so [empty |-- t' \in T] by
            [T_If].

          - If [t --> t'] by rule [ST_IfTrue] or [ST_IfFalse], then
            either [t' = t2] or [t' = t3], and [empty |-- t' \in T]
            follows by assumption.

     - If the final step of the derivation is by [T_Sub], then there
       is a type [S] such that [S <: T] and [empty |-- t \in S].  The
       result is immediate by the induction hypothesis for the typing
       subderivation and an application of [T_Sub].  [] *)

Theorem preservation : forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; eauto];

       try (inversion HE; subst; eauto;
            apply typing_inversion_product in HT;
            destruct HT as [S1 [S2 [Hsub [? ?]]]];
            apply sub_inversion_product in Hsub;
            destruct Hsub as [U1 [U2 [Heq [? ?]]]];
            inversion Heq; subst; eauto).

  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0... 
Qed.

(* ~1:10 hours for preservation *)

(* ================================================================= *)
(** ** Records, via Products and Top *)

(** This formalization of the STLC with subtyping omits record
    types for brevity.  If we want to deal with them more seriously,
    we have two choices.

    First, we can treat them as part of the core language, writing
    down proper syntax, typing, and subtyping rules for them.  Chapter
    [RecordSub] shows how this extension works.

    On the other hand, if we are treating them as a derived form that
    is desugared in the parser, then we shouldn't need any new rules:
    we should just check that the existing rules for subtyping product
    and [Unit] types give rise to reasonable rules for record
    subtyping via this encoding. To do this, we just need to make one
    small change to the encoding described earlier: instead of using
    [Unit] as the base case in the encoding of tuples and the "don't
    care" placeholder in the encoding of records, we use [Top].  So:

    {a:Nat, b:Nat} ----> {Nat,Nat}       i.e., (Nat,(Nat,Top))
    {c:Nat, a:Nat} ----> {Nat,Top,Nat}   i.e., (Nat,(Top,(Nat,Top)))

    The encoding of record values doesn't change at all.  It is
    easy (and instructive) to check that the subtyping rules above are
    validated by the encoding. *)

(* ================================================================= *)
(** ** Exercises *)


(* Is subtype antisymmetric? *)

(* I tried... *)
Theorem subtype_antisym : forall S T, S <: T -> T <: S -> S = T.
Proof with eauto.
  induction S; intros T HST HTS.

  - apply sub_inversion_Top in HST; subst...
  - apply sub_inversion_Bool in HTS; subst...
  - admit.
  - apply sub_inversion_arrow in HTS.
    destruct HTS as [U1 [U2 [EqT [HS1U1 HU2S2]]]]; subst.
    assert (<{U1->U2}> <: <{S1->S2}>) by auto.
    inversion HST; subst; clear HST;
    inversion H; subst; clear H...

  (* intros S T H1.
  induction H1...

  - (* S_Trans *)
    intros H2.
    apply S_Trans with (T:=U) in H2... *)
Abort.

Example d1 : forall x, empty |-- (\x:(Bool->Top), x true) (\x:Top, x) \in Top.
Proof with auto.
  intros.
  eapply T_App.
  - apply T_Abs.
    eapply T_App.
    + apply T_Var.
      rewrite update_eq...
    + eapply T_Sub...
  - eapply T_Sub.
    + apply T_Abs...
    + apply S_Arrow... 

    (* or
    eapply T_Abs...
    eapply T_Sub with <{Bool}>... *)
Qed.

Example d2 : forall x, empty |-- (\x:(Bool->Top), x true) (\x:Bool, x) \in Top.
Proof with auto.
  intros.
  eapply T_App...
  eapply T_Sub with <{(Bool->Top)->Top}>...
  apply T_Abs...
  eapply T_App...
Qed.

(** **** Exercise: 2 stars, standard (variations)

(* 10:37 min  - stuck for a while trying to prove antisymmetricity
   + 1:05 hour + 2 hours (i'm slow. 2 stars uh :/) *)
    Each part of this problem suggests a different way of changing the
    definition of the STLC with Unit and subtyping.  (These changes
    are not cumulative: each part starts from the original language.)
    In each part, list which properties (Progress, Preservation, both,
    or neither) become false.  If a property becomes false, give a
    counterexample.

    - Suppose we add the following typing rule:

                           Gamma |-- t \in S1->S2
                    S1 <: T1     T1 <: S1      S2 <: T2
                    -----------------------------------    (T_Funny1)
                           Gamma |-- t \in T1->T2

       Neither become false: this rule is equivalent to [T_Sub] where [T]
       is the arrow type [T1->T2] was obtained by weakening the result type of
       [S1->S2]. The assumption that both [S1 <: T1] and [T1 <: S1] hold
       is difficult, if not impossible, to meet in our calculus if
       [S1] and [T1] aren't the same type, rendering the addition
       of this rule innocuous.

    - Suppose we add the following reduction rule:

                             --------------------         (ST_Funny21)
                             unit --> (\x:Top. x)

      Progress remains true, because a term where such step had already
      happened will (most likely) be ill-typed, otherwise the term can
      take a step by [ST_Funny21].

      Preservation becomes false:

        empty |-- unit \in Unit =>
        unit --> (\x:Top. x)    =>
        empty |-- (\x:Top. x) \in Unit (* impossible! [unit] is the only member of [Unit] *)

    - Suppose we add the following subtyping rule:

                               ----------------          (S_Funny3)
                               Unit <: Top->Top

      This rule says: a value of type [Unit] can safely be used in any context 
      where a value of type [Top->Top] is expected.

      Progress becomes false:

        empty |-- unit 1 \in Top
        [unit 1] is stuck!

         [T_Sub + S_Funny3]   [T_Sub + S_Top]
        |-- unit : Top->Top    |-- 1 : Top
        -----------------------------------
                |-- unit 1 : Top

      Preservation remains true (can't think of anything well typed that steps!)

    - Suppose we add the following subtyping rule:

                               ----------------          (S_Funny4)
                               Top->Top <: Unit

      This rule says: wherever a [Unit] is expected, I can use a [Top->Top] 
      safely.

      Neither become false: there's not much to do when a value of [Unit]
        is expected.
      
    - Suppose we add the following reduction rule:

                             ---------------------      (ST_Funny5)
                             (unit t) --> (t unit)

      Neither beocme false: [unit t] cannot be typed, because [unit] doesn't
        have an arrow type nor it can be generalized to one.

    - Suppose we add the same reduction rule _and_ a new typing rule:

                             ---------------------       (ST_Funny5)
                             (unit t) --> (t unit)

                           ---------------------------     (T_Funny6)
                           empty |-- unit \in Top->Top

      Progress remains true: now [unit t] can be typed.

      Preservation becomes false:

        empty |-- unit true \in Top
        unit true --> true unit
        [true unit] is ill-typed!
      
    - Suppose we _change_ the arrow subtyping rule to:

                          S1 <: T1 S2 <: T2
                          -----------------              (S_Arrow')
                          S1->S2 <: T1->T2

      Both the argument and the result type are covariant.

      Normally, a function accepts a stronger argument that it expects.

        empty |-- (\f:(Nat*Nat)->Nat, f (1,2) + 3) (\p:Top, 4) \in Nat

      But [S_Arrow'] entails the opposite! A function now "works" with a weaker
      argument, but this breaks stuff.

      Progress remains true (abstraction are values,
        substitution is always possible).

      Preservation becomes false:

        empty |-- (\f:Top->Bool, f unit) (\p:Bool, if p then true else false) \in Bool
        (\f:Top->Bool, f unit) (\p:Bool, if p then true else false) -->
          (\p:Bool, if p then true else false) unit.
        [empty |-- (\p:Bool, if p then true else false) unit] is ill-typed!

        empty |-- (\f:Top->Nat, f unit + 3) (\n:Nat, n + 4) \in Nat       
        (\f:Top->Nat, f unit + 3) (\n:Nat, n + 4) --> (\n:Nat, n + 4) unit + 3
        [(\n:Nat, n + 4) unit + 3] is ill typed!
*)

(* Do not modify the following line: *)
Definition manual_grade_for_variations : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Exercise: Adding Products *)

(** **** Exercise: 5 stars, standard (products)

    Adding pairs, projections, and product types to the system we have
    defined is a relatively straightforward matter.  Carry out this
    extension by modifying the definitions and proofs above:

    - Constructors for pairs, first and second projections, and
      product types have already been added to the definitions of
      [ty] and [tm].  Also, the definition of substitution has been
      extended.

    - Extend the surrounding definitions accordingly (refer to chapter
      [MoreSTLC]):

        - value relation
        - operational semantics
        - typing relation

    - Extend the subtyping relation with this rule:

                        S1 <: T1    S2 <: T2
                        --------------------   (S_Prod)
                         S1 * S2 <: T1 * T2

    - Extend the proofs of progress, preservation, and all their
      supporting lemmas to deal with the new constructs.  (You'll also
      need to add a couple of completely new lemmas.) *)

(* Do not modify the following line: *)
Definition manual_grade_for_products_value_step : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_products_subtype_has_type : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_products_progress : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_products_preservation : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Formalized "Thought Exercises" *)

(** The following are formal exercises based on the previous "thought
    exercises." *)

Ltac invert_arrow :=
  match goal with
  | H : _ <: <{_ -> _}> |- _ =>
      apply sub_inversion_arrow in H; auto;
      destruct H as [U1 [U2 [Heq [H1 H2]]]]; subst;
      inversion Heq; subst
  end.

Module FormalThoughtExercises.
Import Examples.
Notation p := "p".
Notation a := "a".

Definition TF P := P \/ ~P.

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1a) *)

(* ~1 min *)
Theorem formal_subtype_instances_tf_1a:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T->S}> <: <{T->S}>).
Proof with eauto.
  left...  Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1b) *)
Theorem formal_subtype_instances_tf_1b:
  TF (forall S T U V, S <: T -> U <: V ->
         <{Top->U}> <: <{S->Top}>).
Proof with eauto.
  left...  Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1c) *)
Theorem formal_subtype_instances_tf_1c:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(C->C)->(A*B)}> <: <{(C->C)->(Top*B)}>).
Proof with eauto.
  left...  Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1d) *)
Theorem formal_subtype_instances_tf_1d:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T->(T->U)}> <: <{S->(S->V)}>).
Proof with eauto.
  left...  Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1e) *)

(* +35 min - forgot about the inversion lemmas... *)
Theorem formal_subtype_instances_tf_1e:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(T->T)->U}> <: <{(S->S)->V}>).
Proof with eauto.
  right. intro Bad.
  specialize (Bad <{Unit}> <{Top}> <{Unit}> <{Top}>)...
  
  (* haven't learned anything have ya *)
  apply sub_inversion_arrow in Bad...
  decompose record Bad.
  inversion H; subst.

  apply sub_inversion_arrow in H0.
  decompose record H0.
  inversion H1; subst.

  apply sub_inversion_Unit in H3.
  discriminate.
Qed.

(*
  assert (H : <{Unit}> <: <{Top}>)...
  specialize (Bad H H).
  remember <{ (Top -> Top) -> Unit }> as S1.
  remember <{ (Unit -> Unit) -> Top }> as S2.

  induction Bad; subst; try solve_by_invert...
  - apply IHBad1...
    exfalso.
    apply IHBad2...
  
   apply sub_inversion_arrow in Bad2.
    destruct Bad2 as [U1 [U2 [Heq [H1 H2]]]]; subst.
    apply sub_inversion_arrow in Bad1.
    destruct Bad1 as [S1 [S2 [Heq' [H1' H2']]]]; subst.
    inversion Heq'; subst; clear Heq'.
    admit.

    (* stuck: how do I deal with transitivity? *)
  - inversion H3; subst...
    + admit.
    + inversion H4; subst...
Abort. *)
  
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1f) *)
Theorem formal_subtype_instances_tf_1f:
  TF (forall S T U V, S <: T -> U <: V ->
         <{((T->S)->T)->U}> <: <{((S->T)->S)->V}>).
Proof.
  left. intros.
  repeat (apply S_Arrow; auto).
Qed.

(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1g) *)

(* ~5 min *)
Theorem formal_subtype_instances_tf_1g:
  TF (forall S T U V, S <: T -> U <: V ->
         <{S*V}> <: <{T*U}>).
Proof with eauto.
  right. intro Bad.
  specialize (Bad <{Unit}> <{Top}> <{Unit}> <{Top}>).

  apply sub_inversion_product in Bad...
  destruct Bad as [U1 [U2 [Eq [H1 H2]]]].
  inversion Eq; subst.
  apply sub_inversion_Unit in H2. discriminate.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_instances_tf_2a) *)

(* 9:07 min - wasting time trying to automate the proof, Ltac
   refuses to collaborate *)
Theorem formal_subtype_instances_tf_2a:
  TF (forall S T,
         S <: T ->
         <{S->S}> <: <{T->T}>).
Proof with auto.
  right. intros Bad.
  specialize (Bad <{Unit}> <{Top}>).
  apply sub_inversion_arrow in Bad...
  decompose record Bad.
  inversion H; subst.
  apply sub_inversion_Unit in H0.
  discriminate.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_instances_tf_2b) *)

(* 6:37 min *)
Theorem formal_subtype_instances_tf_2b:
  TF (forall S,
         S <: <{A->A}> ->
         exists T,
           S = <{T->T}> /\ T <: A).
Proof with auto.
  right. intro Bad.
  assert (<{Top->A}> <: <{A->A}>) by auto.
  decompose record (Bad _ H).
  solve_by_inverts 2.
Qed.

Lemma neq_nat : forall n, n <> S n.
Proof. induction n.
  - discriminate.
  - intro Bad.
    injection Bad. contradiction.
Qed.

(** [] *)
Print ty_ind.
(** **** Exercise: 2 stars, standard, optional (formal_subtype_instances_tf_2d)

    Hint: Assert a generalization of the statement to be proved and
    use induction on a type (rather than on a subtyping
    derviation). *)

(* 37:14 min + *)

Lemma sub_arrow_silly : forall S T, ~ S <: <{S->T}>.
Proof with eauto.
  intros S T Bad.
  generalize dependent T.
  induction S; intros T H;
  apply sub_inversion_arrow in H;
        destruct H as [U1 [U2 [Heq [H1 H2]]]];
  try discriminate.
  inversion Heq; subst; clear Heq.
  apply IHS1 with U2.
Abort.
  
Theorem formal_subtype_instances_tf_2d:
  TF (exists S,
         S <: <{S->S}>).
Proof.
  right. intros [S].

  specialize (sub_arrow_silly H).
  (* 28:51 min *)
  assert (neq_arrow : forall T, T <> <{T->T}>).
  { induction T; intro Bad; try discriminate.
    injection Bad; intros; clear Bad.
    rewrite H1 in IHT1.
    apply IHT1.
    f_equal; assumption. }

  induction S;

  try (apply sub_inversion_arrow in H;
       decompose record H;
       discriminate).

  apply sub_inversion_arrow in H.
  destruct H as [U1 [U2 [Eq [H1 H2]]]].
  inversion Eq; subst; clear Eq.

  


  (* remember <{S->S}> as A.
  induction H; subst. *)

(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_instances_tf_2e) *)
Theorem formal_subtype_instances_tf_2e:
  TF (exists S,
         <{S->S}> <: S).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfa) *)
Theorem formal_subtype_concepts_tfa:
  TF (exists T, forall S, S <: T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfb) *)
Theorem formal_subtype_concepts_tfb:
  TF (exists T, forall S, T <: S).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfc) *)
Theorem formal_subtype_concepts_tfc:
  TF (exists T1 T2, forall S1 S2, <{S1*S2}> <: <{T1*T2}>).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfd) *)
Theorem formal_subtype_concepts_tfd:
  TF (exists T1 T2, forall S1 S2, <{T1*T2}> <: <{S1*S2}>).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfe) *)
Theorem formal_subtype_concepts_tfe:
  TF (exists T1 T2, forall S1 S2, <{S1->S2}> <: <{T1->T2}>).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tff) *)
Theorem formal_subtype_concepts_tff:
  TF (exists T1 T2, forall S1 S2, <{T1->T2}> <: <{S1->S2}>).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfg) *)

Theorem formal_subtype_concepts_tfg:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f (S i) <: f i)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfh) *)
Theorem formal_subtype_concepts_tfh:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f i <: f (S i))).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (formal_proper_subtypes) *)
Theorem formal_proper_subtypes:
  TF (forall T,
         ~(T = <{Bool}> \/ (exists n, T = <{Base n}>) \/ T = <{Unit}>) ->
         exists S,
           S <: T /\ S <> T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Definition smallest_largest HT :=
  (* There exists a smallest and a largest. *)
  (exists TS TL, forall T, TS <: T /\ T <: TL <-> HT T)
  \/
  (* There exists a smallest, but no largest. *)
  ((exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists a largest, but not smallest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   (exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists neither a smallest nor a largest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T)).

(** **** Exercise: 3 stars, advanced, optional (formal_small_large_1) *)
Theorem formal_small_large_1:
  smallest_largest
  (fun T =>
   empty |-- <{(\p:T*Top, p.fst) ((\z:A, z), unit)}> \in <{A->A}>).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (formal_small_large_2) *)
Theorem formal_small_large_2:
  smallest_largest
  (fun T =>
   empty |-- <{(\p:(A->A)*(B->B), p) ((\z:A, z), (\z:B, z))}> \in T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (formal_small_large_3) *)
Theorem formal_small_large_3:
  smallest_largest
  (fun T =>
   (a |-> A) |-- <{(\p:A*T, (p.snd) (p.fst)) (a, \z:A, z)}> \in A).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (formal_small_large_4) *)
Theorem formal_small_large_4:
  smallest_largest
  (fun T =>
   exists S,
     empty |-- <{\p:A*T, (p.snd) (p.fst)}> \in S).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Definition smallest P :=
  TF (exists TS, forall T, TS <: T <-> P T).

(** **** Exercise: 3 stars, standard, optional (formal_smallest_1) *)
Theorem formal_smallest_1:
  smallest
  (fun T =>
   exists S t,
     empty |-- <{ (\x:T, x x) t }> \in S).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (formal_smallest_2) *)
Theorem formal_smallest_2:
  smallest
  (fun T =>
   empty |-- <{(\x:Top, x) ((\z:A, z), (\z:B, z))}> \in T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End FormalThoughtExercises.

End STLCSub.

(* 2024-01-03 15:04 *)
