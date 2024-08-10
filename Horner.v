Require Import List.
Require Import Lia.
Require Nat.
Import ListNotations.

Fixpoint eval_poly (x : nat) (cf : list nat) :=
  match cf with
  | [] => 0
  | an :: cf' => eval_poly x cf' + an * Nat.pow x (length cf')
  end.

Fixpoint horner_loop (acc : nat) (x : nat) (cf : list nat) :=
  match cf with
  | [] => acc
  | an :: cf' => horner_loop (acc * x + an) x cf'
  end.

Definition horner (x : nat) (cf : list nat) := horner_loop 0 x cf.

Compute horner 2 [3;0;2;1].
Compute horner 2 [0;2;1] + 3 * Nat.pow 2 3.

(* 1h17min + *)
Lemma add_assoc : forall n m o, n + m + o = n + (m + o).
Proof. lia.  Qed.

Lemma mult_assoc : forall n m o, n * m * o = n * (m * o).
Proof. lia.  Qed.

(* horner_loop acc x cf =
acc * Nat.pow x (length cf - 1) + horner_loop 0 x cf. *)

Definition g1 acc1 acc2 x cf := horner_loop (acc1 + acc2) x cf.
Definition g2 acc1 acc2 x cf := acc1 * Nat.pow x (length cf) + horner_loop acc2 x cf.

(* do unit tests before enunciating facts! *)
Compute g1 12 3 5 [7;5].
Compute g2 12 3 5 [7;5].

Compute g1 1 2 3 [42].
Compute g2 1 2 3 [42]. (* wtf... it was [length cf] and not its predecessor all along... (wasted 2h on this!) *)

Lemma horner_loop_plus_unsound : forall cf acc1 acc2 x,
  False ->
  horner_loop (acc1 + acc2) x cf =
  acc1 * Nat.pow x (length cf - 1) + horner_loop acc2 x cf. (* SUBTRACTING ONE IS TEMPTING, BUT IT'S WRONG!! *)
Proof.
    (* consider doing induction on either [acc1] or [acc2] and using sum properties *)
  induction cf as [| a cf' IH]; intros acc1 acc2 x.
  * simpl. lia.
  * simpl.    remember (length cf') as len.
    replace ((acc1 + acc2) * x + a) with (acc1 * x + (acc2 * x + a)).
    rewrite (IH (acc1 * x) (acc2 * x + a) x).
    destruct cf' as [| b cf''] eqn:Eqcf'.
    - simpl in *; subst. (* stuck... *)
    (* replace (len - 0) with (S (len - 1)). ### nope: what if [cf'] is [nil]? *)
    Fail rewrite PeanoNat.Nat.pow_succ_r.
Abort.

Definition h1 accu a x cf := (accu * x + a) * Nat.pow x (length cf) + horner_loop 0 x cf.

Definition h2 accu a x cf := horner_loop (accu + a) x cf.

Definition h3 accu a x cf := horner_loop accu x (a :: cf).
 
Compute 3 * Nat.pow 3 1 + horner_loop 0 3 [42].
Compute horner_loop 3 3 [42].
Compute horner_loop 0 3 [3; 42].

Compute h1 2 3 9 [3;42].
Compute h3 2 3 9 [3;42].

Lemma horner_loop_plus_fail' : forall cf acc a x,
  horner_loop acc x (a :: cf) =
  (acc * x + a) * Nat.pow x (length cf) + horner_loop 0 x cf.
Proof.
  induction cf as [| b cf' IH]; intros acc a x.
  * simpl. lia.
  * simpl in *.
    replace ((acc * x + a) * x + b) with (acc * x * x + (a * x + b)).
    rewrite (IH (acc * x) (a * x + b) x).
    replace ((acc * x + a) * (x * Nat.pow x (length cf')))
    with ((acc * x * x + a * x) * Nat.pow x (length cf')).
  Abort. (* this is mental *)

Lemma horner_loop_plus_fail'' : forall cf acc1 acc2 x,
  horner_loop (acc1 + acc2) x cf =
  acc1 * Nat.pow x (length cf - 1) + horner_loop acc2 x cf. 
Proof.
  intros cf acc1. generalize dependent cf.
  induction acc1; intros cf acc2 x; simpl.
  * reflexivity.
  * rewrite add_assoc. replace (S (acc1 + acc2)) with (acc1 + (1 + acc2)).
    rewrite (IHacc1 cf (1 + acc2) x).
Abort.

(* +3h *)
Lemma horner_loop_plus : forall cf acc1 acc2 x,
  horner_loop (acc1 + acc2) x cf =
  acc1 * Nat.pow x (length cf) + horner_loop acc2 x cf. (* DO NOT SUBTRACT ONE *)
Proof.
  induction cf as [| a cf' IH]; intros acc1 acc2 x.
  * simpl. lia.
  * simpl.
    replace ((acc1 + acc2) * x + a) with (acc1 * x + (acc2 * x + a)).
    rewrite (IH (acc1 * x) (acc2 * x + a) x).
    rewrite mult_assoc. reflexivity. lia.
Qed.

Theorem horner_correct : forall x cf,
  eval_poly x cf = horner x cf.
Proof.
  intros x cf.
  generalize dependent x.
  induction cf as [| a cf' IH].
  * reflexivity.
  * intros x. unfold horner in *. simpl. rewrite IH.
    replace (a) with (a + 0).
    rewrite (horner_loop_plus cf' a 0 x). lia. lia.
Qed.
