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

  (* horner_loop acc x cf =
  acc * Nat.pow x (length cf - 1) + horner_loop 0 x cf. *)

Lemma horner_loop_plus : forall cf acc1 acc2 x,
  horner_loop (acc1 + acc2) x cf =
  acc1 * Nat.pow x (length cf - 1) + horner_loop acc2 x cf.
Proof.
  (* consider doing induction on either [acc1] or [acc2] and using sum properties *)
  induction cf; intros acc1 acc2 x.
  * simpl. lia.
  * simpl. rewrite add_assoc. rewrite <- IHacc.


Theorem horner_correct : forall x cf,
  eval_poly x cf = horner x cf.
Proof.
  intros x cf.
  remember (length cf) as g.
  generalize dependent x.
  induction cf as [| a cf' IH].
  * reflexivity.
  * intros x. unfold horner in *. simpl. rewrite IH.
