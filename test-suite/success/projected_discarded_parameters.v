(* A projected constructor wrapper discards its target index. Comparing every
   argument of [retag] first instead computes a discarded exponential tree.
   This is a standalone kernel fixture, not a replacement for a Lean proof.
   The baseline times out at the first Qed; the forwarding strategy passes. *)
Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.

Record Tagged (tag : nat) : Type := tagged { payload : nat }.
Arguments tagged {tag} _.
Arguments payload {tag} _.

Definition retag {source : nat} (target : nat) (r : Tagged source)
  : Tagged target := tagged (payload r).

(* Definitionally zero, with the same deliberately duplicated recursion as
   the existing EtaBeforeComputation fixture. No large source is generated. *)
Fixpoint duplicate (fuel : nat) : nat :=
  match fuel with
  | O => O
  | S k => Nat.add (duplicate k) (duplicate k)
  end.

(* The payload is independent of the target index. exact_no_check leaves
   conversion to the kernel at Qed; each positive has a bounded deadline. *)
Goal forall r : Tagged O,
  payload (retag (duplicate 32) r) = payload (retag O r).
Proof.
  intro r.
  exact_no_check (eq_refl (payload (retag (duplicate 32) r))).
  Timeout 5 Qed.

Goal forall r : Tagged O,
  payload (retag O r) = payload (retag (duplicate 32) r).
Proof.
  intro r.
  exact_no_check (eq_refl (payload (retag O r))).
  Timeout 5 Qed.

(* Discarding the index must not discard a changed payload. *)
Goal forall n : nat,
  payload (retag O (@tagged O (S n))) = payload (retag O (@tagged O n)).
Proof.
  intro n.
  exact_no_check (eq_refl (payload (retag O (@tagged O (S n))))).
  Fail Qed.
Abort.

(* Qed creates an actual opaque body, not an Opaque transparency hint. *)
Definition sealed_retag {source : nat} (target : nat) (r : Tagged source)
  : Tagged target.
Proof. exact (retag target r). Qed.

Goal forall r : Tagged O, payload (sealed_retag O r) = payload r.
Proof.
  intro r.
  exact_no_check (eq_refl (payload r)).
  Fail Qed.
Abort.
