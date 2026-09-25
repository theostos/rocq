(* Projected applications of transparent record wrappers: a wrapper
   parameter is discarded by unfolding without forcing its value, while the
   arguments of a projected method are compared before an expensive
   implementation unfolds. *)
Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Record Ops := ops { run : nat -> nat }.

(* A constant dictionary has no wrapper arguments. *)
Definition slow_ops := ops (fun n =>
  (fix go (n : nat) : nat :=
    match n with
    | O => O
    | S k => match go k with O => go k | S _ => O end
    end) n).
Definition identity (n : nat) := n.
Goal run slow_ops 26 = run slow_ops (identity 26).
Proof. exact_no_check (eq_refl (run slow_ops 26)). Timeout 5 Qed.
Goal run slow_ops (identity 26) = run slow_ops 26.
Proof. exact_no_check (eq_refl (run slow_ops 26)). Timeout 5 Qed.
Goal forall x : nat, (fun _ => run slow_ops 26) x =
                    run slow_ops (identity 26).
Proof. intro x. exact_no_check (eq_refl (run slow_ops 26)). Timeout 5 Qed.

(* A wrapper parameter is discarded; the method arguments after the
   projection are not arguments of the wrapper. *)
Definition parameterized (_ : nat) := ops (fun n => n).
Goal run (parameterized (run slow_ops 26)) 7 = run (parameterized 0) 7.
Proof. exact_no_check (eq_refl (run (parameterized (run slow_ops 26)) 7)). Timeout 5 Qed.
Goal run (parameterized 0) 7 = run (parameterized (run slow_ops 26)) 7.
Proof. exact_no_check (eq_refl (run (parameterized 0) 7)). Timeout 5 Qed.

(* Transparent aliases (inferInstance applied to an instance) expose their
   method the same way. *)
Definition infer {A : Type} (a : A) := a.
Definition aliased (n : nat) := infer (parameterized n).
Goal run (aliased (run slow_ops 26)) 7 = run (aliased 0) 7.
Proof. exact_no_check (eq_refl (run (aliased 0) 7)). Timeout 5 Qed.
Goal run (aliased 0) 7 = run (aliased (run slow_ops 26)) 7.
Proof. exact_no_check (eq_refl (run (aliased 0) 7)). Timeout 5 Qed.

Definition captures (n : nat) := infer (ops (fun _ => n)).
Goal run (captures 0) 7 = run (captures 1) 7.
Proof. exact_no_check (eq_refl 0). Fail Qed. Abort.
Definition sealed (n : nat) : Ops.
Proof. exact (aliased n). Qed.
Goal run (sealed 0) 7 = 7.
Proof. exact_no_check (eq_refl 7). Fail Qed. Abort.

(* Relevant method arguments still matter. *)
Definition identity_ops := ops (fun n => n).
Goal run identity_ops 0 = run identity_ops 1.
Proof. exact_no_check (eq_refl 0). Fail Qed. Abort.
Goal run (parameterized 0) 0 = run (parameterized 1) 1.
Proof. exact_no_check (eq_refl 0). Fail Qed. Abort.

(* A bare projection of a constructor wrapper forwarding its source: the
   discarded index is not computed. *)
Record Tagged (tag : nat) : Type := tagged { payload : nat }.
Arguments tagged {tag} _.
Arguments payload {tag} _.
Definition retag {source : nat} (target : nat) (r : Tagged source)
  : Tagged target := tagged (payload r).
Fixpoint duplicate (fuel : nat) : nat :=
  match fuel with O => O | S k => Nat.add (duplicate k) (duplicate k) end.

Goal forall r : Tagged O,
  payload (retag (duplicate 32) r) = payload (retag O r).
Proof. intro r. exact_no_check (eq_refl (payload (retag (duplicate 32) r))). Timeout 5 Qed.
Goal forall r : Tagged O,
  payload (retag O r) = payload (retag (duplicate 32) r).
Proof. intro r. exact_no_check (eq_refl (payload (retag O r))). Timeout 5 Qed.

(* Discarding the index must not discard a changed payload. *)
Goal forall n : nat,
  payload (retag O (@tagged O (S n))) = payload (retag O (@tagged O n)).
Proof. intro n. exact_no_check (eq_refl (payload (retag O (@tagged O (S n))))). Fail Qed. Abort.

Definition sealed_retag {source : nat} (target : nat) (r : Tagged source)
  : Tagged target.
Proof. exact (retag target r). Qed.
Goal forall r : Tagged O, payload (sealed_retag O r) = payload r.
Proof. intro r. exact_no_check (eq_refl (payload r)). Fail Qed. Abort.
