Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Record Ops := ops { run : nat -> nat }.
Fixpoint duplicate n :=
  match n with O => O | S k => Nat.add (duplicate k) (duplicate k) end.

(* Computed, rather than syntactically forwarded, method field. *)
Definition method (n : nat) : nat -> nat :=
  match n with O => fun _ => O | S _ => fun _ => O end.
Definition wrapper n := ops (method n).

(* The source arguments 0 and 1 already disprove source congruence. Check
   them before the method arguments, then project and discard those arguments.
   Lean's lazy projected-source comparison has that ordering.
   exact_no_check only avoids an elaborator-side conversion: Qed below must
   check each proof in the kernel and is required to succeed. *)
Goal run (wrapper 0) (duplicate 30) = run (wrapper 1) 0.
Proof. exact_no_check (eq_refl (run (wrapper 1) 0)). Timeout 5 Qed.
Goal run (wrapper 1) 0 = run (wrapper 0) (duplicate 30).
Proof. exact_no_check (eq_refl (run (wrapper 0) (duplicate 30))). Timeout 5 Qed.
Goal forall x : nat, (fun _ : nat => run (wrapper 0) (duplicate 30)) x = run (wrapper 1) 0.
Proof. intro; exact_no_check (eq_refl (run (wrapper 1) 0)). Timeout 5 Qed.

(* A successful source comparison must still compare all outer arguments. *)
Definition identity_ops := ops (fun n => n).
Goal run identity_ops 0 = run identity_ops 1.
Proof. exact_no_check (eq_refl 0). Fail Qed. Abort.

(* Bare projections: after lazy source unfolding exposes a constructor,
   compare only the requested field, never the discarded record fields. *)
Record Selection := selection { chosen : nat; discarded : nat }.
Definition left_selection n := selection 0 n.
Definition right_selection n := selection 0 n.
Definition wrong_selection n := selection 1 n.
Goal chosen (left_selection (duplicate 30)) = chosen (right_selection 1).
Proof. exact_no_check (eq_refl 0). Timeout 5 Qed.
Goal chosen (right_selection 1) = chosen (left_selection (duplicate 30)).
Proof. exact_no_check (eq_refl 0). Timeout 5 Qed.
Goal forall x, chosen (left_selection x) = chosen (right_selection 1).
Proof. intro; exact_no_check (eq_refl 0). Timeout 5 Qed.
Goal chosen (left_selection 0) = chosen (wrong_selection 0).
Proof. exact_no_check (eq_refl 0). Fail Qed. Abort.
Goal left_selection 0 = right_selection 1.
Proof. exact_no_check (eq_refl (left_selection 0)). Fail Qed. Abort.
