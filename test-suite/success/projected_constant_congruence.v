Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Record Ops := ops { run : nat -> nat }.

(* A constant dictionary has NO wrapper arguments. Its method's arguments
   must still be compared before unfolding an expensive implementation. *)
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

(* A genuine wrapper parameter is different: unfold to discard it without
   forcing its expensive value. Do not count later method arguments as
   arguments to the wrapper itself. *)
Definition parameterized (_ : nat) := ops (fun n => n).
Goal run (parameterized (run slow_ops 26)) 7 = run (parameterized 0) 7.
Proof. exact_no_check (eq_refl (run (parameterized (run slow_ops 26)) 7)). Timeout 5 Qed.
Goal run (parameterized 0) 7 = run (parameterized (run slow_ops 26)) 7.
Proof. exact_no_check (eq_refl (run (parameterized 0) 7)). Timeout 5 Qed.

(* Transparent aliases (e.g. inferInstance applied to another instance) must
   also expose their method before comparing discarded record parameters. *)
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
