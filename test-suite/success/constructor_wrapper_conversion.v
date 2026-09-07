Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Record Inner := inner { value : nat }.
Record Outer := outer { bits : Inner }.
Fixpoint duplicate (n : nat) : nat :=
  match n with
  | O => O
  | S n => Nat.add (duplicate n) (duplicate n)
  end.
Definition expensive (n : nat) := duplicate 32.
Definition wrap (x : Inner) := outer x.
Definition inner_op (x : Inner) := inner (expensive (value x)).
Definition outer_op (x : Outer) := outer (inner (expensive (value (bits x)))).

(* Unfolding [wrap] exposes the constructor immediately. Eta-expanding it
   first can instead force [expensive], whose argument also contains [wrap]. *)
Goal forall x, wrap (inner_op x) = outer_op (wrap x).
Proof. intro x; exact_no_check (eq_refl (wrap (inner_op x))). Timeout 5 Qed.
Goal forall x, outer_op (wrap x) = wrap (inner_op x).
Proof. intro x; exact_no_check (eq_refl (wrap (inner_op x))). Timeout 5 Qed.

Goal wrap (inner 0) = outer (inner 1).
Proof. exact_no_check (eq_refl (outer (inner 1))). Fail Qed. Abort.
Definition sealed (x : Inner) : Outer.
Proof. exact (outer x). Qed.
Goal forall x, sealed x = outer x.
Proof. intro x; exact_no_check (eq_refl (outer x)). Fail Qed. Abort.
Goal forall x, outer x = sealed x.
Proof. intro x; exact_no_check (eq_refl (outer x)). Fail Qed. Abort.
