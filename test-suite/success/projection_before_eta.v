(* Delta reduction must precede record eta for projection wrappers too.
   Early eta forces [expensive] instead of exposing the shared field. *)
Unset Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Record Inner := inner { value : nat }.
Record Outer := outer { bits : Inner }.

Fixpoint duplicate (n : nat) : nat :=
  match n with O => O | S k => Nat.add (duplicate k) (duplicate k) end.
Definition expensive (_ : nat) := duplicate 32.
Definition projected (x : Outer) : Inner := bits x.
Definition inner_op (x : Inner) := inner (expensive (value x)).
Definition outer_op (x : Outer) := outer (inner_op (projected x)).

(* Expose the constructor on the right before the projection-only wrapper on
   the left. Dependency probes are disabled to exercise this oracle order. *)
Strategy -10 [inner_op expensive].
Strategy 10 [projected outer_op].

Goal forall x, projected (outer_op x) = inner_op (projected x).
Proof.
  intro x; exact_no_check (eq_refl (projected (outer_op x))).
Timeout 5 Qed.

Goal forall x, inner_op (projected x) = projected (outer_op x).
Proof.
  intro x; exact_no_check (eq_refl (projected (outer_op x))).
Timeout 5 Qed.
