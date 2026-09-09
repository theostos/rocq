(* A named primitive projection is a transparent constant alias, not a Proj
   node at the head of the wrapper's body. It needs the same eta priority. *)
Unset Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Record Inner := inner { value : nat }.
Record Outer := outer { bits : Inner }.
Fixpoint duplicate (n : nat) : nat :=
  match n with O => O | S k => Nat.add (duplicate k) (duplicate k) end.
Definition expensive (_ : nat) := duplicate 32.
Definition named_projection := @bits.
Definition projected (x : Outer) : Inner := named_projection x.
Definition inner_op (x : Inner) := inner (expensive (value x)).
Definition outer_op (x : Outer) := outer (inner_op (projected x)).
Strategy -10 [inner_op expensive].
Strategy 10 [projected outer_op].

Goal forall x, projected (outer_op x) = inner_op (projected x).
Proof. intro x; exact_no_check (eq_refl (projected (outer_op x))). Timeout 5 Qed.
Goal forall x, inner_op (projected x) = projected (outer_op x).
Proof. intro x; exact_no_check (eq_refl (projected (outer_op x))). Timeout 5 Qed.

(* A genuinely opaque alias remains opaque, including through another alias. *)
Definition sealed (x : Outer) : Inner.
Proof. exact (bits x). Qed.
Definition sealed_alias := sealed.
Goal forall n, sealed_alias (outer (inner n)) = inner n.
Proof. intro n; exact_no_check (eq_refl (inner n)). Fail Qed. Abort.
Goal forall n, inner n = sealed_alias (outer (inner n)).
Proof. intro n; exact_no_check (eq_refl (inner n)). Fail Qed. Abort.
