(* Record eta against a flex: eta first, unless the flex is a constructor or
   projection wrapper, whose unfolding exposes the shared field. *)
Unset Kernel Conversion Dep Heuristic.
Set Primitive Projections.

Fixpoint duplicate (n : nat) : nat :=
  match n with O => O | S k => Nat.add (duplicate k) (duplicate k) end.

(* Eta must not evaluate a costly record producer to compare it with its
   own projections. *)
Module EtaFirst.
Record Box := box { value : nat }.
Definition computed (fuel n : nat) : Box :=
  match duplicate fuel with O => box n | S _ => box (S n) end.

Goal forall n, computed 32 n = box (value (computed 32 n)).
Proof. intro n; exact_no_check (eq_refl (computed 32 n)). Timeout 5 Qed.
Goal forall n, box (value (computed 32 n)) = computed 32 n.
Proof. intro n; exact_no_check (eq_refl (computed 32 n)). Timeout 5 Qed.

(* A stuck producer also retains eta, but changing its field is rejected. *)
Definition picked (n : nat) (left right : Box) : Box :=
  match n with O => left | S _ => right end.
Goal forall n l r, picked n l r = box (value (picked n l r)).
Proof. intros n l r; exact_no_check (eq_refl (picked n l r)). Timeout 5 Qed.
Goal forall n l r, box (value (picked n l r)) = picked n l r.
Proof. intros n l r; exact_no_check (eq_refl (picked n l r)). Timeout 5 Qed.
Goal forall n l r, picked n l r = box (S (value (picked n l r))).
Proof. intros n l r; exact_no_check (eq_refl (picked n l r)).
Fail Qed. Abort.
Goal forall n l r, box (S (value (picked n l r))) = picked n l r.
Proof. intros n l r; exact_no_check (eq_refl (picked n l r)).
Fail Qed. Abort.
End EtaFirst.

(* A projection wrapper unfolds before eta, which would force [expensive]
   instead of exposing the shared field; a named primitive projection is a
   transparent alias of the same kind. The oracle exposes the constructor on
   the right before the wrapper on the left. *)
Module DeltaFirst.
Record Inner := inner { value : nat }.
Record Outer := outer { bits : Inner }.
Definition expensive (_ : nat) := duplicate 32.
Definition projected (x : Outer) : Inner := bits x.
Definition named_projection := @bits.
Definition projected_alias (x : Outer) : Inner := named_projection x.
Definition inner_op (x : Inner) := inner (expensive (value x)).
Definition outer_op (x : Outer) := outer (inner_op (projected x)).
Definition outer_op_alias (x : Outer) := outer (inner_op (projected_alias x)).
Strategy -10 [inner_op expensive].
Strategy 10 [projected projected_alias outer_op outer_op_alias].

Goal forall x, projected (outer_op x) = inner_op (projected x).
Proof. intro x; exact_no_check (eq_refl (projected (outer_op x))). Timeout 5 Qed.
Goal forall x, inner_op (projected x) = projected (outer_op x).
Proof. intro x; exact_no_check (eq_refl (projected (outer_op x))). Timeout 5 Qed.
Goal forall x, projected_alias (outer_op_alias x) = inner_op (projected_alias x).
Proof. intro x; exact_no_check (eq_refl (projected_alias (outer_op_alias x))). Timeout 5 Qed.
Goal forall x, inner_op (projected_alias x) = projected_alias (outer_op_alias x).
Proof. intro x; exact_no_check (eq_refl (projected_alias (outer_op_alias x))). Timeout 5 Qed.

(* An opaque alias remains opaque, including through another alias. *)
Definition sealed (x : Outer) : Inner.
Proof. exact (bits x). Qed.
Definition sealed_alias := sealed.
Goal forall n, sealed_alias (outer (inner n)) = inner n.
Proof. intro n; exact_no_check (eq_refl (inner n)). Fail Qed. Abort.
Goal forall n, inner n = sealed_alias (outer (inner n)).
Proof. intro n; exact_no_check (eq_refl (inner n)). Fail Qed. Abort.
End DeltaFirst.
