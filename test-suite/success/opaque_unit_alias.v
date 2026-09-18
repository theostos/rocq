Inductive Unit := unit.
Register Unit as kernel.unit_like.
Definition HiddenUnit := Unit.

Goal forall (x y : HiddenUnit), x = y.
Proof. intros x y. exact_no_check (eq_refl x).
Opaque HiddenUnit.
Fail Qed.
Transparent HiddenUnit.
Qed.
