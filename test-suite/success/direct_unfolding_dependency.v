Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.

Record Box := box { value : nat }.

(* Reducing this application is expensive, but conversion only needs to
   unfold [wrapped] and compare two occurrences of [expensive]. *)
Fixpoint duplicate (n : nat) : nat :=
  match n with
  | O => O
  | S n => Nat.add (duplicate n) (duplicate n)
  end.
Definition expensive (n : nat) := duplicate 32.
Definition wrapped (n : nat) := box (expensive n).
Strategy -10 [expensive].
Strategy 10 [wrapped].

Definition direct_dependency (n : nat) :
  expensive n = value (wrapped n).
Proof. exact_no_check (eq_refl (expensive n)). Timeout 5 Qed.
Definition direct_dependency_reverse (n : nat) :
  value (wrapped n) = expensive n.
Proof. exact_no_check (eq_refl (expensive n)). Timeout 5 Qed.

(* Selecting an unfolding direction must not bypass the comparison. *)
Definition successor_box (n : nat) := box (S n).
Fail Definition unequal (n : nat) :
  n = value (successor_box n) := eq_refl _.
