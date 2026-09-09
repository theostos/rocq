(* Record eta must not evaluate a costly record producer just to compare it
   with its own projections. Exercise the kernel at Qed in both directions. *)
Unset Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Record Box := box { value : nat }.

Fixpoint duplicate (n : nat) : nat :=
  match n with O => O | S k => Nat.add (duplicate k) (duplicate k) end.
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
