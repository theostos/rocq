Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Set Definitional UIP.

Record ProofBox (P : SProp) : Type := proof_box { proof_value : P }.
Register ProofBox as kernel.unit_like.
Record Box (A : Type) := box { value : A }.
Record Trans (P : nat -> SProp) := trans {
  app : forall n, Box (ProofBox (P n))
}.
Inductive EqS (A : Type) (x : A) : A -> SProp := rfl : EqS A x x.
Definition transport (A : Type) (x y : A) (e : EqS A x y) (B : Type) (v : B) : B :=
  match e with rfl _ _ => v end.

(* Transport, application, projection, functional eta, projection. The last
   singleton type depends on the fresh function binder, not a dummy subject. *)
Goal forall A (x y : A) (e : EqS A x y) P (p : forall n, P n) (t : Trans P),
  transport A x y e (Trans P) t = trans P (fun n => box _ (proof_box (P n) (p n))).
Proof. intros A x y e P p t.
  exact_no_check (eq_refl (trans P (fun n => box _ (proof_box (P n) (p n))))). Qed.

Goal forall A (x y : A) (e : EqS A x y) (Q : SProp) (q : Q)
    P (p : forall n, P n) (f : Q -> Trans P),
  trans P (fun n => box _ (proof_box (P n) (p n))) =
  transport A x y e (Q -> Trans P) f q.
Proof. intros A x y e Q q P p f.
  exact_no_check (eq_refl (trans P (fun n => box _ (proof_box (P n) (p n))))). Qed.

Goal forall A (x y : A) (e : EqS A x y) P (p : forall n, P n)
    (f : nat -> Trans P),
  transport A x y e (nat -> Trans P) f =
  (fun _ => trans P (fun n => box _ (proof_box (P n) (p n)))).
Proof. intros A x y e P p f.
  exact_no_check (eq_refl (fun _ : nat => trans P (fun n => box _ (proof_box (P n) (p n))))).
Qed.

(* Functional eta and transport must not erase relevant data. *)
Goal forall A (x y : A) (e : EqS A x y) (f : nat -> Box nat),
  transport A x y e (nat -> Box nat) f = (fun n => box nat n).
Proof. intros A x y e f.
  exact_no_check (eq_refl (fun n => box nat n)). Fail Qed. Abort.
Goal forall A (x y : A) (e : EqS A x y) (f : nat -> Box nat),
  (fun n => box nat n) = transport A x y e (nat -> Box nat) f.
Proof. intros A x y e f.
  exact_no_check (eq_refl (fun n => box nat n)). Fail Qed. Abort.
