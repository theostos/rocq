Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Set Definitional UIP.

Inductive U := unit_value.
Register U as kernel.unit_like.
Record ProofBox (P : SProp) : Type := proof_box { proof_value : P }.
Register ProofBox as kernel.unit_like.
Record Box (A : Type) := box { value : A }.

Goal forall (b : bool) (u : U), (if b then u else unit_value) = unit_value.
Proof. intros b u. exact_no_check (eq_refl unit_value). Qed.
Goal forall (b : bool) (u : U), u = (if b then unit_value else u).
Proof. intros b u. exact_no_check (eq_refl u). Qed.

(* The case is followed by primitive record eta and a singleton-valued field. *)
Goal forall (P : SProp) (p : P) (b : bool) (u : Box (ProofBox P)),
  box _ (proof_box P p) = (if b then u else box _ (proof_box P p)).
Proof. intros P p b u. exact_no_check (eq_refl (box _ (proof_box P p))). Qed.

Inductive EqS (A : Type) (x : A) : A -> SProp := rfl : EqS A x x.
Definition transport (A : Type) (x y : A) (e : EqS A x y) (B : Type) (v : B) : B :=
  match e with rfl _ _ => v end.

Goal forall A (x y : A) (e : EqS A x y) (u : U),
  transport A x y e U u = unit_value.
Proof. intros A x y e u. exact_no_check (eq_refl unit_value). Qed.
Goal forall A (x y : A) (e : EqS A x y) (u : U),
  u = transport A x y e U u.
Proof. intros A x y e u. exact_no_check (eq_refl u). Qed.

Goal forall A (x y z t : A) (e : EqS A x y) (f : EqS A z t) (u v : U),
  (match e with rfl _ _ => u end) = (match f with rfl _ _ => v end).
Proof. intros A x y z t e f u v.
  exact_no_check (eq_refl (match e with rfl _ _ => u end)). Qed.

Goal forall A (x y : A) (e : EqS A x y) P (p : P) (u : Box (ProofBox P)),
  box _ (proof_box P p) = transport A x y e (Box (ProofBox P)) u.
Proof. intros A x y e P p u. exact_no_check (eq_refl (box _ (proof_box P p))). Qed.

(* Relevant data never becomes judgmentally equal merely because of a case. *)
Goal forall (b : bool), (if b then 0 else 1) = 0.
Proof. intros b. exact_no_check (eq_refl 0). Fail Qed. Abort.
Goal forall A (x y : A) (e : EqS A x y) (n : nat),
  transport A x y e nat n = 0.
Proof. intros A x y e n. exact_no_check (eq_refl 0). Fail Qed. Abort.
Goal forall (b : bool) (x y : Box nat), (if b then x else y) = box nat 0.
Proof. intros b x y. exact_no_check (eq_refl (box nat 0)). Fail Qed. Abort.
