Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.

Record ProofBox (P : SProp) : Type := proof_box { proof_value : P }.
Register ProofBox as kernel.unit_like.
Record Box (A : Type) := box { value : A }.
Record Dependent (P : bool -> SProp) := dependent {
  tag : bool;
  payload : Box (ProofBox (P tag))
}.

(* The payload type depends on the actual record, not an invented scrutinee. *)
Goal forall (P : bool -> SProp) (r : Dependent P)
  (x : Box (ProofBox (P (tag P r)))), payload P r = x.
Proof. intros P r x. exact_no_check (eq_refl (payload P r)). Qed.

(* A record with a relevant boolean field is not itself a singleton. *)
Goal forall (P : bool -> SProp) (r s : Dependent P), r = s.
Proof. intros P r s. exact_no_check (eq_refl r). Fail Qed. Abort.

Inductive U := tt.
Register U as kernel.unit_like.
Definition Alias (A : Type) := Box A.
Goal forall x y : Alias U, value _ x = value _ y.
Proof. intros x y. exact_no_check (eq_refl (value _ x)).
Opaque Alias.
Fail Qed.
Transparent Alias.
Qed.
