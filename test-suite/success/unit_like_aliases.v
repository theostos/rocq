Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Record ProofBox (P : SProp) : Type := proof_box { proof_value : P }.
Register ProofBox as kernel.unit_like.
Record Box (A : Type) := box { value : A }.
Definition Alias (A : Type) := A.
Definition Alias2 (A : Type) := Alias A.

Goal forall (P : SProp) (x y : Alias2 (Box (Alias (ProofBox P)))) , x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Qed.

(* A local's type computes by selecting the Hom field of a concrete category,
   as in Mathlib's punitCoconeIsColimit._proof_4. The endpoints stay neutral. *)
Record Quiver (A : Type) := quiver { Hom : A -> A -> Type }.
Record Category (A : Type) := category { toQuiver : Quiver A }.
Definition discrete (A : Type) (P : SProp) : Category A :=
  category A (quiver A (fun _ _ => Box (ProofBox P))).
Definition Morphism A (c : Category A) x y := Hom A (toQuiver A c) x y.
Definition canonical A P (p : P) (x y : A) : Morphism A (discrete A P) x y.
Proof. exact (box _ (proof_box P p)). Qed.

Goal forall A P (p : P) (x y : A) (m : Morphism A (discrete A P) x y),
  m = canonical A P p x y.
Proof. intros A P p x y m. exact_no_check (eq_refl m). Qed.
Goal forall A P (p : P) (x y : A) (m : Morphism A (discrete A P) x y),
  canonical A P p x y = m.
Proof. intros A P p x y m. exact_no_check (eq_refl m). Qed.
Goal forall A P (x y : A) (m n : Morphism A (discrete A P) x y), m = n.
Proof. intros A P x y m n. exact_no_check (eq_refl m). Qed.

Inductive Unit := unit.
Register Unit as kernel.unit_like.
Goal forall (x y : Alias Unit), x = y.
Proof. intros x y. exact_no_check (eq_refl x). Qed.

(* Aliasing never erases relevant fields or unknown parameters. *)
Goal forall (x y : Alias2 (Box nat)), x = y.
Proof. intros x y. exact_no_check (eq_refl x). Fail Qed. Abort.
Goal forall (A : Type) (x y : Alias (Box A)), x = y.
Proof. intros A x y. exact_no_check (eq_refl x). Fail Qed. Abort.
Definition numbered (A : Type) : Category A :=
  category A (quiver A (fun _ _ => Box nat)).
Goal forall A (x y : A) (m n : Morphism A (numbered A) x y), m = n.
Proof. intros A x y m n. exact_no_check (eq_refl m). Fail Qed. Abort.
Goal forall A (c : Category A) (x y : A) (m n : Morphism A c x y), m = n.
Proof. intros A c x y m n. exact_no_check (eq_refl m). Fail Qed. Abort.

(* Opaque type aliases and category values remain opaque. *)
Definition Hidden P := Box (ProofBox P).
Goal forall P (x y : Hidden P), x = y.
Proof. intros P x y. exact_no_check (eq_refl x).
Opaque Hidden.
Fail Qed.
Transparent Hidden.
Qed.
Goal forall A P (x y : A) (m n : Morphism A (discrete A P) x y), m = n.
Proof. intros A P x y m n. exact_no_check (eq_refl m).
Opaque discrete.
Fail Qed.
Transparent discrete.
Qed.

(* Do not replace a neutral record in a dependent field's type by a dummy. *)
Record Dependent := dependent { field_type : Type; field : field_type }.
Definition DepAlias := Dependent.
Goal forall (x : DepAlias) (y : field_type x), field x = y.
Proof. intros x y. exact_no_check (eq_refl (field x)). Fail Qed. Abort.

(* The query must not evaluate recursive type computations to find a unit. *)
Fixpoint slow (n : nat) : nat :=
  match n with O => O | S k => Nat.add (slow k) (slow k) end.
Definition computed (P : SProp) :=
  match slow 32 with O => ProofBox P | S _ => ProofBox P end.
Goal forall P (x y : computed P), x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Timeout 5 Fail Qed. Abort.

Unset Kernel Conversion Dep Heuristic.
Goal forall A P (x y : A) (m n : Morphism A (discrete A P) x y), m = n.
Proof. intros A P x y m n. exact_no_check (eq_refl m). Qed.
