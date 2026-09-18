Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.

Inductive U := unit_value.
Register U as kernel.unit_like.
Definition bool_alias (b : bool) := b.
Definition family (b : bool) : Type := if b then U else nat.

(* A type-level match can be blocked on a transparent definition, not just a
   literal constructor. Inspect its WHNF before deciding singleton eligibility. *)
Goal forall f g : family (bool_alias true), f = g.
Proof. intros f g. exact_no_check (eq_refl f). Qed.
Goal forall f : family (bool_alias true), unit_value = f.
Proof. intro f. exact_no_check (eq_refl unit_value). Qed.
Section Named.
  Variables f g : family (bool_alias true).
  Goal f = g.
  Proof. exact_no_check (eq_refl g). Qed.
End Named.

(* The discriminant can itself contain a match, fixpoint or projection. *)
Definition nested (b : bool) := if bool_alias b then bool_alias true else false.
Goal forall f g : family (nested true), f = g.
Proof. intros f g. exact_no_check (eq_refl f). Qed.
Fixpoint descend (n : nat) : bool :=
  match n with O => bool_alias true | S k => descend k end.
Definition numeral := 3.
Goal forall f g : family (descend numeral), f = g.
Proof. intros f g. exact_no_check (eq_refl f). Qed.
Record Flag := flag { value : bool }.
Definition chosen := flag (bool_alias true).
Goal forall f g : family (value chosen), f = g.
Proof. intros f g. exact_no_check (eq_refl f). Qed.

Inductive ParamUnit (A : Type) := param_unit.
Register ParamUnit as kernel.unit_like.
Definition indexed (b : bool) (A B : Type) :=
  if bool_alias b then ParamUnit A else ParamUnit B.
Goal forall A B (f g : indexed true A B), f = g.
Proof. intros A B f g. exact_no_check (eq_refl f). Qed.
Goal forall A B (f : indexed false A B), f = param_unit B.
Proof. intros A B f. exact_no_check (eq_refl (param_unit B)). Qed.

Record Box (A : Type) := box { contents : A }.
Goal forall f g : Box (family (bool_alias true)), f = g.
Proof. intros f g. exact_no_check (eq_refl f). Qed.

(* No guessing a neutral branch, collapsing relevant data, or ignoring
   opacity. These must reach and fail kernel checking, not just elaboration. *)
Goal forall f g : family (bool_alias false), f = g.
Proof. intros f g. exact_no_check (eq_refl f). Fail Qed. Abort.
Goal forall b (f g : family (bool_alias b)), f = g.
Proof. intros b f g. exact_no_check (eq_refl f). Fail Qed. Abort.
Goal forall f g : Box (family (bool_alias false)), f = g.
Proof. intros f g. exact_no_check (eq_refl f). Fail Qed. Abort.
Opaque bool_alias.
Goal forall f g : family (bool_alias true), f = g.
Proof. intros f g. exact_no_check (eq_refl f). Fail Qed. Abort.
Transparent bool_alias.
Goal forall f g : family (bool_alias true), f = g.
Proof. intros f g. exact_no_check (eq_refl f). Qed.
