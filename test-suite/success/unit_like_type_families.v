Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.

Inductive U := unit_value.
Register U as kernel.unit_like.
Definition family (b : bool) : Type := if b then U else nat.

(* Neither a local binder nor a named assumption needs an explicit U type. *)
Goal forall f : family true, f = unit_value.
Proof. intro f. exact_no_check (eq_refl unit_value). Qed.
Goal forall f g : family true, f = g.
Proof. intros f g. exact_no_check (eq_refl f). Qed.
Section Named.
  Variables f g : family true.
  Goal f = g.
  Proof. exact_no_check (eq_refl g). Qed.
  Goal unit_value = f.
  Proof. exact_no_check (eq_refl unit_value). Qed.
End Named.

Inductive ParamUnit (A : Type) := param_unit.
Register ParamUnit as kernel.unit_like.
Definition indexed_family (b : bool) (A B : Type) :=
  if b then ParamUnit A else ParamUnit B.
Goal forall A B (f : indexed_family true A B), f = param_unit A.
Proof. intros A B f. exact_no_check (eq_refl (param_unit A)). Qed.
Goal forall A B (f : indexed_family false A B), param_unit B = f.
Proof. intros A B f. exact_no_check (eq_refl (param_unit B)). Qed.

(* A branch with a constructor-local definition exercises lazy let substitution. *)
Inductive WithLet : Type := with_let : let A := U in A -> WithLet.
Definition let_family (x : WithLet) : Type := match x with with_let _ => U end.
Goal forall f : let_family (with_let unit_value), f = unit_value.
Proof. intro f. exact_no_check (eq_refl unit_value). Qed.

(* Relevant alternatives and stuck type-level matches are not singleton types. *)
Goal forall f : family false, f = 0.
Proof. intro f. exact_no_check (eq_refl 0). Fail Qed. Abort.
Goal forall b (f g : family b), f = g.
Proof. intros b f g. exact_no_check (eq_refl f). Fail Qed. Abort.
