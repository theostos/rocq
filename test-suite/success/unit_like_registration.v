Set Primitive Projections.
Set Universe Polymorphism.

(* Registration needs one constructor, no index and no relevant field. *)
Inductive EtaUnit@{u} : Type@{u} := eta_unit.
Register EtaUnit as kernel.unit_like.
Inductive ProofFields (P : SProp) : Type := proof_fields (_ : P).
Register ProofFields as kernel.unit_like.
Inductive PhantomUnit (A : Type) := phantom_unit.
Register PhantomUnit as kernel.unit_like.

Inductive BadIndexedUnit : nat -> Type := bad_indexed_unit : BadIndexedUnit 0.
Fail Register BadIndexedUnit as kernel.unit_like.
Inductive BadRecursiveUnit := bad_recursive_unit : BadRecursiveUnit -> BadRecursiveUnit.
Fail Register BadRecursiveUnit as kernel.unit_like.
(* Unknown relevance is not a certificate of irrelevance at every instance. *)
Inductive QBox@{s;u|} (A : Type@{s;u}) := qbox (_ : A).
Fail Register QBox as kernel.unit_like.
Goal forall (x y : QBox nat), x = y.
Proof. intros x y. exact_no_check (eq_refl x). Fail Qed. Abort.

(* Inhabitants of a registered type are convertible. *)
Example unit_like_constructor_eta (x : EtaUnit) : x = eta_unit.
Proof. exact (eq_refl x). Qed.
Example unit_like_neutral_eta (x y : EtaUnit) : x = y.
Proof. exact (eq_refl x). Qed.
Example unit_like_application_eta (f : EtaUnit -> EtaUnit) (x : EtaUnit) : f x = eta_unit.
Proof. exact (eq_refl eta_unit). Qed.
Example unit_like_applications_eta (f : nat -> EtaUnit) (x y : nat) : f x = f y.
Proof. exact (eq_refl (f x)). Qed.
Axiom dependent_operation : forall A : Type, nat -> A.
Example dependent_unit_like_applications_eta (x y : nat) :
  dependent_operation EtaUnit x = dependent_operation EtaUnit y.
Proof. exact (eq_refl (dependent_operation EtaUnit x)). Qed.
Definition unit_like_match (n : nat) : EtaUnit := match n with O | S _ => eta_unit end.
Example transparent_unit_like_applications_eta (x y : nat) :
  unit_like_match x = unit_like_match y.
Proof. exact (eq_refl (unit_like_match x)). Qed.
Goal forall P (x y : ProofFields P), x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Qed.
Example parameterized_unit_like_eta (A : Type) (x y : PhantomUnit A) : x = y.
Proof. exact (eq_refl x). Qed.
Record EtaPair (A B : Type) := eta_pair { eta_fst : A; eta_snd : B }.
Example unit_like_under_record_eta (A : Type) (p : EtaPair A EtaUnit) :
  eta_pair A EtaUnit (eta_fst A EtaUnit p) eta_unit = p.
Proof. exact (eq_refl p). Qed.
