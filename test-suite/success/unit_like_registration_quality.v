Set Universe Polymorphism.
Set Kernel Conversion Dep Heuristic.

(* Unknown relevance is not a certificate of irrelevance at every instance. *)
Inductive QBox@{s;u|} (A : Type@{s;u}) := qbox (_ : A).
Fail Register QBox as kernel.unit_like.

Goal forall (x y : QBox nat), x = y.
Proof. intros x y. exact_no_check (eq_refl x). Fail Qed. Abort.

(* Ordinary universe polymorphism and definitely irrelevant fields are safe. *)
Inductive EmptyFields@{u} : Type@{u} := empty_fields.
Register EmptyFields as kernel.unit_like.
Inductive ProofFields (P : SProp) : Type := proof_fields (_ : P).
Register ProofFields as kernel.unit_like.
Goal forall P (x y : ProofFields P), x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Qed.
