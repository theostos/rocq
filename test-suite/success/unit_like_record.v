Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.

Record ProofBox (P : SProp) : Type := proof_box { proof_value : P }.
Register ProofBox as kernel.unit_like.
Record Box (A : Type) := box { value : A }.

(* The inner proof box is registered. The outer record is unit-like only at
   this parameter instantiation, by primitive-record eta. Check at Qed, not
   just in elaboration. This models Mathlib's ULift (PLift P) morphisms. *)
Goal forall (P : SProp) (x y : Box (ProofBox P)), x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Qed.
Goal forall (P : SProp) (f : nat -> Box (ProofBox P)) x y, f x = f y.
Proof. intros P f x y. exact_no_check (eq_refl (f x)). Qed.
Goal forall (P : SProp) (x y : Box (Box (ProofBox P))), x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Qed.

Record Several (P : SProp) := several {
  first : ProofBox P; second : Box (ProofBox P); third : P
}.
Goal forall (P : SProp) (x y : Several P), x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Qed.

Record Operation := operation { run : forall A : Type, nat -> Box A }.
Goal forall (P : SProp) (op : Operation) n (x : Box (ProofBox P)),
  run op (ProofBox P) n = x.
Proof. intros P op n x. exact_no_check (eq_refl x). Qed.

Definition sealed (P : SProp) (p : P) : Box (ProofBox P).
Proof. exact (box _ (proof_box P p)). Qed.
Goal forall (P : SProp) (p : P) (x : Box (ProofBox P)), sealed P p = x.
Proof. intros P p x. exact_no_check (eq_refl x). Qed.
Goal forall (P : SProp) (p : P) (x : Box (ProofBox P)), x = sealed P p.
Proof. intros P p x. exact_no_check (eq_refl x). Qed.

(* Relevant information, including an unknown parameter type, is retained. *)
Goal forall (x y : Box nat), x = y.
Proof. intros x y. exact_no_check (eq_refl x). Fail Qed. Abort.
Goal forall (A : Type) (x y : Box A), x = y.
Proof. intros A x y. exact_no_check (eq_refl x). Fail Qed. Abort.
Goal forall (f : nat -> Box nat) x y, f x = f y.
Proof. intros f x y. exact_no_check (eq_refl (f x)). Fail Qed. Abort.
Goal forall (op : Operation) n (x : Box nat), run op nat n = x.
Proof. intros op n x. exact_no_check (eq_refl x). Fail Qed. Abort.

Record Mixed (P : SProp) := mixed { proof_part : ProofBox P; number : nat }.
Goal forall (P : SProp) (x y : Mixed P), x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Fail Qed. Abort.

(* Do not infer unit-ness through a scrutinee-dependent projection type. *)
Inductive U := tt.
Register U as kernel.unit_like.
Record Dependent (family : U -> Type) := dependent {
  tag : U; payload : family tag
}.
Goal forall (family : U -> Type) (x y : Dependent family), x = y.
Proof. intros family x y. exact_no_check (eq_refl x). Fail Qed. Abort.

(* Having one constructor is not enough: the outer type needs record eta. *)
Inductive Plain (A : Type) := plain : A -> Plain A.
Goal forall (P : SProp) (x y : Plain (ProofBox P)), x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Fail Qed. Abort.

Definition Hidden (P : SProp) := Box (ProofBox P).
Opaque Hidden.
Goal forall (P : SProp) (x y : Hidden P), x = y.
Proof. intros P x y. exact_no_check (eq_refl x). Fail Qed. Abort.
