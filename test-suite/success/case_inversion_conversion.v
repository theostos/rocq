Set Kernel Conversion Dep Heuristic.
Set Definitional UIP.
Set Primitive Projections.
Set Universe Polymorphism.

Inductive IEq {A : Type} (x : A) : A -> SProp := irefl : IEq x x.
Definition itransport {A : Type} (P : A -> Type) {x y}
    (e : IEq x y) (v : P x) : P y :=
  match e with irefl _ => v end.

(* Inversion compares instantiated motive types, not the indices alone.
   Constant and non-injective motives must continue reducing. *)
Goal forall A B (x y : A) (e : IEq x y) (v : B),
  itransport (fun _ => B) e v = v.
Proof. intros. exact_no_check (eq_refl v). Qed.

Goal forall A (P : A -> Type) x (e : IEq x x) (v : P x),
  itransport P e v = v.
Proof. intros. exact_no_check (eq_refl v). Qed.

Definition repeat_family (n : nat) : Type :=
  match n with O => nat | S _ => bool end.
Goal forall n m (e : IEq (S n) (S m)) (v : bool),
  itransport repeat_family e v = v.
Proof. intros. exact_no_check (eq_refl v). Qed.

(* Universes and freshly crossed binders remain part of the comparison. *)
Goal forall A (P : A -> Type),
  (fun x (e : IEq x x) (v : P x) => itransport P e v) =
  (fun x (_ : IEq x x) (v : P x) => v).
Proof. intros. exact_no_check (eq_refl (fun x (_ : IEq x x) (v : P x) => v)). Qed.

Record IndexedBox (n : nat) : Type := indexed_box { datum : nat }.

(* A failed/inconclusive inversion is NOT permission to remove a cast.
   These terms have the same result type, but the cast remains blocked. *)
Goal forall n m (e : IEq n m) (v : IndexedBox n),
  datum m (itransport IndexedBox e v) = datum n v.
Proof. intros. exact_no_check (eq_refl (datum n v)). Fail Qed. Abort.

Goal forall n m (e : IEq n m) (v : IndexedBox n),
  datum n v = datum m (itransport IndexedBox e v).
Proof. intros. exact_no_check (eq_refl (datum n v)). Fail Qed. Abort.

(* A successful inversion never discards a relevant field. *)
Goal forall n (e : IEq n n) (v : IndexedBox n),
  datum n (itransport IndexedBox e v) = S (datum n v).
Proof. intros. exact_no_check (eq_refl (datum n v)). Fail Qed. Abort.
