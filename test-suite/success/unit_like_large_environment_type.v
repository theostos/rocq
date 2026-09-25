Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.
Set Definitional UIP.

Record ProofBox (P : SProp) : Type := proof_box { proof_value : P }.
Register ProofBox as kernel.unit_like.
Record Container (D : Type) (P : SProp) : Type := container {
  data : nat;
  certificate : ProofBox P
}.
Record Pair (A B : Type) := pair { first : A; second : B }.

(* Exceed the expanded quotation allowance with a small shared syntax DAG.
   Keep the type inline: a constant alias would hide its size from quotation. *)
Ltac large_type A :=
  let rec build n T :=
    lazymatch n with
    | O => exact T
    | S ?m => let T' := constr:(Pair T T) in build m T'
    end in
  build 11 A.

(* An application argument is checked under actual local declarations.
   Their stored types live below those declarations, unlike closures for
   binders introduced during conversion. Rebase environment indices first. *)
Definition large_projected_type :=
  fun (A : Type) (P : SProp) (q : P)
      (x : Container ltac:(large_type A) P) =>
    @id (certificate _ _ x = proof_box P q) (eq_refl (proof_box P q)).

Definition large_projected_type_under_binder :=
  fun (A : Type) (P : nat -> SProp) (q : forall n, P n)
      (x : forall n, Container ltac:(large_type A) (P n)) =>
    @id ((fun n => certificate _ _ (x n)) = (fun n => proof_box (P n) (q n)))
      (eq_refl (fun n => proof_box (P n) (q n))).

(* The corrected witness must retain the instantiated proposition and
   relevant fields, even in the same large surrounding context. *)
Fail Definition different_proposition :=
  fun (A : Type) (P Q : SProp) (q : Q)
      (x : Container ltac:(large_type A) P) =>
    @id (certificate _ _ x = certificate _ _ x) (eq_refl (proof_box Q q)).
Fail Definition relevant_field :=
  fun (A : Type) (P : SProp) (x : Container ltac:(large_type A) P) =>
    @id (data _ _ x = 0) (eq_refl 0).
