Set Primitive Projections.
Inductive U := unit_value.
Register U as kernel.unit_like.
Record Pair (A B : Type) := pair { first : A; second : B }.

(* Same conversion as LawfulMonadStateOf.modify_eq, without the importer. *)
Definition projected_identity (A : Type) (z : Pair U A) :
  (fun k : U => k) = (fun _ : U => first U A z) := eq_refl _.
Definition projected_identity_reverse (A : Type) (z : Pair U A) :
  (fun _ : U => first U A z) = (fun k : U => k) := eq_refl _.
Definition two_projections (x y : Pair U nat) :
  first U nat x = first U nat y := eq_refl _.
Definition nested_projection (x : Pair (Pair U nat) nat) (u : U) :
  first U nat (first (Pair U nat) nat x) = u := eq_refl _.
Definition applied_projection (x : Pair (nat -> U) nat) (n : nat) (u : U) :
  first (nat -> U) nat x n = u := eq_refl _.
Definition local_projection (x : Pair U nat) (u : U) :
  let v := first U nat x in v = u := eq_refl _.
Definition UAlias := U.
Definition aliased_projection (x : Pair UAlias nat) (u : U) :
  first UAlias nat x = u := eq_refl _.
Record Operation := operation { run : forall A : Type, nat -> A }.
Definition instantiated_projection (x : Operation) (n : nat) (u : U) :
  run x U n = u := eq_refl _.

(* A unit field does not erase the other fields or their enclosing record. *)
Fail Definition wrong_nat_field (x y : Pair U nat) :
  second U nat x = second U nat y := eq_refl _.
Fail Definition wrong_record (x y : Pair U nat) : x = y := eq_refl _.
Fail Definition wrong_nat_projection (x : Pair nat nat) (n : nat) :
  first nat nat x = n := eq_refl _.
Fail Definition wrong_nat_function (x : Pair (nat -> nat) nat) (n : nat) :
  first (nat -> nat) nat x n = n := eq_refl _.
Fail Definition wrong_instantiation (x : Operation) (n : nat) :
  run x nat n = n := eq_refl _.
Fail Definition wrong_polymorphic_field (A : Type) (x y : Pair A U) :
  first A U x = first A U y := eq_refl _.

Record DepPair := dep_pair { field_type : Type; field_value : field_type }.
Fail Definition wrong_dependent_projection (x : DepPair) (v : field_type x) :
  field_value x = v := eq_refl _.

(* An irrelevant record parameter must not affect field instantiation. *)
Inductive ParameterProof : SProp := parameter_proof.
Record ErasedPair (A : Type) (p : ParameterProof) :=
  erased_pair { erased_field : A }.
Definition erased_unit_field (p : ParameterProof) (x : ErasedPair U p) (u : U) :
  erased_field U p x = u := eq_refl _.
Fail Definition wrong_erased_nat_field
    (p : ParameterProof) (x : ErasedPair nat p) (n : nat) :
  erased_field nat p x = n := eq_refl _.
