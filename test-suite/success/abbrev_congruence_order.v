Set Kernel Conversion Dep Heuristic.

Fixpoint expensive (n : nat) : nat :=
  match n with
  | O => O
  | S k => match expensive k with O => expensive k | S _ => O end
  end.

(* A recursive definition with a constructor argument is not necessarily a
   primitive recursor. Prefer its alias over evaluating the recursive call.
   Keep this in both directions, independently of the default tie-breaker. *)
Definition expensive_alias n := expensive n.
Goal expensive 26 = expensive_alias 26.
Proof.
  exact_no_check (eq_refl (expensive 26)).
  Timeout 5 Qed.
Goal expensive_alias 26 = expensive 26.
Proof.
  exact_no_check (eq_refl (expensive_alias 26)).
  Timeout 5 Qed.

(* Lean's abbreviation hint is mapped to Expand. Its branch arguments are
   not compared before exposing the recursor's actual computation. *)
Definition abbrev_rec (n zero : nat) (step : nat -> nat -> nat) : nat :=
  nat_rect (fun _ => nat) zero step n.
Strategy expand [abbrev_rec].
(* Keep nat_rect at its ordinary priority. It represents the additional
   definition layer around a primitive recursor in the Rocq translation. *)

Goal abbrev_rec 0 7 (fun _ _ => expensive 26) =
     abbrev_rec 0 7 (fun _ _ => expensive 27).
Proof.
  exact_no_check (eq_refl (abbrev_rec 0 7 (fun _ _ => expensive 26))).
  Timeout 5 Qed.

Goal abbrev_rec 0 7 (fun _ _ => expensive 27) =
     abbrev_rec 0 7 (fun _ _ => expensive 26).
Proof.
  exact_no_check (eq_refl (abbrev_rec 0 7 (fun _ _ => expensive 27))).
  Timeout 5 Qed.

(* Reducing an abbreviation must still reject different returned values. *)
Goal abbrev_rec 0 7 (fun _ _ => 0) = abbrev_rec 0 8 (fun _ _ => 0).
Proof. exact_no_check (eq_refl 7). Fail Qed. Abort.

(* An ordinary eliminator, including a parameterized one, has the same
   constructor demand. No Expand hint is supplied for these definitions. *)
Definition ordinary_rec (A : Type) (zero : A) (step : nat -> A -> A) :=
  fix go (n : nat) : A :=
    match n with O => zero | S k => step k (go k) end.

Goal ordinary_rec nat 7 (fun _ _ => expensive 26) 0 =
     ordinary_rec nat 7 (fun _ _ => expensive 27) 0.
Proof.
  exact_no_check (eq_refl (ordinary_rec nat 7 (fun _ _ => expensive 26) 0)).
  Timeout 5 Qed.

(* The visible constructor can have arguments; the selected branch ignores
   the recursive result and hence the expensive zero branch. *)
Goal ordinary_rec nat (expensive 26) (fun _ _ => 7) 1 =
     ordinary_rec nat (expensive 27) (fun _ _ => 7) 1.
Proof.
  exact_no_check (eq_refl (ordinary_rec nat (expensive 26) (fun _ _ => 7) 1)).
  Timeout 5 Qed.

(* A neutral structural argument cannot be assumed to select either branch. *)
Goal forall n, ordinary_rec nat 7 (fun _ _ => 0) n =
               ordinary_rec nat 8 (fun _ _ => 0) n.
Proof. intro n. exact_no_check (eq_refl 7). Fail Qed. Abort.

(* Nonrecursive recursors have a Case body rather than a Fix body. Their
   unselected branches must not be compared before the constructor selects. *)
Definition ordinary_case (A : Type) (yes no : A) (b : bool) :=
  match b with true => yes | false => no end.

Fixpoint small_eq (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n, S m => small_eq n m
  | _, _ => false
  end.
Goal ordinary_case nat 7 (expensive 26) (small_eq 2 2) =
     ordinary_case nat 7 (expensive 27) (small_eq 2 2).
Proof.
  exact_no_check (eq_refl (ordinary_case nat 7 (expensive 26) (small_eq 2 2))).
  Timeout 5 Qed.

(* A primitive projection can hide the constructor selecting a recursor
   branch. Both the recursive and nonrecursive forms must expose that major
   before comparing branch functions which its value will discard. *)
Set Primitive Projections.
Record major_source := { major_nat : nat; major_bool : bool }.
Unset Primitive Projections.
Definition selected_major := {| major_nat := 0; major_bool := true |}.
Goal ordinary_rec nat 7 (fun _ _ => expensive 26) (major_nat selected_major) =
     ordinary_rec nat 7 (fun _ _ => expensive 27) (major_nat selected_major).
Proof.
  exact_no_check (eq_refl (ordinary_rec nat 7 (fun _ _ => expensive 26) (major_nat selected_major))).
  Timeout 5 Qed.
Goal ordinary_case nat 7 (expensive 26) (major_bool selected_major) =
     ordinary_case nat 7 (expensive 27) (major_bool selected_major).
Proof.
  exact_no_check (eq_refl (ordinary_case nat 7 (expensive 26) (major_bool selected_major))).
  Timeout 5 Qed.
(* A tactic-level Opaque hint on a Definition does not make its body opaque
   to final kernel checking. A Qed body is the relevant negative control. *)
Definition hidden_major : major_source.
Proof. exact selected_major. Qed.
Goal ordinary_case nat 7 8 (major_bool hidden_major) = 7.
Proof. exact_no_check (eq_refl 7). Fail Qed. Abort.

Goal forall n, ordinary_case nat n (expensive 26) (major_bool selected_major) = n.
Proof. intro n. exact_no_check (eq_refl n). Timeout 5 Qed.
Goal forall source, ordinary_case nat 7 8 (major_bool source) = 7.
Proof. intro source. exact_no_check (eq_refl 7). Fail Qed. Abort.
Goal ordinary_case nat 7 8 (major_bool selected_major) = 8.
Proof. exact_no_check (eq_refl 8). Fail Qed. Abort.

(* Keep both heads eliminator-headed to exercise major publication itself. *)
Goal ordinary_case nat 7 8 (major_bool hidden_major) =
     ordinary_case nat 7 9 (major_bool hidden_major).
Proof.
  exact_no_check (eq_refl (ordinary_case nat 7 8 (major_bool hidden_major))).
  Fail Qed. Abort.
Goal forall source, ordinary_case nat 7 8 (major_bool source) =
                    ordinary_case nat 7 9 (major_bool source).
Proof.
  intro source. exact_no_check (eq_refl (ordinary_case nat 7 8 (major_bool source))).
  Fail Qed. Abort.
Goal ordinary_case nat 7 8 (major_bool selected_major) =
     ordinary_case nat 9 8 (major_bool selected_major).
Proof.
  exact_no_check (eq_refl (ordinary_case nat 7 8 (major_bool selected_major))).
  Fail Qed. Abort.

Definition next_major n := {| major_nat := S n; major_bool := true |}.
Goal forall x,
  ordinary_rec nat (expensive 26) (fun k _ => k) (major_nat (next_major x)) =
  ordinary_rec nat (expensive 27) (fun k _ => k) (major_nat (next_major x)).
Proof.
  intro x.
  exact_no_check (eq_refl (ordinary_rec nat (expensive 26) (fun k _ => k) (major_nat (next_major x)))).
  Timeout 5 Qed.
Goal forall x y,
  ordinary_rec nat 0 (fun k _ => k) (major_nat (next_major x)) =
  ordinary_rec nat 0 (fun k _ => k) (major_nat (next_major y)).
Proof.
  intros x y.
  exact_no_check (eq_refl (ordinary_rec nat 0 (fun k _ => k) (major_nat (next_major x)))).
  Fail Qed. Abort.

Goal forall x : nat, True.
Proof.
  intro x.
  exact_no_check
    (let source := next_major x in let alias := source in
     let witness := fun y : nat =>
       (eq_refl (ordinary_rec nat (expensive 1) (fun k _ => k) (major_nat alias)) :
         ordinary_rec nat (expensive 1) (fun k _ => k) (major_nat alias) =
         ordinary_rec nat (expensive 2) (fun k _ => k) (major_nat alias)) in I).
  Timeout 5 Qed.

Goal ordinary_case nat 7 (expensive 26) true =
     ordinary_case nat 7 (expensive 27) true.
Proof.
  exact_no_check (eq_refl (ordinary_case nat 7 (expensive 26) true)).
  Timeout 5 Qed.

Goal ordinary_case nat (expensive 26) 7 false =
     ordinary_case nat (expensive 27) 7 false.
Proof.
  exact_no_check (eq_refl (ordinary_case nat (expensive 26) 7 false)).
  Timeout 5 Qed.

(* Kernel checking of these casts takes place under actual LocalDef entries,
   including an alias in the smaller context of the second definition. *)
Goal True.
Proof.
  assert (True) as unused.
  { exact_no_check
      (let b := true in let alias := b in
       let witness := (eq_refl (ordinary_case nat 7 (expensive 1) alias) :
         ordinary_case nat 7 (expensive 1) alias =
         ordinary_case nat 7 (expensive 2) alias) in I).
  }
  exact I.
  Timeout 5 Qed.

Goal True.
Proof.
  exact_no_check
    (let n := 0 in let alias := n in
     let witness := (eq_refl (ordinary_rec nat 7 (fun _ _ => expensive 1) alias) :
       ordinary_rec nat 7 (fun _ _ => expensive 1) alias =
       ordinary_rec nat 7 (fun _ _ => expensive 2) alias) in I).
  Timeout 5 Qed.

Goal forall b, ordinary_case nat 7 0 b = ordinary_case nat 8 0 b.
Proof. intro b. exact_no_check (eq_refl 7). Fail Qed. Abort.

Goal ordinary_case nat 7 0 true = ordinary_case nat 8 0 true.
Proof. exact_no_check (eq_refl 7). Fail Qed. Abort.

(* Partial applications still use ordinary congruence/eta, not a guessed
   structural argument position. *)
Definition seven_alias := 7.
Goal ordinary_rec nat seven_alias (fun _ _ => 0) =
     ordinary_rec nat 7 (fun _ _ => 0).
Proof.
  exact_no_check (eq_refl (ordinary_rec nat 7 (fun _ _ => 0))).
  Timeout 5 Qed.

(* Ordinary congruence remains available when the definition is opaque. *)
Opaque abbrev_rec.
Definition zero_alias := 0.
Goal abbrev_rec zero_alias 7 (fun _ _ => 0) =
     abbrev_rec 0 7 (fun _ _ => 0).
Proof.
  exact_no_check (eq_refl (abbrev_rec 0 7 (fun _ _ => 0))).
  Timeout 5 Qed.
