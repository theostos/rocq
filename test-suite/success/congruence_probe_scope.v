Set Kernel Conversion Dep Heuristic.

Inductive PNat := PZero | PSucc : PNat -> PNat.
Register PNat as kernel.ind_peano_nat.
Fixpoint double n :=
  match n with PZero => PZero | PSucc n => PSucc (PSucc (double n)) end.
Register double as kernel.peano_nat_double.

Definition alias (x : nat) := x.
Fixpoint left (n : PNat) (x : nat) : nat :=
  match n with PZero => x | PSucc n => left n x end.
Fixpoint right (n : PNat) (x : nat) : nat :=
  match n with PZero => alias x | PSucc n => right n x end.

(* The kernel crosses the lambda binder before comparing the applications. *)
Goal (fun x => left (PSucc PZero) x) = (fun x => right (PSucc PZero) x).
Proof. exact_no_check (eq_refl (fun x => left (PSucc PZero) x)). Timeout 5 Qed.

Goal (fun x => right (PSucc PZero) x) = (fun x => left (PSucc PZero) x).
Proof. exact_no_check (eq_refl (fun x => left (PSucc PZero) x)). Timeout 5 Qed.

Goal (fun x y => left (PSucc PZero) x) = (fun x y : nat => right (PSucc PZero) y).
Proof. exact_no_check (eq_refl (fun x y : nat => left (PSucc PZero) x)). Fail Qed. Abort.

(* Eta comparison gives the two sides different lifts. *)
Goal (fun x => left (PSucc PZero) x) = right (PSucc PZero).
Proof. exact_no_check (eq_refl (right (PSucc PZero))). Timeout 5 Qed.
Goal right (PSucc PZero) = (fun x => left (PSucc PZero) x).
Proof. exact_no_check (eq_refl (right (PSucc PZero))). Timeout 5 Qed.

(* Keep external relatives distinct from newly crossed binders. *)
Definition outer_relative (outer : nat) :
  (fun inner : nat => left (PSucc PZero) outer) =
  (fun inner : nat => right (PSucc PZero) outer).
Proof.
  exact_no_check (eq_refl (fun inner : nat => left (PSucc PZero) outer)).
  Timeout 5 Qed.
Definition different_relatives (outer : nat) :
  (fun inner : nat => left (PSucc PZero) outer) =
  (fun inner : nat => right (PSucc PZero) inner).
Proof.
  exact_no_check (eq_refl (fun inner : nat => left (PSucc PZero) outer)).
  Fail Qed. Abort.

(* Fixpoint bodies introduce a recursive binder as well as lambda binders. *)
Definition walk_left := fix walk n :=
  match n with O => O | S k => left (PSucc PZero) (walk k) end.
Definition walk_right := fix walk n :=
  match n with O => O | S k => right (PSucc PZero) (walk k) end.
Goal walk_left = walk_right.
Proof. exact_no_check (eq_refl walk_left). Timeout 5 Qed.

Inductive ProofArg : SProp := proof_arg.
Goal (fun (_ : ProofArg) x => left (PSucc PZero) x) =
     (fun (_ : ProofArg) x => right (PSucc PZero) x).
Proof.
  exact_no_check (eq_refl (fun (_ : ProofArg) x => left (PSucc PZero) x)).
  Timeout 5 Qed.

Goal (forall x, left (PSucc PZero) x = x) =
     (forall x, right (PSucc PZero) x = x).
Proof.
  exact_no_check (eq_refl (forall x, left (PSucc PZero) x = x)).
  Timeout 5 Qed.
