Set Kernel Conversion Dep Heuristic.

Inductive PNat := PZero | PSucc : PNat -> PNat.
Register PNat as kernel.ind_peano_nat.
Fixpoint double n :=
  match n with PZero => PZero | PSucc k => PSucc (PSucc (double k)) end.
Register double as kernel.peano_nat_double.

Inductive ProofArg : SProp := proof_a | proof_b.
Definition proof_id (proof : ProofArg) : ProofArg := proof.
Notation proof_left := (proof_id proof_a).
Notation proof_right := (proof_id proof_b).

(* Hiding the final binder behind an alias allows the ordinary comparison to
   erase a shared proof application before the optional congruence probe copies
   it. Bare proof constructors do not reproduce that shared-closure mutation. *)
Definition ProofTail (_ : PNat) := ProofArg -> nat.
Fixpoint choose (n : PNat) (x : nat) {struct n} : ProofTail n :=
  match n with
  | PZero => fun _ => 0
  | PSucc k => fun proof => choose k x proof
  end.

Goal choose (PSucc PZero) 0 proof_left = choose (PSucc PZero) 1 proof_right.
Proof. exact_no_check (eq_refl (choose (PSucc PZero) 0 proof_left)). Timeout 5 Qed.

Goal choose (double (PSucc PZero)) 0 proof_left =
     choose (double (PSucc PZero)) 1 proof_right.
Proof.
  exact_no_check (eq_refl (choose (double (PSucc PZero)) 0 proof_left)).
  Timeout 5 Qed.

Goal choose (PSucc PZero) 1 proof_right = choose (PSucc PZero) 0 proof_left.
Proof. exact_no_check (eq_refl (choose (PSucc PZero) 1 proof_right)). Timeout 5 Qed.

(* Also exercise copying an argument/prefix containing an erased proof. *)
Record Tagged := tag { number : nat; valid : ProofArg }.
Fixpoint ignore_tag (n : PNat) (value : Tagged) : nat :=
  match n with PZero => 0 | PSucc k => ignore_tag k value end.

Goal ignore_tag (PSucc PZero) (tag 0 proof_left) =
     ignore_tag (PSucc PZero) (tag 1 proof_right).
Proof.
  exact_no_check (eq_refl (ignore_tag (PSucc PZero) (tag 0 proof_left))).
  Timeout 5 Qed.

Fixpoint ignore_tag_prefix (n : PNat) (value : Tagged) (last : nat) : nat :=
  match n with PZero => last | PSucc k => ignore_tag_prefix k value last end.

Goal ignore_tag_prefix (PSucc PZero) (tag 0 proof_left) 7 =
     ignore_tag_prefix (PSucc PZero) (tag 1 proof_right) 7.
Proof.
  exact_no_check (eq_refl (ignore_tag_prefix (PSucc PZero) (tag 0 proof_left) 7)).
  Timeout 5 Qed.

(* Falling back must not make unequal relevant data convertible. *)
Goal ignore_tag_prefix (PSucc PZero) (tag 0 proof_left) 7 =
     ignore_tag_prefix (PSucc PZero) (tag 1 proof_right) 8.
Proof.
  exact_no_check (eq_refl (ignore_tag_prefix (PSucc PZero) (tag 0 proof_left) 7)).
  Fail Qed.
Abort.

Fixpoint read_tag (n : PNat) (value : Tagged) : nat :=
  match n with PZero => number value | PSucc k => read_tag k value end.

Goal read_tag (PSucc PZero) (tag 0 proof_left) =
     read_tag (PSucc PZero) (tag 1 proof_right).
Proof.
  exact_no_check (eq_refl (read_tag (PSucc PZero) (tag 0 proof_left))).
  Fail Qed.
Abort.
