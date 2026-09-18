Set Kernel Conversion Dep Heuristic.

Inductive PNat := PZero | PSucc : PNat -> PNat.
Register PNat as kernel.ind_peano_nat.
Inductive ProofArg : SProp := proof_a | proof_b.
Definition proof_id (proof : ProofArg) : ProofArg := proof.

(* Compatibility control: the proof argument is inside the prefix, before the
   peeled last argument. This case also passes without the erased-proof fix. *)
Definition ProofTail (_ : PNat) := ProofArg -> nat -> nat.
Fixpoint choose (n : PNat) (x : nat) {struct n} : ProofTail n :=
  match n with
  | PZero => fun _ last => last
  | PSucc k => fun proof last => choose k x proof last
  end.

Goal choose (PSucc PZero) 0 (proof_id proof_a) 7 =
     choose (PSucc PZero) 1 (proof_id proof_b) 7.
Proof.
  exact_no_check (eq_refl (choose (PSucc PZero) 0 (proof_id proof_a) 7)).
  Timeout 5 Qed.

Goal choose (PSucc PZero) 1 (proof_id proof_b) 7 =
     choose (PSucc PZero) 0 (proof_id proof_a) 7.
Proof.
  exact_no_check (eq_refl (choose (PSucc PZero) 1 (proof_id proof_b) 7)).
  Timeout 5 Qed.

Goal choose (PSucc PZero) 0 (proof_id proof_a) 7 =
     choose (PSucc PZero) 1 (proof_id proof_b) 8.
Proof.
  exact_no_check (eq_refl (choose (PSucc PZero) 0 (proof_id proof_a) 7)).
  Fail Qed.
Abort.
