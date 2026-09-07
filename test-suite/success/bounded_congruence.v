From Corelib Require Import BinNums.
From Stdlib Require Import NArith.BinNat.
Set Kernel Conversion Dep Heuristic.

Inductive PNat := PZero | PSucc : PNat -> PNat.
Register PNat as kernel.ind_peano_nat.
Fixpoint double n :=
  match n with PZero => PZero | PSucc n => PSucc (PSucc (double n)) end.
Register double as kernel.peano_nat_double.
Fixpoint decode_pos p :=
  match p with
  | xH => PSucc PZero
  | xO p => double (decode_pos p)
  | xI p => PSucc (double (decode_pos p))
  end.
Definition decode_N n := match n with N0 => PZero | Npos p => decode_pos p end.
Register decode_N as kernel.peano_nat_of_N.
Inductive PBool := PFalse | PTrue.
Fixpoint ble n m :=
  match n, m with
  | PZero, _ => PTrue
  | PSucc _, PZero => PFalse
  | PSucc n, PSucc m => ble n m
  end.
Register ble as kernel.peano_nat_ble.

Definition choose width fuel :=
  (fix go n := match n with
   | PZero => PFalse
   | PSucc k => match ble width k with PTrue => PTrue | PFalse => go k end
   end) fuel.
Definition large := decode_N 4294967296%N.
Definition larger := decode_N 18446744073709551616%N.

(* Both applications reduce to PFalse. Comparing their function prefixes
   instead unfolds huge recursions in branches that are not taken. *)
Goal choose large (PSucc PZero) = choose larger (PSucc PZero).
Proof. exact_no_check (eq_refl (choose large (PSucc PZero))). Timeout 5 Qed.

Goal choose larger (PSucc PZero) = choose large (PSucc PZero).
Proof. exact_no_check (eq_refl (choose large (PSucc PZero))). Timeout 5 Qed.

Goal (fun _ : nat => choose large (PSucc PZero)) =
     (fun _ : nat => choose larger (PSucc PZero)).
Proof.
  exact_no_check (eq_refl (fun _ : nat => choose large (PSucc PZero))).
  Timeout 5 Qed.

(* Exhausting a probe must not accept a wrong result. *)
Goal choose large (PSucc PZero) = PTrue.
Proof. exact_no_check (eq_refl PTrue). Fail Qed. Abort.
Goal choose large (PSucc PZero) = choose PZero (PSucc PZero).
Proof. exact_no_check (eq_refl (choose large (PSucc PZero))). Fail Qed. Abort.

Definition sealed (x : PBool) : PBool.
Proof. exact x. Qed.
Goal sealed (choose large (PSucc PZero)) = choose larger (PSucc PZero).
Proof. exact_no_check (eq_refl (choose larger (PSucc PZero))). Fail Qed. Abort.

(* These heads cannot unfold. Their argument comparison must be allowed to
   exceed the speculative budget: congruence is the only available path. *)
Definition truth := true.
Fixpoint copies_left (n : nat) : list bool :=
  match n with O => nil | S k => cons true (copies_left k) end.
Fixpoint copies_right (n : nat) : list bool :=
  match n with O => nil | S k => cons truth (copies_right k) end.
Definition seal_list (xs : list bool) : list bool.
Proof. exact xs. Qed.
Goal seal_list (copies_left 600) = seal_list (copies_right 600).
Proof. exact_no_check (eq_refl (seal_list (copies_left 600))). Timeout 5 Qed.
Goal forall f : list bool -> list bool,
  f (copies_left 600) = f (copies_right 600).
Proof. intro f; exact_no_check (eq_refl (f (copies_left 600))). Timeout 5 Qed.
