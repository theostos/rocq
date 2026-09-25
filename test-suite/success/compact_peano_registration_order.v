(* Closing this module replays dependent registrations into a fresh context. *)
Module FreshScheme.
Inductive PNat := PZero | PSucc : PNat -> PNat.
Register PNat as kernel.ind_peano_nat.
Fixpoint pdouble n :=
  match n with PZero => PZero | PSucc n => PSucc (PSucc (pdouble n)) end.
Register pdouble as kernel.peano_nat_double.
Fixpoint padd n m :=
  match m with PZero => n | PSucc m => PSucc (padd n m) end.
Register padd as kernel.peano_nat_add.
End FreshScheme.

Example reloaded_add :
  FreshScheme.padd FreshScheme.PZero (FreshScheme.PSucc FreshScheme.PZero) =
  FreshScheme.PSucc FreshScheme.PZero := eq_refl.
