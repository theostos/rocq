Inductive PNat := PZero | PSucc : PNat -> PNat.
Register PNat as kernel.ind_peano_nat.
Fixpoint pdouble n :=
  match n with PZero => PZero | PSucc n => PSucc (PSucc (pdouble n)) end.
Register pdouble as kernel.peano_nat_double.
Fixpoint padd n m :=
  match m with PZero => n | PSucc m => PSucc (padd n m) end.
Register padd as kernel.peano_nat_add.

(* The inner let allocates a reducible, shared function closure. Its update
   frame must not be populated with the result of its first application. *)
Definition two_calls := Eval lazy in
  (let f := (let ignored := PZero in padd) in
   (f PZero PZero, f (PSucc PZero) PZero)).
Example shared_calls : two_calls = (PZero, PSucc PZero) := eq_refl.

Definition partial_calls := Eval lazy in
  (let f := (let ignored := PZero in padd PZero) in
   (f PZero, f (PSucc PZero))).
Example shared_partial_calls : partial_calls = (PZero, PSucc PZero) := eq_refl.
