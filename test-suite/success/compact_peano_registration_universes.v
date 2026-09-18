Inductive PNat := PZero | PSucc : PNat -> PNat.
Register PNat as kernel.ind_peano_nat.
Fixpoint pdouble n :=
  match n with PZero => PZero | PSucc n => PSucc (PSucc (pdouble n)) end.

(* An unused abstract universe is absent from the displayed function type,
   but the constant still cannot be quoted at an empty universe instance. *)
Polymorphic Definition phantom_double@{u} := pdouble.
Fail Register phantom_double as kernel.peano_nat_double.
Register pdouble as kernel.peano_nat_double.

Fixpoint padd n m :=
  match m with PZero => n | PSucc m => PSucc (padd n m) end.
Polymorphic Definition phantom_add@{u} := padd.
Fail Register phantom_add as kernel.peano_nat_add.
Register padd as kernel.peano_nat_add.
