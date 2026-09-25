From Corelib Require Import BinNums.
From Stdlib Require Import NArith.

Set Primitive Projections.

(* Registration checks the shape of the type and the computation rules. *)
Inductive BadNat := BadZero | BadSucc : BadNat -> BadNat | BadExtra.
Fail Register BadNat as kernel.ind_peano_nat.

Inductive IrrelevantNat : SProp :=
| IrrelevantZero
| IrrelevantSucc : IrrelevantNat -> IrrelevantNat.
Fail Register IrrelevantNat as kernel.ind_peano_nat.

Inductive PNat := PZero | PSucc : PNat -> PNat.
Register PNat as kernel.ind_peano_nat.

Definition bad_double (_ : PNat) := PZero.
Fail Register bad_double as kernel.peano_nat_double.

Fixpoint pdouble n :=
  match n with
  | PZero => PZero
  | PSucc n => PSucc (PSucc (pdouble n))
  end.
Register pdouble as kernel.peano_nat_double.

Lemma opaque_double : PNat -> PNat.
Proof. exact pdouble. Qed.
Fail Register opaque_double as kernel.peano_nat_double.

Definition bad_add (_ _ : PNat) := PZero.
Fail Register bad_add as kernel.peano_nat_add.

Fixpoint padd n m :=
  match m with
  | PZero => n
  | PSucc m => PSucc (padd n m)
  end.
Register padd as kernel.peano_nat_add.

Definition ppred n :=
  match n with
  | PZero => PZero
  | PSucc n => n
  end.

Definition bad_sub (n _ : PNat) := n.
Fail Register bad_sub as kernel.peano_nat_sub.

Fixpoint psub n m :=
  match m with
  | PZero => n
  | PSucc m => ppred (psub n m)
  end.
Register psub as kernel.peano_nat_sub.

Fixpoint pmul n m :=
  match m with
  | PZero => PZero
  | PSucc m => padd (pmul n m) n
  end.
Register pmul as kernel.peano_nat_mul.

Definition bad_pow (_ _ : PNat) := PZero.
Fail Register bad_pow as kernel.peano_nat_pow.

Fixpoint ppow n m :=
  match m with
  | PZero => PSucc PZero
  | PSucc m => pmul (ppow n m) n
  end.
Register ppow as kernel.peano_nat_pow.

Fixpoint decode_pos p :=
  match p with
  | xH => PSucc PZero
  | xO p => pdouble (decode_pos p)
  | xI p => PSucc (pdouble (decode_pos p))
  end.

Definition decode_N n :=
  match n with
  | N0 => PZero
  | Npos p => decode_pos p
  end.
Register decode_N as kernel.peano_nat_of_N.

Inductive PBool := PFalse | PTrue.
Definition bad_beq (_ _ : PNat) := PTrue.
Fail Register bad_beq as kernel.peano_nat_beq.

Fixpoint pbeq n m :=
  match n, m with
  | PZero, PZero => PTrue
  | PSucc n, PSucc m => pbeq n m
  | _, _ => PFalse
  end.
Register pbeq as kernel.peano_nat_beq.

Definition bad_ble (_ _ : PNat) := PTrue.
Fail Register bad_ble as kernel.peano_nat_ble.

Fixpoint pble n m :=
  match n, m with
  | PZero, _ => PTrue
  | PSucc _, PZero => PFalse
  | PSucc n, PSucc m => pble n m
  end.
Register pble as kernel.peano_nat_ble.

Definition bad_fueled_worker (_ _ _ : PNat) := PZero.
Fail Register bad_fueled_worker as kernel.peano_nat_div_go.

(* Registered operations compute on compact values. *)
Definition huge := decode_N 1208925819614629174706176%N.

Example huge_pow_equal : ppow (PSucc (PSucc PZero)) (decode_N 80%N) = huge.
Proof. reflexivity. Qed.

Example subtraction_borrow :
  psub (decode_N 16%N) (decode_N 9%N) = decode_N 7%N.
Proof. reflexivity. Qed.

Example huge_truncated_subtraction : psub (decode_N 32%N) huge = PZero.
Proof. reflexivity. Qed.

Example huge_beq : pbeq huge huge = PTrue.
Proof. reflexivity. Qed.

Example huge_successor : pble huge (PSucc huge) = PTrue.
Proof. reflexivity. Qed.

(* Closed arguments hidden behind transparent computation are reduced before
   falling back to unary recursion. *)
Record PBox := { unbox : PNat }.
Definition wrapped n := unbox {| unbox := n |}.

Example wrapped_huge_pow_equal :
  ppow (wrapped (PSucc (PSucc PZero))) (wrapped (decode_N 80%N)) = huge.
Proof. reflexivity. Qed.

Example wrapped_huge_add :
  padd (wrapped huge) (wrapped huge) = decode_N 2417851639229258349412352%N.
Proof. reflexivity. Qed.

(* A compact value under a closed wrapper. *)
Inductive PInt :=
| POfNat : PNat -> PInt
| PNegSucc : PNat -> PInt.

Definition pint_pow value exponent :=
  match value with
  | POfNat n => POfNat (ppow n exponent)
  | PNegSucc n => PNegSucc (ppow (PSucc n) exponent)
  end.

Definition pint_mul left right :=
  match left, right with
  | POfNat n, POfNat m => POfNat (pmul n m)
  | POfNat n, PNegSucc m => PNegSucc (pmul n (PSucc m))
  | PNegSucc n, POfNat m => PNegSucc (pmul (PSucc n) m)
  | PNegSucc n, PNegSucc m => POfNat (pmul (PSucc n) (PSucc m))
  end.

Strategy 1 [pint_pow].

Example compact_peano_under_closed_wrapper :
  pint_pow (POfNat (decode_N 2%N)) (decode_N 80%N) =
  pint_mul (POfNat (decode_N 2%N)) (pint_pow (POfNat (decode_N 2%N)) (decode_N 79%N)).
Proof. reflexivity. Qed.

(* Elimination sees a constructor view of a compact value. *)
Definition bool_motive b :=
  match b with
  | PFalse => False
  | PTrue => True
  end.

Example dependent_bool : bool_motive (pble huge huge).
Proof. exact I. Qed.

Definition nat_motive n :=
  match n with
  | PZero => False
  | PSucc pred => pble pred pred = PTrue
  end.

Definition dependent_nat : nat_motive huge := eq_refl PTrue.

(* Open arguments follow the ordinary computation rules. *)
Example open_computation (n : PNat) : pble PZero n = PTrue.
Proof. reflexivity. Qed.

(* Equal registered operations compare their arguments before unfolding. *)
Example mixed_compact_open_congruence (n : PNat) :
  pble huge n = pble (ppow (PSucc (PSucc PZero)) (decode_N 80%N)) n.
Proof. reflexivity. Qed.

Fail Definition demanded_open_computation (n : PNat) :
  pble n PZero = PFalse := eq_refl PFalse.
