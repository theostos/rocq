Set Primitive Projections.
Record Box := box { value : nat }.
Inductive Plain := plain (payload : nat).
Definition payload (x : Plain) := match x with plain n => n end.

Section Stuck.
Variable n : nat.
Variables left right : Box.
Local Abbreviation pick := (match n with O => left | S _ => right end).
Local Abbreviation pick_fix :=
  ((fix loop (n : nat) : Box :=
     match n with O => left | S k => loop k end) n).

(* These computations are stuck on [n]. Its type is [nat], while the whole
   elimination has record type. A shallow head-type probe cannot establish it. *)
Goal pick = box (value pick).
Proof. exact_no_check (eq_refl pick). Timeout 5 Qed.
Goal box (value pick) = pick.
Proof. exact_no_check (eq_refl pick). Timeout 5 Qed.
Goal pick_fix = box (value pick_fix).
Proof. exact_no_check (eq_refl pick_fix). Timeout 5 Qed.
Goal box (value pick_fix) = pick_fix.
Proof. exact_no_check (eq_refl pick_fix). Timeout 5 Qed.

(* Ordinary eta still compares fields and does not apply to plain inductives. *)
Goal pick = box (S (value pick)).
Proof. exact_no_check (eq_refl pick). Fail Qed. Abort.
Variable opaque_plain : Plain.
Goal opaque_plain = plain (payload opaque_plain).
Proof. exact_no_check (eq_refl opaque_plain). Fail Qed. Abort.
End Stuck.
