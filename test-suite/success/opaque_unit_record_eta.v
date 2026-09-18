Set Kernel Conversion Dep Heuristic.
Set Primitive Projections.

Inductive Token := token.
Register Token as kernel.unit_like.
Record WithUnit := pack { token_field : Token; data : nat }.

(* Genuine kernel opacity: eta may inspect the record's projections, but
   must not unfold [sealed] to discover the value of its relevant field. *)
Definition sealed (n : nat) : WithUnit.
Proof. exact (pack token n). Qed.

Goal forall n u, sealed n = pack u (data (sealed n)).
Proof. intros n u; exact_no_check (eq_refl (sealed n)). Timeout 5 Qed.
Goal forall n u, pack u (data (sealed n)) = sealed n.
Proof. intros n u; exact_no_check (eq_refl (sealed n)). Timeout 5 Qed.

Goal forall n u, sealed n = pack u (S (data (sealed n))).
Proof. intros n u; exact_no_check (eq_refl (sealed n)). Fail Qed. Abort.
Goal forall n u, pack u (S (data (sealed n))) = sealed n.
Proof. intros n u; exact_no_check (eq_refl (sealed n)). Fail Qed. Abort.
Goal forall n, data (sealed n) = n.
Proof. intro n; exact_no_check (eq_refl n). Fail Qed. Abort.

Section Stuck.
Variable n : nat.
Variables left right : WithUnit.
Variable u : Token.
Local Definition picked := match n with O => left | S _ => right end.

(* Unfolding this local definition cannot decide the match. Late record eta
   must still identify its unit field without discarding the [nat] field. *)
Goal picked = pack u (data picked).
Proof. exact_no_check (eq_refl picked). Timeout 5 Qed.
Goal pack u (data picked) = picked.
Proof. exact_no_check (eq_refl picked). Timeout 5 Qed.

Goal picked = pack u (S (data picked)).
Proof. exact_no_check (eq_refl picked). Fail Qed. Abort.
Goal pack u (S (data picked)) = picked.
Proof. exact_no_check (eq_refl picked). Fail Qed. Abort.
End Stuck.
