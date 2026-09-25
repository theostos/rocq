Set Kernel Conversion Dep Heuristic.
Inductive U := unit_value.
Register U as kernel.unit_like.
Inductive Shape := pure | arg (s : Shape) | except (s : Shape).
Fixpoint Conds (s : Shape) : Type :=
  match s with pure => U | arg t => Conds t | except t => (bool * Conds t)%type end.
Fixpoint combine (s : Shape) : Conds s -> Conds s -> Conds s :=
  match s return Conds s -> Conds s -> Conds s with
  | pure => fun _ _ => unit_value
  | arg t => combine t
  | except t => fun p q => (andb (fst p) (fst q), combine t (snd p) (snd q))
  end.

(* Like Std.Do.ExceptConds.and_eq_left: the local domain is a recursive
   family, not a syntactic singleton. Both comparison orientations matter. *)
Goal forall p q : Conds pure, p = combine pure p q.
Proof. intros p q. exact_no_check (eq_refl p). Qed.
Goal forall p q : Conds pure, combine pure p q = p.
Proof. intros p q. exact_no_check (eq_refl p). Qed.
Goal forall p q : Conds pure, p = q.
Proof. intros p q. exact_no_check (eq_refl p). Qed.
Goal forall p q : Conds (arg (arg pure)), p = combine (arg (arg pure)) p q.
Proof. intros p q. exact_no_check (eq_refl p). Qed.
Section Named.
  Variables p q : Conds (arg pure).
  Goal p = q.
  Proof. exact_no_check (eq_refl p). Qed.
  Goal unit_value = p.
  Proof. exact_no_check (eq_refl unit_value). Qed.
End Named.

Inductive ParamUnit (A : Type) := param_unit.
Register ParamUnit as kernel.unit_like.
Fixpoint Indexed (s : Shape) (A B : Type) : Type :=
  match s with pure => ParamUnit A | arg t => Indexed t A B | except _ => ParamUnit B end.
Goal forall A B (p q : Indexed (arg pure) A B), p = q.
Proof. intros A B p q. exact_no_check (eq_refl p). Qed.
Goal forall A B (p : Indexed (except pure) A B), p = param_unit B.
Proof. intros A B p. exact_no_check (eq_refl p). Qed.

(* Computing a type must not erase relevant fields, guess a neutral branch,
   or unfold an opaque family. Failed singleton inspection is inconclusive. *)
Goal forall p q : Conds (except pure), p = q.
Proof. intros p q. exact_no_check (eq_refl p). Fail Qed. Abort.
Goal forall s (p q : Conds s), p = q.
Proof. intros s p q. exact_no_check (eq_refl p). Fail Qed. Abort.
Opaque Conds.
Goal forall p q : Conds pure, p = q.
Proof. intros p q. exact_no_check (eq_refl p). Fail Qed. Abort.
