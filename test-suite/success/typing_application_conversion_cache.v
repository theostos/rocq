Set Kernel Conversion Dep Heuristic.

(* Distinct applications share a costly inferred/expected domain pair, while
   HConstr's existing inference cache still sees distinct function heads. *)
Definition cache_zero := nat_rect (fun _ => nat) 0 (fun _ r => r) 512.
Definition cache_domain := match cache_zero with O => nat | S _ => bool end.
Definition cache_paths (a : cache_domain) (f g h : nat -> nat) :=
  (f a, g a, h a).
Check (cache_paths : cache_domain -> (nat -> nat) -> (nat -> nat) ->
  (nat -> nat) -> nat * nat * nat).

(* A result for nat must not authorize a comparison with another domain. *)
Fail Definition cache_wrong_domain (a : cache_domain) (f : nat -> nat)
  (g : bool -> nat) := (f a, g a).

(* Identical relative indices in distinct binder contexts are not enough. *)
Definition cache_scopes :=
  ((fun (x : nat) (f : nat -> nat) => f x),
   (fun (x : bool) (f : bool -> bool) => f x)).
Fail Definition cache_wrong_scope :=
  ((fun (x : nat) (f : nat -> nat) => f x),
   (fun (x : bool) (f : nat -> nat) => f x)).

(* Cumulativity is ordered; larger sorts cannot flow in the reverse direction. *)
Definition cache_up (F : Type -> Type) := F Set.
Fail Definition cache_down (F : Set -> Type) := F Type.
