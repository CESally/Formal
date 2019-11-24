(* Author : CESally *)
Require Export Setoid Ensembles Utf8.
Reserved Notation "x @ y" (at level 20, left associativity).

Delimit Scope group_scope with grp.
Arguments In [_].
Arguments Included [_].
Notation "e ∈ S" := (In S e) (at level 20) : group_scope.
Notation "A ⊆ B" := (Included A B) (at level 20) : group_scope.
Open Scope group_scope.

Module T.
Section top.
Context {C : Type}.
Variable D  : Ensemble C.
Variable op : C -> C -> C.
Variable   e  : C.
Hypothesis ein: e ∈ D.
Local Infix "@" := op (at level 20, left associativity).

Definition is_assoc : Prop := ∀ x y z : C,
  x ∈ D -> y ∈ D -> z ∈ D ->
  x @ y @ z = x @ (y @ z).

Definition is_comm : Prop := ∀ x y : C,
  x ∈ D -> y ∈ D -> x @ y = y @ x.

Definition idempotent (x: C) : Prop :=
  x ∈ D /\ x @ x = x.

Definition order2 (x: C) : Prop :=
  x ∈ D /\ x @ x = e.

Definition l_ident : Prop := ∀ x, x ∈ D -> e @ x = x.
Definition r_ident : Prop := ∀ x, x ∈ D -> x @ e = x.
Definition   ident : Prop := ∀ x, x ∈ D -> e @ x = x /\ x @ e = x.

Definition l_inv (inv:C -> C) : Prop := ∀ x, x ∈ D -> x ∈ D -> inv x @ x = e.
Definition r_inv (inv:C -> C) : Prop := ∀ x, x ∈ D -> x @ inv x = e.

Definition closed_u (inv: C -> C) : Prop := ∀ x,
  x ∈ D -> (inv x) ∈ D.
Definition closed_b : Prop := ∀ x y,
  x ∈ D -> y ∈ D -> (x @ y) ∈ D.

Definition is_l_inv_of (x' x e:C) : Prop := x' @ x = e.
Definition is_r_inv_of (x' x e:C) : Prop := x @ x' = e.

Definition conjugate (h g: C) (inv: C -> C) : C := h @ g @ (inv h).

End top.
End T.

Close Scope group_scope.
