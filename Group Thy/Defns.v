(* Author : CESally *)
Require Export Setoid Ensembles Utf8.
Reserved Notation "x @ y" (at level 20, left associativity).

(* Declare Scope Groups. *)
Delimit Scope group_scope with grp.
Definition Included' {X:Type} A B := Included X A B.
Definition In' {X:Type} e S := In X e S.
Notation "e ∈ S" := (In' S e) (at level 20) : group_scope.
Notation "A ⊆ B" := (Included' A B) (at level 20) : group_scope.
Open Scope group_scope.

Section Groups.
Variable C : Type.

Section Basic_laws.
Variable D  : Ensemble C.
Variable op : C -> C -> C.
Variable e  : C.
Local Infix "@" := op (at level 20, left associativity).

Definition is_assoc : Prop := ∀ x y z : C, x @ y @ z = x @ (y @ z).

Definition l_ident : Prop := ∀ x, e @ x = x.
Definition r_ident : Prop := ∀ x, x @ e = x.

Definition l_inv (inv:C -> C) : Prop := ∀ x, inv x @ x = e.
Definition r_inv (inv:C -> C) : Prop := ∀ x, x @ inv x = e.

Definition closed_u (inv: C -> C) : Prop := ∀ x,
  x ∈ D -> (inv x) ∈ D.
Definition closed_b : Prop := ∀ x y,
  x ∈ D ->
  y ∈ D -> (x @ y) ∈ D.

Definition is_l_inv_of (x' x e:C) : Prop := x' @ x = e.
Definition is_r_inv_of (x' x e:C) : Prop := x @ x' = e.

Definition conjugate (h g: C) (inv: C -> C) : C := h @ g @ (inv h).

End Basic_laws.


Section Grp_defn.

Record Group : Type := mkgroup {
  carrier  : Ensemble C;
  op : C -> C -> C;
  e  : C;
  inv: C -> C;
  closure : closed_b carrier op;
  assoc   : is_assoc op;

  ein : e ∈ carrier;
  lid : l_ident op e;
  rid : r_ident op e;

  invin : closed_u carrier inv;
  linv  : l_inv op e inv;
  rinv  : r_inv op e inv
}.

Definition is_Group (carrier : Ensemble C) (op: C -> C -> C)
                   (e: C) (inv: C -> C):=
  closed_b carrier op /\
  is_assoc op /\
  e ∈ carrier /\
  l_ident op e /\
  r_ident op e /\
  closed_u carrier inv /\
  l_inv op e inv /\
  r_inv op e inv.

Definition isn't_Group (carrier : Ensemble C) (op: C -> C -> C)
                   (e: C) (inv: C -> C):=
  ~ closed_b carrier op \/
  ~ is_assoc op \/
  ~ e ∈ carrier \/
  ~ l_ident op e \/
  ~ r_ident op e \/
  ~ closed_u carrier inv \/
  ~ l_inv op e inv \/
  ~ r_inv op e inv.



Section Subgroups.
Variable (H N G: Group) (h n g g1 g2: C).
Hypothesis Hh: h ∈ H.(carrier).
Hypothesis Nn: n ∈ N.(carrier).
Hypothesis Gg: g ∈ G.(carrier).
Hypothesis G1: g1 ∈ G.(carrier).
Hypothesis G2: g2 ∈ G.(carrier).
Local Infix "@" := G.(op) (at level 20, left associativity).

Inductive subgroup : Prop :=
  Definition_of_sgrp :
    H.(carrier) ⊆ G.(carrier) ->
    H.(op) = G.(op) -> subgroup.

Definition normal_subgroup : Prop :=
  subgroup /\
  n @ g @ (N.(inv) n) ∈ N.(carrier).

Definition normal_comm : Prop :=
  g1 @ g2 ∈ N.(carrier) <-> g2 @ g1 ∈ N.(carrier).

Inductive left_coset : Ensemble C :=
  lft_cs: subgroup ->
        g @ h ∈ (left_coset).

Inductive right_coset (g: C): Ensemble C :=
  rgt_cs: subgroup ->
          h @ g ∈ (right_coset g).
End Subgroups.
End Grp_defn.
End Groups.

Arguments subgroup [_].
Notation "A ≤ B" := (subgroup A B) (at level 70) : group_scope.

Section Homomorphisms.
Arguments carrier [_].
Arguments op [_].
Arguments e [_].
Variable (C D: Type).
Variable (G: Group C) (H: Group D).
Variable (g g1 g2: C) (h h1 h2: D).
Hypothesis Gg: g ∈ G.(carrier).
Hypothesis G1: g1 ∈ G.(carrier).
Hypothesis G2: g2 ∈ G.(carrier).
Hypothesis Hh: h ∈ H.(carrier).
Hypothesis H1: h1 ∈ H.(carrier).
Hypothesis H2: h2 ∈ H.(carrier).
Infix "@" := G.(op) (at level 20, left associativity).
Infix "+" := H.(op) (at level 50, left associativity).


Definition fn := C -> D.
Definition homomorphism :=
  {f: fn |  f (g1 @ g2) =  f g1 + f g2}.
Definition homo2fn (h: homomorphism) : fn := proj1_sig h.
Coercion   homo2fn : homomorphism >-> fn.
Variable (f: homomorphism).

Definition kernel : Ensemble C := fun g => (f: fn) g = H.(e).
Definition image  : Ensemble D := fun h => forall g, (f: fn) g = h.



End Homomorphisms.
Close Scope group_scope.

Create HintDb grp.
Hint Unfold is_assoc l_ident r_ident l_inv r_inv 
            In' In Included' Included carrier: grp.