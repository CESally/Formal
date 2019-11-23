(* Author : CESally *)
Require Import Notions.
Reserved Notation "x @ y" (at level 20, left associativity).

(* Declare Scope Groups. *)

Open Scope group_scope.


Module lGroups.
Include Notions.T.
Section Defn.
Context {C : Type}.

Record t : Type := mklgroup {
  carrier  : Ensemble C;
  op : C -> C -> C;
  e  : C;
  inv: C -> C;
  closure : closed_b carrier op;
  assoc   : is_assoc carrier op;

  ein : e ∈ carrier;
  lid : l_ident carrier op e;

  invin : closed_u carrier inv;
  linv  : l_inv carrier op e inv
}.
End Defn.


Section Basics.
Context {C : Type}.
Variable (G: @t C).
Variable (a b c  id: C).
Hypothesis Ga : a ∈ G.(carrier).
Hypothesis Gb : b ∈ G.(carrier).
Hypothesis Gc : c ∈ G.(carrier).
Hypothesis Gi : id ∈ G.(carrier).
Local Notation e := (e G).
Local Notation op := (op G).
Local Notation assoc := (assoc G).
Local Infix "@" := op (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).

Hint Resolve (closure G) ein (invin G)  : lgrp.
Hint Rewrite @assoc : lgrp.

Theorem left_can : forall z x y, 
  z ∈ G.(carrier) ->
  x ∈ G.(carrier) ->
  y ∈ G.(carrier) ->
  z @ x = z @ y -> x = y.
Proof with auto with lgrp.
  intros * Gz Gx Gy H.
  rewrite <- G.(lid), <- (G.(lid) y)...
  rewrite <- (G.(linv) z)...
  repeat rewrite assoc...
  rewrite H...
Qed.


Theorem lft_id_is_id: r_ident G.(carrier) op e.
Proof with auto with lgrp.
  intros ? **.
  apply (left_can (x '))...
  rewrite <- assoc...
  repeat rewrite linv...
  rewrite lid...
Qed.


Theorem lft_inv_is_inv: r_inv G.(carrier) op e G.(inv).
Proof with auto with lgrp.
  intros ? **. apply (left_can (x '))...
  rewrite <- assoc, G.(linv),
          G.(lid), lft_id_is_id...
Qed.

End Basics.
End lGroups.


Module Groups.
Include T.
Section Defn.
Context {C : Type}.


Record Group : Type := mkgroup {
  carrier  : Ensemble C;
  op : C -> C -> C;
  e  : C;
  inv: C -> C;
  closure : closed_b carrier op;
  assoc   : is_assoc carrier op;

  ein : e ∈ carrier;
  lid : l_ident carrier op e;
  rid : r_ident carrier op e;

  invin : closed_u carrier inv;
  linv  : l_inv carrier op e inv;
  rinv  : r_inv carrier op e inv
}.

Definition is_Group (carrier : Ensemble C) (op: C -> C -> C)
                   (e: C) (inv: C -> C):=
  closed_b carrier op /\
  is_assoc carrier op /\
  e ∈ carrier /\
  l_ident carrier op e /\
  r_ident carrier op e /\
  closed_u carrier inv /\
  l_inv carrier op e inv /\
  r_inv carrier op e inv.

Definition isn't_Group (carrier : Ensemble C) (op: C -> C -> C)
                   (e: C) (inv: C -> C):=
  ~ closed_b carrier op \/
  ~ is_assoc carrier op \/
  ~ e ∈ carrier \/
  ~ l_ident carrier op e \/
  ~ r_ident carrier op e \/
  ~ closed_u carrier inv \/
  ~ l_inv carrier op e inv \/
  ~ r_inv carrier op e inv.



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
End Defn.


Arguments subgroup [_].
Notation "A ≤ B" := (subgroup A B) (at level 70) : group_scope.

Section Homomorphisms.
Variable (C D: Type).
Variable (G: @Group C) (H: @Group D).
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
            In Included carrier lid rid linv rinv: grp.
Ltac atg := auto with grp.


End Groups.
Close Scope group_scope.