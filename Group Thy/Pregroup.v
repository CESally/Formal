(* Author : CESally *)
Require Import Setoid Ensembles Utf8 Notions.
Open Scope group_scope.

Section pregroup_structures.
Context {C : Type}.

Section left_groups.
Record LGroup : Type := mkLGroup {
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

Section facts.
Variable (G: LGroup).
Variable (a b c id: C).
Hypothesis Ga : a ∈ G.(carrier).
Hypothesis Gb : b ∈ G.(carrier).
Hypothesis Gc : c ∈ G.(carrier).
Hypothesis Gi : id ∈ G.(carrier).
Local Notation e := (e G).
Local Notation op := (op G).
Local Notation assoc := (assoc G).
Local Infix "@" := op (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).

Hint Resolve (closure G) (ein G) (invin G) (lid G) : lgrp.
Hint Rewrite assoc : lgrp.

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

Theorem lft_id_is_id : ident G.(carrier) op e.
Proof with auto with lgrp.
  intros ? **. split...
  apply (left_can (x '))...
  rewrite <- assoc...
  repeat rewrite linv...
Qed.

Theorem lft_id_is_id' : r_ident G.(carrier) op e.
Proof with auto with lgrp.
  intros ? **.
  apply (left_can (x '))...
  rewrite <- assoc...
  repeat rewrite linv...
Qed.


Theorem lft_inv_is_inv: r_inv G.(carrier) op e G.(inv).
Proof with auto with lgrp.
  intros ? **. apply (left_can (x '))...
  rewrite <- assoc, G.(linv),
          G.(lid), lft_id_is_id'...
Qed.


Theorem right_can : forall z x y, 
  z ∈ G.(carrier) ->
  x ∈ G.(carrier) ->
  y ∈ G.(carrier) ->
  x @ z = y @ z -> x = y.
Proof with auto with lgrp.
  intros * Gz Gx Gy H.
  rewrite <- (lft_id_is_id' y),
          <-  lft_id_is_id'...
  rewrite <- (lft_inv_is_inv z)...
  repeat rewrite <- assoc...
  rewrite H...
Qed.

End facts.
End left_groups.



End pregroup_structures.





