(* Author : CESally *)
Require Export Notions BinInt.
Close Scope Z_scope.
Close Scope N_scope.



Reserved Notation "x @ y" (at level 20, left associativity).

(* Declare Scope Groups. *)

Open Scope group_scope.


Module lGroups.
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

Coercion carrier: Group >-> Ensemble.

Remark group_facts : forall G: Group,
  closed_b G.(carrier) G.(op) /\
  is_assoc G.(carrier) G.(op) /\
  G.(e) ∈ G.(carrier) /\
  l_ident G.(carrier) G.(op) G.(e) /\
  r_ident G.(carrier) G.(op) G.(e) /\
  closed_u G.(carrier) G.(inv) /\
  l_inv G.(carrier) G.(op) G.(e) G.(inv) /\
  r_inv G.(carrier) G.(op) G.(e) G.(inv).
Proof.
  destruct G; repeat (split; auto).
Qed.


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

Corollary G_is_grp : forall G : Group,
 is_Group G.(carrier) G.(op) G.(e) G.(inv).
Proof.
  intros. decompose [and] (group_facts G).
  repeat split; auto.
Qed.

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
Hypothesis Hh: h ∈ H.
Hypothesis Nn: n ∈ N.
Hypothesis Gg: g ∈ G.
Hypothesis G1: g1 ∈ G.
Hypothesis G2: g2 ∈ G.
Local Infix "@" := G.(op) (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).


Inductive subgroup_ind : Prop :=
  Definition_of_sgrp :
    H ⊆ G -> H.(op) = G.(op) -> subgroup_ind.

Definition subgroup_prop : Prop :=
    H ⊆ G /\ H.(op) = G.(op).

Definition is_Subgroup_of (carrier : Ensemble C):=
  carrier ⊆ G /\
  closed_b carrier G.(op) /\
  is_assoc carrier G.(op) /\
  G.(e) ∈ carrier /\
  l_ident carrier G.(op) G.(e) /\
  r_ident carrier G.(op) G.(e) /\
  closed_u carrier G.(inv) /\
  l_inv carrier G.(op) G.(e) G.(inv) /\
  r_inv carrier G.(op) G.(e) G.(inv).


Local Notation subgroup := subgroup_prop.

Definition normal_subgroup : Prop :=
  subgroup /\
  n @ g @ (N.(inv) n) ∈ N.

Definition normal_comm : Prop :=
  g1 @ g2 ∈ N <-> g2 @ g1 ∈ N.

Export BinPos.Pos.
Close Scope positive_scope.
Definition rep_aux (id x: C) := iter (fun y => x @ y) id.

Definition rep (n: Z) : C :=
  match n with
  | Zpos p => rep_aux G.(e) g p
  | Zneg p => rep_aux G.(e) (g ') p
  | Z0     => G.(e)
  end.

(* Definition cyclic_subgroup : Prop :=
  subgroup /\
  ∀ (n: Z), rep n ∈ H.(carrier). *)

Inductive left_coset : Ensemble C :=
  lft_cs: subgroup ->
        g @ h ∈ (left_coset).

Inductive right_coset (g: C): Ensemble C :=
  rgt_cs: subgroup ->
          h @ g ∈ (right_coset g).
End Subgroups.
End Defn.


Arguments subgroup_ind [_].
Arguments subgroup_prop [_].
Local Notation subgroup := subgroup_prop.
Notation "A ≤ B" := (subgroup A B) (at level 70) : group_scope.

Section Homomorphisms.
Section top.
Context {C D: Type}.
Variable (G: @Group C) (H: @Group D).
Variable (g g1 g2: C) (h h1 h2: D).
Hypothesis Gg: g  ∈ G.
Hypothesis G1: g1 ∈ G.
Hypothesis G2: g2 ∈ G.
Hypothesis Hh: h  ∈ H.
Hypothesis H1: h1 ∈ H.
Hypothesis H2: h2 ∈ H.
Infix "@" := G.(op) (at level 20, left associativity).
Infix "+" := H.(op) (at level 50, left associativity).


Definition fn := C -> D.
(* carrier to carrier *)
Definition c2c (f:fn) := ∀ x (Gx: x ∈ G.(carrier)), f x ∈ H.(carrier).
Definition structure_preserving (f: fn) := c2c f /\
  ∀ a b, (f:fn) (a @ b) = (f:fn) a + (f:fn) b.
Definition homomorphism :=
  {f: fn |  structure_preserving f}.
Definition homo2fn (h: homomorphism) : fn := proj1_sig h.
Coercion   homo2fn : homomorphism >-> fn.
Definition homosp (h: homomorphism) := proj2_sig h.

Lemma homo_img_in : ∀ (f: homomorphism) x,
  x ∈ G.(carrier) -> (f:fn) x ∈ H.(carrier).
Proof.
  intros f. destruct f as [f [ghomo sp]].
  exact ghomo.
Qed.

Lemma homo_img_in' : ∀ (f: fn) x, c2c f ->
  x ∈ G.(carrier) -> (f:fn) x ∈ H.(carrier).
Proof. intros **. apply H0; auto. Qed.

Variable (f: homomorphism).
Definition kernel : Ensemble C := fun g => (f: fn) g = H.(e).
Definition image  : Ensemble D := fun h => forall g, (f: fn) g = h.

End top.



Arguments structure_preserving [_ _ _ _].

Section inverse.
Context {C D: Type}.
Variable (G: @Group C) (H: @Group D).
Variable (g g1 g2: C) (h h1 h2: D).
Hypothesis Gg: g  ∈ G.
Hypothesis G1: g1 ∈ G.
Hypothesis G2: g2 ∈ G.
Hypothesis Hh: h  ∈ H.
Hypothesis H1: h1 ∈ H.
Hypothesis H2: h2 ∈ H.
Infix "@" := G.(op) (at level 20, left associativity).
Infix "+" := H.(op) (at level 50, left associativity).


(* Require Import FinFun. *)
Definition Bijective (f: homomorphism G H) :=
  ∃ f' : (homomorphism H G),
    (∀ x, x ∈ G -> (f':fn) ((f :fn) x) = x) /\
    (∀ y, y ∈ H -> (f :fn) ((f':fn) y) = y).

Definition Injective (f: homomorphism G H) :=
  ∀ x y, x ∈ G -> y ∈ G ->
  (f:fn) x = (f:fn) y -> x = y.

Definition Surjective (f: homomorphism G H) :=
  ∀ y, y ∈ H.(carrier) -> ∃ x, x ∈ G.(carrier) /\ 
  (f:fn) x = y.



(* Require Import FinFun. *)
Definition isomorphism :=
  {f: homomorphism G H | Bijective f}.
Definition iso2homo (h: isomorphism): homomorphism G H := proj1_sig h.
Coercion   iso2homo : isomorphism >-> homomorphism.
Definition iso2fn (h: isomorphism) : fn := (proj1_sig (proj1_sig h)).
Coercion   iso2fn : isomorphism >-> fn.
Definition isosp (h: isomorphism) := (proj2_sig (proj1_sig h)).
Definition isob (h: isomorphism) := proj2_sig h.

Lemma Bi2I : ∀ {f: homomorphism G H}, Bijective f -> Injective f.
Proof with auto.
  intros * [f' [f'f ff']] x y Gx Gy fxfy.
  rewrite <- f'f, <- (f'f x), fxfy...
Qed.

Lemma Bi2S : ∀ {f: homomorphism G H}, Bijective f -> Surjective f.
Proof with auto.
  intros * [f' [f'f ff']] y Hy.
  exists ((f':fn) y). split...
  apply homo_img_in...
Qed.

Lemma Bi2I_S : ∀ {f: homomorphism G H}, Bijective f ->
                  Injective f /\ Surjective f.
Proof with auto.
  intros * [f' [f'f ff']].
  split.
  - intros x y Gx Gy fxfy. rewrite <- f'f, <- (f'f x), fxfy...
  - intros y Hy. exists ((f':fn) y). split... apply homo_img_in...
Qed.

(* Lemma I_S2Bi : ∀ {f: homomorphism G H},
  Injective f -> Surjective f -> Bijective f.
Proof with auto.
Admitted. *)

End inverse.
End Homomorphisms.

Arguments Bi2I_S [_ _ _ _ _].
Arguments rep [_ _].


Ltac b2is bi := destruct (Bi2I_S bi) as [?inj ?sur].
Ltac b2is' bi := destruct (Bi2I_S bi) as [inj sur];
                 unfold Injective in inj; unfold Surjective in sur;
                 simpl in *.
Ltac dhomo f := destruct f as [bbob [?ghomo ?sp]]; simpl in *;
                clear f; rename bbob into f.
Ltac diso  f := destruct f as [[bbob [?ghomo ?sp]] bi];
                b2is' bi; destruct bi as [f' [f'f ff']];
                clear f; rename bbob into f; simpl in *.

Ltac is_grp  := split;[|split;[|split;[|split;[|split;[|split;[|split]]]]]].
Ltac is_sgrp := split;[|split;[|split;[|split;[|split;[|split;[|split;
                [|split]]]]]]].







Create HintDb grp.
Hint Resolve homo_img_in : grp.
Hint Unfold is_assoc l_ident r_ident l_inv r_inv 
            In Included carrier lid rid linv rinv: grp.
Local Hint Resolve @closure @ein @lid @rid
                   @invin @linv @rinv
                   : grp.
Local Hint Rewrite @assoc : grp.
Ltac atg  :=  auto with grp.
Ltac eatg := eauto with grp.
Close Scope group_scope.