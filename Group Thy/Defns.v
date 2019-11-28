(* Author : CESally *)
Require Export Notions BinInt.
Close Scope Z_scope.
Close Scope N_scope.
Open Scope group_scope.

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


Definition is_Group (carrier : Ensemble C)
                    (op: C -> C -> C)
                    (e: C)
                    (inv: C -> C):=
  closed_b carrier op /\
  is_assoc carrier op /\
  e ∈ carrier /\
  l_ident carrier op e /\
  r_ident carrier op e /\
  closed_u carrier inv /\
  l_inv carrier op e inv /\
  r_inv carrier op e inv.

Corollary is_Group__is_grp : ∀ a b c d
  (H: is_Group a b c d), Group.
Proof with auto.
  intros **. unfold is_Group in H.
  decompose [and] H.
  apply (mkgroup a b c d)...
Defined.


Corollary is_grp__is_Group : forall G : Group,
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

Section group_basics.
Local Infix "@" := op (at level 20, left associativity).
End group_basics.

Section Subgroups.
  Variable (H G: Group).

  Definition subgroup_prop : Prop :=
      H ⊆ G /\ H.(op) = G.(op).

  Definition is_Subgroup_of (H : Ensemble C):=
    H ⊆ G /\
    closed_b H G.(op) /\
    G.(e) ∈ H /\
    closed_u H G.(inv).

  (* Other subgroup facts in [Basics.v] *)
End Subgroups.

Local Notation subgroup := subgroup_prop.

Section Normal_subgroups.
  Variable (N G: Group) (n g g1 g2: C).
  Hypothesis Nn: n ∈ N.
  Hypothesis Gg: g ∈ G.
  Hypothesis G1: g1 ∈ G.
  Hypothesis G2: g2 ∈ G.
  Local Infix "@" := G.(op) (at level 20, left associativity).
  Local Notation "a '''" := (inv G a) (at level 2, left associativity).

  Definition normal_subgroup : Prop :=
    subgroup N G /\
    forall n g, n ∈ N -> g ∈ G ->
    n @ g @ (N.(inv) n) ∈ N.

  Definition normal_comm : Prop :=
    subgroup N G /\
    forall g1 g2, g1 ∈ G -> g2 ∈ G ->
    g1 @ g2 ∈ N <-> g2 @ g1 ∈ N.

  Definition is_Normal_subgroup_of (carrier : Ensemble C):=
    carrier ⊆ G /\
    closed_b carrier G.(op) /\
    G.(e) ∈ carrier /\
    closed_u carrier G.(inv) /\
    ( forall n, n @ g @ n ' ∈ carrier \/
      g1 @ g2 ∈ carrier <-> g2 @ g1 ∈ carrier).

End Normal_subgroups.

Section nsg_fact.
  Variable (N G: Group).
  Local Infix "@" := G.(op) (at level 20, left associativity).

  Corollary nsg_defns_same : normal_subgroup N G  <-> normal_comm N G.
  Proof with auto.
    split.
    - intros ? ? **. split; intro. unfold normal_subgroup in H.

  Qed.
End nsg_fact.



Section Cyclic_subgroups.
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
Definition c2c (f:fn) := ∀ x (Gx: x ∈ G), f x ∈ H.
Definition structure_preserving (f: fn) := c2c f /\
  ∀ a b, (f:fn) (a @ b) = (f:fn) a + (f:fn) b.
Definition homomorphism :=
  {f: fn |  structure_preserving f}.
Definition homo2fn (h: homomorphism) : fn := proj1_sig h.
Coercion   homo2fn : homomorphism >-> fn.
Definition homosp (h: homomorphism) := proj2_sig h.

Lemma homo_img_in : ∀ (f: homomorphism) x,
  x ∈ G -> (f:fn) x ∈ H.
Proof.
  intros f. destruct f as [f [ghomo sp]].
  exact ghomo.
Qed.

Lemma homo_img_in' : ∀ f x, c2c f ->
  x ∈ G -> f x ∈ H.
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


Definition Bijective (f: @fn C D) :=
  ∃ f' : @fn D C, @structure_preserving D C H G f' /\
    (∀ x, x ∈ G -> (f' (f x) = x)) /\
    (∀ y, y ∈ H -> (f (f' y) = y)).

Definition Injective (f: @fn C D) :=
  ∀ x y, x ∈ G -> y ∈ G ->
  f x = f y -> x = y.

Definition Surjective (f: @fn C D) :=
  ∀ y, y ∈ H -> ∃ x, x ∈ G /\
  f x = y.




Definition isomorphism :=
  {f: @fn C D | @structure_preserving C D G H f & Bijective f}.
Definition iso2homo (h: isomorphism): homomorphism G H :=
  exist _ (proj1_sig (sig_of_sig2 h)) (proj2_sig (sig_of_sig2 h)).
Coercion   iso2homo : isomorphism >-> homomorphism.
Definition iso2fn (h: isomorphism) : fn := (proj1_sig (sig_of_sig2 h)).
Coercion   iso2fn : isomorphism >-> fn.
Definition isosp (h: isomorphism) := (proj2_sig (sig_of_sig2 h)).
Definition isob (h: isomorphism) := proj3_sig h.

Lemma Bi2I : ∀ {f: homomorphism G H}, Bijective f -> Injective f.
Proof with auto.
  intros * [f' [_ [f'f ff']]] x y Gx Gy fxfy.
  rewrite <- f'f, <- (f'f x), fxfy...
Qed.

Lemma Bi2S : ∀ {f: homomorphism G H}, Bijective f -> Surjective f.
Proof with eauto.
  intros * [f' [[g2g sp] [f'f ff']]] y Hy.
  exists (f' y); split...
Qed.

Lemma Bi2I_S : ∀ {f: homomorphism G H}, Bijective f ->
                  Injective f /\ Surjective f.
Proof with auto.
  intros * [f' [[g2g sp] [f'f ff']]]. split.
  - intros x y Gx Gy fxfy.
    rewrite <- f'f, <- (f'f x), fxfy...
  - intros y Hy. exists (f' y); split...
Qed.


Lemma Iso2I : ∀ (f: isomorphism), Injective f.
Proof with auto.
  destruct f
    as [f [ghomo sp] [f' [[ghomo' sp'] [f'f ff']]]]
  ; simpl. intros x y Gx Gy fxfy.
  rewrite <- (f'f x), fxfy...
Qed.

Lemma Iso2S : ∀ (f: isomorphism), Surjective f.
Proof with auto.
  destruct f
    as [f [ghomo sp] [f' [[ghomo' sp'] [f'f ff']]]]
  ; simpl. intros y Hy. exists (f' y); split...
Qed.

Lemma Iso2I_S : ∀ (f: isomorphism),
  Injective f /\ Surjective f.
Proof with auto.
  destruct f
    as [f [ghomo sp] [f' [[ghomo' sp'] [f'f ff']]]]
  ; simpl; split.
  - intros x y Gx Gy fxfy. rewrite <- (f'f x), fxfy...
  - intros y Hy. exists (f' y); split...
Qed.


Definition is_Isomorphism (f:@fn C D): Prop :=
  @structure_preserving C D G H f /\ Bijective f.

Definition is_Isomorphism_is_iso : forall {f}
  (H: is_Isomorphism f), isomorphism.
Proof with auto.
  intros * [sp bi].
  refine (exist2 _ _ _ sp bi).
Qed.


Definition is_Isomorphic : Prop := exists (f:isomorphism), True.







(* Lemma I_S2Bi : ∀ {f: homomorphism G H},
  Injective f -> Surjective f -> Bijective f.
Proof with auto.
Admitted. *)

End inverse.
End Homomorphisms.

Arguments Bi2I_S [_ _ _ _ _].
Arguments rep [_ _].
Arguments Iso2I_S [_ _ _ _].

Ltac iso2is iso := destruct (Iso2I_S iso) as [?inj ?sur].
Ltac b2is  bi := destruct (Bi2I_S bi) as [?inj ?sur].
Ltac b2is' bi := destruct (Bi2I_S bi) as [inj sur];
                 unfold Injective in inj; unfold Surjective in sur;
                 simpl in *.
Ltac dhomo f := destruct f as [bbob [?ghomo ?sp]];
                rename f into f_homo; rename bbob into f;
                simpl in *.
Ltac diso  f := iso2is f;
                destruct f as [bbob [?ghomo ?sp]
                               [f' [[?ghomo' ?sp'] [f'f ff']]]];
                rename f into f_iso; rename bbob into f;
                simpl in *.


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