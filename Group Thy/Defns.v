(* Author : CESally *)
Require Export Notions BinInt.
Close Scope Z_scope.
Close Scope N_scope.
Open Scope group_scope.




Section Groups.
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

Remark group_axioms : forall G: Group,
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


Corollary is_grp__is_Group : ∀ G: Group,
 is_Group G.(carrier) G.(op) G.(e) G.(inv).
Proof.
  intros. decompose [and] (group_axioms G).
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

End Groups.

Section other_group_constructs.
  Context {C: Type}.
  Variable (G: @Group C).
  Local Infix "@" := (op G) (at level 20, left associativity).

  Definition center : Ensemble C :=
    (λ z, ∀ g, g ∈ G -> z @ g = g @ z).

End other_group_constructs.

Ltac is_grp  := split;[|split;[|split;[|split;[|split;[|split;[|split]]]]]].


Section basics_facts.
Context {C: Type}.
Variable (G: @Group C).
Local Hint Resolve
(closure G) (ein G) (lid G) (rid G) (invin G) (linv G) (rinv G)
: grp.
Local Notation e := (e G).
Local Notation op := (op G).
Local Notation assoc := (assoc G).
Local Notation lid := (lid G).
Local Notation rid := (rid G).
Local Notation linv := (linv G).
Local Notation rinv := (rinv G).
Local Notation ident := (ident G op).
Local Notation l_ident := (l_ident G op).
Local Notation r_ident := (r_ident G op).
Local Infix "@" := op (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).

Theorem left_can : ∀ z {x y},
  x ∈ G -> y ∈ G -> z ∈ G ->
  z @ x = z @ y -> x = y.
Proof with atg.
  intros * Gz Gx Gy H.
  rewrite <- lid, <- (lid y)...
  rewrite <- (linv z)...
  repeat rewrite assoc...
  rewrite H...
Qed.

Theorem right_can : ∀ z {x y},
  x ∈ G -> y ∈ G -> z ∈ G ->
  x @ z = y @ z -> x = y.
Proof with atg.
  intros * Gz Gx Gy H.
  rewrite <- rid, <- (rid y),
          <- (rinv z)...
  repeat rewrite <- assoc...
  rewrite H...
Qed.

Theorem l_gives_r_id : ∀ x,
  l_ident x -> r_ident x.
Proof with atg.
  intros x xlid y Gx Gy...
  apply (right_can y)...
  rewrite assoc, xlid...
Qed.

Theorem r_gives_l_id : ∀ x,
  r_ident x -> l_ident x.
Proof with atg.
  intros x xrid y Gx Gy...
  apply (left_can y)...
  rewrite <- assoc, xrid...
Qed.

Theorem e_unique :∀ id, id ∈ G ->
  ident id -> id = e.
Proof with atg.
  intros **. destruct (H0 e)...
  apply (left_can e)...
  symmetry; rewrite H2...
Qed.

Theorem inv_unique : ∀ x x', x ∈ G -> x' ∈ G ->
  x' @ x  = e ->
  x  @ x' = e ->
  x' = x '.
Proof with atg.
  intros **. apply (left_can x)...
  symmetry; rewrite H2...
Qed.

Theorem e_own_inv : e ' = e.
Proof with atg.
  apply (left_can e)...
  rewrite rinv, lid...
Qed.

Theorem xii__x : ∀ x, x ∈ G ->
  x ' ' = x.
Proof with atg.
  intros **. apply (left_can (x '))...
  rewrite rinv, linv...
Qed.

Theorem inv_of_op : ∀ x y
  (Gx: x ∈ G)
  (Gy: y ∈ G),
  (x @ y) ' = y ' @ x '.
Proof with atg.
  intros **.
  apply (left_can (x @ y))...
  symmetry; rewrite rinv,
                    <- assoc,
                    (assoc x),
                    rinv,
                    rid...
Qed.

Theorem lunique_sol : ∀ g1 g2
  (G1: g1 ∈ G) (G2: g2 ∈ G),
  exists! x, x ∈ G /\
  x @ g1 = g2.
Proof with atg.
  intros **. exists (g2 @ g1 '); split.
  - split... rewrite assoc, linv...
  - intros ? []. rewrite <- H0, assoc, rinv...
Qed.

Theorem runique_sol : ∀ g1 g2
  (G1: g1 ∈ G) (G2: g2 ∈ G),
  exists! x, x ∈ G /\
  g1 @ x = g2.
Proof with atg.
  intros **. exists (g1 ' @ g2); split.
  - rewrite <- assoc, rinv...
  - intros ? [].
    rewrite <- H0, <- assoc, linv...
Qed.

Theorem e_is_lunique_sol_gg : ∀ g x,
  g ∈ G -> x ∈ G ->
  x @ g = g -> x = e.
Proof with atg.
  intros g x Gg Gx xgg.
  destruct (lunique_sol _ _ Gg Gg)
    as [x' [[Gx' x'gg] uni]].
  rewrite <- xgg in x'gg at 2.
  rewrite
  <- (right_can _ Gx' Gx Gg x'gg)...
Qed.

Theorem e_is_runique_sol_gg : ∀ g x,
  g ∈ G -> x ∈ G ->
  g @ x = g -> x = e.
Proof with atg.
  intros g x Gg Gx gxg.
  destruct (runique_sol _ _ Gg Gg)
    as [x' [[Gx' gx'g] uni]].
  rewrite <- gxg in gx'g at 2.
  rewrite
  <- (left_can _ Gx' Gx Gg gx'g)...
Qed.


End basics_facts.






Section Subgroups.
  Context {C : Type}.
  Variable (H G: @Group C).

  Definition subgroup : Prop :=
      H ⊆ G /\ H.(op) = G.(op).

  Definition is_Subgroup_of (H : Ensemble C):=
    H ⊆ G /\
    closed_b H G.(op) /\
    G.(e) ∈ H /\
    closed_u H G.(inv).
End Subgroups.

Notation "H ≤ G" := (subgroup H G) : group_scope.
Ltac is_sgrp := split;[|split;[|split]].

Section subgroup_facts.
Context {C : Type}.
Context {K H G: @ Group C}.
Local Hint Resolve
(closure K) (ein K) (lid K) (rid K) (invin K) (linv K) (rinv K)
(closure H) (ein H) (lid H) (rid H) (invin H) (linv H) (rinv H)
(closure G) (ein G) (lid G) (rid G) (invin G) (linv G) (rinv G)
              : grp.


(* Local Hint Rewrite @assoc : grp. *)
Local Infix "@" := (op G) (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).
Local Infix "+" := (op H) .
Local Notation "a '!'" := (inv H a) (at level 2, left associativity).



Theorem subgroup_has_same_e : H ≤ G ->
  H.(e) = G.(e).
Proof with atg.
  intros [HiG Sm_o].
  destruct (lunique_sol G H.(e) H.(e))
    as [eG [[GeG X] uniG]]...
  rewrite <- (uniG G.(e)) by (split; atg).
  rewrite <- (uniG H.(e)) by
    (split;[|rewrite <- Sm_o, H.(lid)]; atg).
  auto.
Qed.

Lemma subgroup_contains_e : H ≤ G ->
  G.(e) ∈ H.
Proof with atg.
  intros HsgG.
  rewrite <- (subgroup_has_same_e HsgG)...
Qed.

Lemma subgroup_has_same_invs : H ≤ G ->
  ∀ a, a ∈ H ->
  H.(inv) a = G.(inv) a.
Proof with atg.
  intros HsgG a Ha.
  pose proof HsgG as [HiG Sm_o].
  pose proof (subgroup_has_same_e HsgG) as Sm_e.
  destruct (lunique_sol G a H.(e))
    as [a' [[GeG X] uniG]]...
  rewrite <- (uniG (G.(inv) a)) by (split;[|rewrite Sm_e];atg).
  rewrite <- (uniG (H.(inv) a)) by (split;[|rewrite <- Sm_o];atg).
  auto.
Qed.

Theorem is_Subgroup_of_is_grp : ∀ carr,
is_Subgroup_of G carr -> is_Group carr G.(op) G.(e) G.(inv).
Proof with atg.
  intros * [? [? []]]. is_grp...
  - intros x y z xin yin zin.
    apply assoc...
  - intros x _ xin. rewrite G.(lid)...
  - intros x _ xin. rewrite G.(rid)...
  - intros x   xin. rewrite G.(linv)...
  - intros x   xin. rewrite G.(rinv)...
Qed.

Corollary  bob :
H ≤ G <-> is_Subgroup_of G H.(carrier).
Proof with atg.
  split; intros.
  - repeat split; try pose proof H0 as [? ?]...
    + (* intros x y Hx Hy. *) rewrite <- H2...
    + rewrite <- subgroup_has_same_e... 
    + intros x Hx.  rewrite <- subgroup_has_same_invs...
  - pose proof H0 as [? [? []]]; split...
assert (forall x y, In H x -> In H y -> op H x y = op G x y).
{ intros.
    + extensionality. admit.
Admitted.



Theorem trivial_sg : is_Subgroup_of G (λ x, x = G.(e)).
Proof with atg.
  is_sgrp...
  - intros x ->...
  - intros x y -> ->...
  - intros x ->. rewrite e_own_inv...
Qed.

Theorem improper_sg : is_Subgroup_of G (fun x => G.(carrier) x).
Proof with atg. is_sgrp... Qed.

End subgroup_facts.

Ltac ef_sg' HsgG := pose proof HsgG as [?incl ?Sm_o].
Ltac ef_sg  HsgG a b := pose proof HsgG as [a b].




Section Normal_subgroups.
  Context {C : Type}.
  Variable (N G: @Group C).
(*   Variable (N G: Group) (n g g1 g2: C).
  Hypothesis Nn: n ∈ N.
  Hypothesis Gg: g ∈ G.
  Hypothesis G1: g1 ∈ G.
  Hypothesis G2: g2 ∈ G. *)
  Local Infix "@" := G.(op) (at level 20, left associativity).
  Local Notation "a '''" := (inv G a) (at level 2, left associativity).

  Definition normal_subgroup : Prop :=
    subgroup N G /\
    forall n g, n ∈ N -> g ∈ G ->
    g @ n @ (g ') ∈ N.

  Definition normal_comm : Prop :=
    subgroup N G /\
    forall g1 g2, g1 ∈ G -> g2 ∈ G ->
    g1 @ g2 ∈ N <-> g2 @ g1 ∈ N.

  Definition is_Normal_subgroup_of (N : Ensemble C):=
    N ⊆ G /\
    closed_b N G.(op) /\
    G.(e) ∈ N /\
    closed_u N G.(inv) /\
    ((forall n g, n ∈ N -> g ∈ G -> g @ n @ g ' ∈ N) \/
     (forall g1 g2, g1 ∈ G -> g2 ∈ G -> g1 @ g2 ∈ N <-> g2 @ g1 ∈ N)).

End Normal_subgroups.

Section nsg_facts.
  Context {C : Type}.
  Variable (N G: @Group C).
  Local Infix "@" := G.(op) (at level 20, left associativity).
  Local Infix "+" := N.(op)(*  (at level 20, left associativity) *).
  Local Notation "a '''" := (inv G a) (at level 2, left associativity).
  Local Notation "a '!'" := (inv N a) (at level 2, left associativity).
  Local Hint Resolve
  (closure N) (ein N) (lid N) (rid N) (invin N) (linv N) (rinv N)
  (closure G) (ein G) (lid G) (rid G) (invin G) (linv G) (rinv G)
              : grp.

  Corollary nsg_defns_same : normal_subgroup N G  <-> normal_comm N G.
  Proof with atg.
    split; intros [NsgG normal]; ef_sg' NsgG.
    - split...
      intros * G1 G2. split.
      + intros N12.
        epose proof (normal _ (g1 ') N12 _).
        Unshelve. 2:{ atg. }
        rewrite xii__x, <- assoc
              , linv, lid in H...
      + intros N21.
        epose proof (normal _ (g2 ') N21 _).
        Unshelve. 2:{ atg. }
        rewrite xii__x, <- assoc
              , linv, lid in H...
  - split... intros * Nn Gg.
    destruct (normal (g@n) (g ')) as [_ X]...
    apply X. rewrite <- assoc, linv, lid...
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











Hint Resolve homo_img_in : grp.
Close Scope group_scope.