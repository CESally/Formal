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
                      (inv: C -> C) :=
    closed_b carrier op /\
    is_assoc carrier op /\
    e ∈ carrier /\
    l_ident carrier op e /\
    r_ident carrier op e /\
    closed_u carrier inv /\
    l_inv carrier op e inv /\
    r_inv carrier op e inv.

  Corollary grpify_is_Group : ∀ {a b c d}
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

  Definition grpify (G: Group) : Group := G.

  Corollary sanity_check_is_Group : ∀ a b c d
    (X: is_Group a b c d)
    (G' := grpify_is_Group X),
    G'.(carrier) = a /\
    G'.(op) = b /\
    G'.(e) = c /\
    G'.(inv) = d.
  Proof with auto.
    intros **. destruct X
      as [A [B [D [E [F [H [I J]]]]]]]...
  Qed.

End Groups.


Coercion grpify_is_Group : is_Group >-> Group.
Hint Resolve @ein : grp.
Hint Unfold is_Group : grp.

Ltac is_grp := split;[|split;[|split;[|split;[|split;[|split;[|split]]]]]].

Section other_group_constructs.
  Context {C: Type}.
  Variable (G: @Group C).
  Local Infix "@" := (op G) (at level 20, left associativity).

  Definition center : Ensemble C :=
    (λ z, ∀ g, g ∈ G -> z @ g = g @ z).
End other_group_constructs.


Section basics_facts.
Context {C: Type}.
Variable (G: @Group C).
Local Hint Resolve
(closure G) (lid G) (rid G) (invin G) (linv G) (rinv G)
: grp.
Local Notation e := (e G).
Local Notation op := (op G).
Local Notation assoc := (assoc G).
Local Notation lid := (lid G).
Local Notation rid := (rid G).
Local Notation linv := (linv G).
Local Notation rinv := (rinv G).
Local Notation ident := (ident G op).
Local Notation idempotent := (idempotent G op).
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

Theorem bl: ∀ g x y,
  g ∈ G -> x ∈ G -> y ∈ G ->
  x ≠ y -> g @ x ≠ g @ y.
Proof with auto.
  intros * Gg Gx Gy neq eq.
  apply neq. apply (left_can g)...
Qed.

Corollary e_is_ident : ident e.
Proof. split;atg. Qed.

Corollary e_is_idempotent : idempotent e.
Proof (conj (ein G) (rid e (ein G) (ein G))).
(* Proof. atg. Qed. *)


End basics_facts.


Hint Resolve @e_own_inv : grp.
Hint Rewrite @xii__x : grp.


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

Section subgroup_facts.
Context {C : Type}.
Context {K H G: @ Group C}.
Local Hint Resolve
(closure K) (lid K) (rid K) (invin K) (linv K) (rinv K)
(closure H) (lid H) (rid H) (invin H) (linv H) (rinv H)
(closure G) (lid G) (rid G) (invin G) (linv G) (rinv G)
              : grp.


(* Local Hint Rewrite @assoc : grp. *)
Local Infix "@" := (op G) (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).
Local Infix "+" := (op H) .
Local Notation "a '!'" := (inv H a) (at level 2, left associativity).


Theorem is_Subgroup_of_is_grp : ∀ {carr},
   is_Subgroup_of G carr -> is_Group carr G.(op) G.(e) G.(inv).
Proof with atg.
  intros * [? [? []]]. is_grp...
  - intros x y z xin yin zin.
    apply assoc...
Qed.

Theorem grpify_is_Subgroup_of : ∀ {carr},
   is_Subgroup_of G carr -> @Group C.
Proof.
  intros * X. apply is_Subgroup_of_is_grp in X.
  unfold is_Group in X. decompose [and] X.
  refine (mkgroup
    carr
    G.(op)
    G.(e)
    G.(inv)
    _ _ _ _ _ _ _ _
  ); auto.
Qed.


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

Corollary  bob :
H ≤ G <-> is_Subgroup_of G H.(carrier).
Proof with atg.
  split; intros.
  - repeat split; try pose proof H0 as [? ?]...
    + (* intros x y Hx Hy. *) rewrite <- H2...
    + rewrite <- subgroup_has_same_e... 
    + intros x Hx.  rewrite <- subgroup_has_same_invs...
  - pose proof H0 as [? [? []]]; split...
    + admit.
Admitted.



Theorem trivial_sg : is_Subgroup_of G (λ x, x = G.(e)).
Proof with atg.
  split;[|split;[|split]]...
  - intros x ->...
  - intros x y -> ->...
  - intros x ->...
Qed.

Theorem improper_sg : is_Subgroup_of G (fun x => G.(carrier) x).
Proof with atg.
  split;[|split;[|split]]...
Qed.

End subgroup_facts.


Hint Resolve subgroup_contains_e : grp.

Ltac ef_sg' HsgG := pose proof HsgG as [?incl ?Sm_o].
Ltac ef_sg  HsgG a b := pose proof HsgG as [a b].


Section Cosets.
  Context {C : Type}.

  Definition  left_coset {G: @Group C} (g: C) (H: @Group C) : Ensemble C :=
    λ x, g ∈ G /\ (H ≤ G ->
      ∃ h, h ∈ H /\ op G g h = x).

  Definition right_coset {G: @Group C} (H: @Group C) (g: C) : Ensemble C :=
    λ x, g ∈ G /\ (H ≤ G ->
      ∃ h, h ∈ H /\ op G h g = x).

  Inductive  left_coset_ind {G: @Group C} (g: C) (H: @Group C) : Ensemble C :=
    lci: g ∈ G -> H ≤ G ->
      ∀ h, h ∈ H -> op G g h ∈ @left_coset_ind G g H.

  Inductive right_coset_ind {G: @Group C} (H: @Group C) (g: C) : Ensemble C :=
    rci: g ∈ G -> H ≤ G ->
      ∀ h, h ∈ H -> op G h g ∈ @right_coset_ind G H g.

(*   Definition conjugate_set *)
End Cosets.

Notation "g 'l^' H" := ( left_coset g H) (at level 20, no associativity).
Notation "H '^r' g" := (right_coset H g) (at level 20, no associativity).
Notation "g 'i^' H" := ( left_coset_ind g H) (at level 20, no associativity).
Notation "H '^i' g" := (right_coset_ind H g) (at level 20, no associativity).

Section Normal_subgroups.
  Context {C : Type}.
  Variable (N G: @Group C).
  Local Infix "@" := G.(op) (at level 20, left associativity).
  Local Notation "a '''" := (inv G a) (at level 2, left associativity).

  Definition normal_subgroup : Prop :=
    N ≤ G /\
    ∀ n g, n ∈ N -> g ∈ G ->
    g @ n @ (g ') ∈ N.

  Definition normal_comm : Prop :=
    N ≤ G /\
    ∀ g1 g2, g1 ∈ G -> g2 ∈ G ->
    g1 @ g2 ∈ N <-> g2 @ g1 ∈ N.

  Definition normal_cosets : Prop :=
    N ≤ G /\
    ∀ g , (@left_coset C G g N) == (@right_coset C G N g).


  Definition normal_modular (normal: Ensemble C -> Group -> Prop) : Prop :=
    subgroup N G /\
    normal N G.

  Definition is_Normal_subgroup_of (N : Ensemble C) :=
    N ⊆ G /\
    closed_b N G.(op) /\
    G.(e) ∈ N /\
    closed_u N G.(inv) /\
    ((∀ n g, n ∈ N -> g ∈ G -> g @ n @ g ' ∈ N) \/
     (∀ g1 g2, g1 ∈ G -> g2 ∈ G -> g1 @ g2 ∈ N <-> g2 @ g1 ∈ N)).

  Definition is_Normal_subgroup_of_modular
    (N : Ensemble C) (normal: Ensemble C -> Group -> Prop) :=
    N ⊆ G /\
    closed_b N G.(op) /\
    G.(e) ∈ N /\
    closed_u N G.(inv) /\
    normal N G.

  Definition nmod_conjugate (N: Ensemble C) (G: @Group C) : Prop :=
    ∀ n g, n ∈ N -> g ∈ G ->      op G (op G g n) (G.(inv) g) ∈ N.

  Definition nmod_comm (N: Ensemble C) (G: @Group C) : Prop :=
    ∀ g1 g2, g1 ∈ G -> g2 ∈ G ->    G.(op) g1 g2 ∈ N <-> G.(op) g2 g1 ∈ N.

(*   Definition nmod_cosets (N: Ensemble C) (G: @Group C) : Prop :=
    ∀ g , (@left_coset C G g N) == (@right_coset C G N g). *)

End Normal_subgroups.

Section nsg_facts.
Context {C : Type}.
Variable (N G: @Group C).
Local Infix "@" := G.(op) (at level 20, left associativity).
Local Infix "+" := N.(op)(*  (at level 20, left associativity) *).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).
Local Notation "a '!'" := (inv N a) (at level 2, left associativity).
Local Hint Resolve
(closure N) (lid N) (rid N) (invin N) (linv N) (rinv N)
(closure G) (lid G) (rid G) (invin G) (linv G) (rinv G)
            : grp.


Example sanity_check : normal_comm N G <-> normal_modular N G nmod_comm.
Proof with atg.
  split; intros []; split...
Qed.

Corollary nsg_defns_same1 : normal_subgroup N G  <-> normal_comm N G.
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

Corollary nsg_defns_same2 : normal_cosets N G  <-> normal_comm N G.
Proof with atg.
  split; intros [NsgG normal]; ef_sg' NsgG; split...
  - intros g1 g2 G1 G2; split.
    + intros N12. destruct (normal (g1 ') g2)
                  as [[_ [g2g1 [N21 pr1'2]]] _]... {
        split... intros _. exists (g1@g2).
        split... rewrite <- assoc, G.(linv)... }
      destruct (lunique_sol G (g1 ') g2) as [pr [_ uni]]...
      rewrite <- (uni g2g1), (uni (g2@g1)) in N21...
      split... rewrite assoc, G.(rinv)...
    + intros N21. destruct (normal (g1 ') g2)
                  as [_ [_ [g2g1 [N12 g2'pr1]]]]... clear _tmp. {
        split... intros _. exists (g2@g1).
        split... rewrite assoc, G.(rinv)... }
      destruct (runique_sol G (g1 ') g2) as [pr [_ uni]]...
      rewrite <- (uni g2g1), (uni (g1@g2)) in N12...
      split... rewrite <- assoc, G.(linv)...
  - intros g x; split.
    + intros [Gg [n [Nn <-]]]... split...
      exists (g @ n @ g '). split.
      * rewrite normal, <- assoc, G.(linv)
        , <- (subgroup_has_same_e NsgG)
        , <- Sm_o...
      * rewrite assoc, G.(linv)...
    + intros [Gg [n [Nn <-]]]... split...
      exists (g ' @ (n @ g)). split.
      * rewrite normal, assoc, G.(rinv)
        , <- (subgroup_has_same_e NsgG)
        , <- Sm_o...
      * rewrite <- assoc, G.(rinv)...
Qed.

Corollary triv_is_nsg : is_Normal_subgroup_of G (fun x => x = G.(e)).
Proof with atg.
  split;[|split;[|split;[|split]]]...
  - intros x ->...
  - intros x y -> ->...
  - intros x ->...
  - left; intros n g -> Gg...
    rewrite rid...
Qed.

End nsg_facts.






Section Cyclic_subgroups.
Export BinPos.Pos.
Close Scope positive_scope.
  Context {C : Type}.
  Variable (H G: @Group C).
  Local Infix "@" := G.(op) (at level 20, left associativity).
  Local Infix "+" := N.(op)(*  (at level 20, left associativity) *).
  Local Notation "a '''" := (inv G a) (at level 2, left associativity).
  Local Notation "a '!'" := (inv N a) (at level 2, left associativity).
(*   Local Hint Resolve
  (closure H) (lid H) (rid N) (invin N) (linv N) (rinv N)
  (closure G) (lid G) (rid G) (invin G) (linv G) (rinv G)
              : grp. *)


Definition rep_aux (id x: C) := iter (fun y => x @ y) id.

Definition rep (n: Z) (g: C) : C :=
  match n with
  | Zpos p => rep_aux G.(e) g p
  | Zneg p => rep_aux G.(e) (g ') p
  | Z0     => G.(e)
  end.

(* Definition cyclic_subgroup : Prop :=
  subgroup /\
  ∀ (n: Z), rep n ∈ H.(carrier). *)
End Cyclic_subgroups.



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
  ∀ a b (Ga: a ∈ G) (Gb: b ∈ G),
    (f:fn) (a @ b) = (f:fn) a + (f:fn) b.
Definition homomorphism :=
  {f: fn |  structure_preserving f}.
Definition homo2fn (h: homomorphism) : fn := proj1_sig h.
Coercion   homo2fn : homomorphism >-> fn.
Definition homosp (h: homomorphism) := proj2_sig h.

Lemma homo_img_in : ∀ (f: homomorphism) x (Gx: x ∈ G),
  (f:fn) x ∈ H.
Proof.
  intros f. destruct f as [f [ghomo sp]].
  exact ghomo.
Qed.

Lemma homo_img_in' : ∀ f x (Gx: x ∈ G),
  c2c f -> f x ∈ H.
Proof. intros **. apply H0; auto. Qed.

Variable (f: homomorphism).
Definition kernel : Ensemble C := fun g => (f: fn) g = H.(e).
Definition image  : Ensemble D := fun h => forall g, (f: fn) g = h.



End top.



Arguments structure_preserving [_ _ _ _].

Section Isomorphisms.
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
    (∀ x (Gx: x ∈ G), (f' (f x) = x)) /\
    (∀ y (Gy: y ∈ H), (f (f' y) = y)).

Definition Injective (f: @fn C D) :=
  ∀ x y (Gx: x ∈ G) (Gy: y ∈ G),
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

End Isomorphisms.
End Homomorphisms.

Arguments Bi2I_S [_ _ _ _ _].
Arguments rep [_ _].
Arguments Iso2I_S [_ _ _ _].
Hint Resolve homo_img_in : grp.

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



Section QuotientGroups.
  Context {C: Type}.
  Variables (N G : @Group C).

  Definition quotient_of_in : Ensemble (Ensemble C) :=
    λ gN, normal_subgroup N G ->
      ∃ g, g ∈ G /\ gN == @left_coset C G g N.

  Inductive quotient_of_in_ind : Ensemble (Ensemble C) :=
    qoii: forall g, g ∈ G -> @left_coset C G g N ∈ quotient_of_in_ind.
  


End QuotientGroups.


Notation "N '/' G" := (quotient_of_in N G)
                       : group_scope.








Ltac is_ :=
  let three := split;[split|] in
  let four := split;[|split;[|split]] in
  let five := split;[|split;[|split;[|split]]] in
  match goal with
  | |- is_Group _ _ _ _ => is_grp
  | |- is_Subgroup_of _ _ => four
  | |- is_Normal_subgroup_of _ _ => five
  | |- is_Isomorphism _ _ _ => three
  end.









Close Scope group_scope.