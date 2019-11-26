(* Author : CESally *)
Require Import Defns.
Import Pos.


Open Scope group_scope.
Section elementary.
Context {C : Type}.
Variable (G: @Group C).
Variable (a b c : C).
Local Hint Resolve
(closure G) (ein G) (lid G) (rid G) (invin G) (linv G) (rinv G)
: grp.
Local Hint Rewrite @assoc : grp.

Local Notation op := (op G).
Local Notation assoc := (assoc G).
Local Notation e := (e G).
Local Notation linv := (linv G).
Local Notation rinv := (rinv G).
Local Notation lid := (lid G).
Local Notation rid := (rid G).
Local Notation ident := (ident G op).
Local Notation l_ident := (l_ident G op).
Local Notation r_ident := (r_ident G op).
Local Notation rep_aux := (rep_aux G).
Local Notation idempotent := (idempotent G op).
Local Notation order2 := (order2 G op e).
Hypothesis Ga : a ∈ G.
Hypothesis Gb : b ∈ G.
Hypothesis Gc : c ∈ G.
Local Infix "@" := op (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).

Theorem left_can : forall z {x y},
  x ∈ G -> y ∈ G -> z ∈ G ->
  z @ x = z @ y -> x = y.
Proof with atg.
  intros * Gz Gx Gy H.
  rewrite <- lid, <- (lid y)...
  rewrite <- (linv z)...
  repeat rewrite assoc...
  rewrite H...
Qed.

Theorem right_can : forall z {x y},
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

Theorem inv_unique : ∀ a', a' ∈ G ->
  a' @ a = e ->
  a @ a' = e ->
  a' = a '.
Proof with atg.
  intros **. apply (left_can a)...
  symmetry; rewrite H1...
Qed.

Theorem e_own_inv : e ' = e.
Proof with atg.
  apply (left_can e)...
  rewrite rinv, lid...
Qed.

Theorem xii__x : forall x, x ∈ G ->
  x ' ' = x.
Proof with atg.
  intros **. apply (left_can (x '))...
  rewrite rinv, linv...
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
  a @ x = b.
Proof with atg.
  intros **. exists (a ' @ b); split.
  - rewrite <- assoc, rinv...
  - intros ? []. rewrite <- H0, <- assoc, linv...
Qed.

Theorem e_is_lunique_sol_aa :
  exists! x, x ∈ G /\
  x @ a = a /\ x = e.
Proof with atg.
  exists e. repeat split...
  - intros Ge [_ [_ ->]]...
Qed.

Theorem e_is_lunique_sol_aa' :
  exists! x, x ∈ G /\
  x @ a = a /\ ident x.
Proof with atg.
  exists e. repeat split...
  intros Ge [GGe [_ ?]].
  rewrite e_unique...
Qed.

Theorem e_is_runique_sol_aa :
  exists! x, x ∈ G /\
  a @ x = a /\ x = e.
Proof with atg.
  exists e. repeat split...
  - intros Ge [_ [_ ->]]...
Qed.

Theorem e_is_runique_sol_aa' :
  exists! x, x ∈ G /\
  a @ x = a /\ ident x.
Proof with atg.
  exists e. repeat split...
  intros Ge [GGe [_ ?]].
  rewrite e_unique...
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

Theorem rep_aux_in : ∀ {x p} {Gx: x ∈ G},
  rep_aux e x p ∈ G.
Proof with auto.
  intros **. unfold rep_aux.
  apply iter_invariant;[| exact G.(ein)].
  intros **. apply closure...
Qed.

Theorem rep_in : ∀ i, @rep C G a i ∈ G.
Proof with auto.
  pose proof G.(ein).
  destruct i; simpl; auto;
  unfold rep_aux; apply iter_invariant;
  auto; intros **; apply closure...
  apply invin...
Qed.

Local Open Scope Z_scope.

Theorem cyclic_inv : ∀ i, (@rep C G a i) ' = @rep C G a (- i).
Proof with auto.
Admitted.



Theorem idem__ident : ∀ x, x ∈ G ->
  (idempotent x) -> ident x.
Proof with atg.
  intros ? ? [Gx idem] y Gy. split.
  - apply (left_can x)...
    rewrite <- assoc, idem...
  - apply (right_can x)...
    rewrite assoc, idem...
Qed.

Theorem idem__unique : ∀ x y
  (Gx: x ∈ G)
  (Gy: y ∈ G)
  (idemx: idempotent x)
  (idemy: idempotent y),
  x = y.
Proof with atg.
  intros **.
  apply idem__ident, e_unique in idemx...
  apply idem__ident, e_unique in idemy...
  subst...
Qed.

Theorem order2__abelian : (∀ x, order2 x) -> is_comm G op.
Proof with atg.
  intros o2 x y Gx Gy. apply (left_can x), (right_can y)...
  repeat rewrite <- assoc...
  pose proof (o2 x) as [_ o2x].
  pose proof (o2 y) as [_ o2y].
  pose proof (o2 (x@y)) as [_ o2xy].
  rewrite o2x, lid, o2y, (assoc (x@y))...
Qed.

Theorem inv_comm__abelian :
  (a @ b) ' = a ' @ b ' <-> a @ b = b @ a.
Proof with atg.
  rewrite inv_of_op... split; intros H.
  - apply (left_can (a '))...
    rewrite <- assoc, linv, lid...
    apply (left_can (b '))...
    repeat rewrite <- assoc...
    rewrite linv, H, (assoc (a ')),
            linv, rid, linv...
  - apply (left_can b)...
    rewrite <- assoc, rinv, lid...
    apply (left_can a)...
    rewrite rinv, <- assoc, H,
            <- (assoc (b@a)), (assoc b),
            rinv, rid, rinv...
Qed.

Theorem ab_squared__comm :
  a @ b @ a @ b = a @ a @ b @ b <-> a @ b = b @ a.
Proof with atg.
  split; intros H.
  - apply (left_can a)...
    repeat rewrite <- assoc...
    apply (right_can b)...
  - rewrite (assoc a), <- H...
    rewrite <- assoc...
Qed.

End elementary.

Section subgroups1.
Context {C : Type}.
Context {K H G: @ Group C}.
Local Hint Resolve
(closure K) (ein K) (lid K) (rid K) (invin K) (linv K) (rinv K)
(closure H) (ein H) (lid H) (rid H) (invin H) (linv H) (rinv H)
(closure G) (ein G) (lid G) (rid G) (invin G) (linv G) (rinv G)
              : grp.
Local Hint Rewrite @assoc : grp.


Theorem subgroup_has_same_e : H ≤ G ->
  H.(e) = G.(e).
Proof with atg.
  intros [HiG Sm_o].
  destruct (lunique_sol G H.(e) H.(e))
    as [eG [[GeG X] uniG]]...
  rewrite <- (uniG G.(e)) by (split; atg).
  rewrite <- (uniG H.(e)) by (
    split;[|rewrite <- Sm_o, H.(lid)]; atg).
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

Theorem trivial_sg : is_Subgroup_of G (fun x => x = G.(e)).
Proof with atg.
  is_sgrp...
  - intros x ->...
  - intros x y -> ->...
  - intros x y z -> -> ->.
    apply assoc...
  - intros x _ ->...
  - intros x _ ->...
  - intros x ->. rewrite e_own_inv...
  - intros x ->...
  - intros x ->...
Qed.


End subgroups1.

Section subgroups2.
Context {C : Type}.
Context {K H G: @ Group C}.
Local Hint Resolve
(closure K) (ein K) (lid K) (rid K) (invin K) (linv K) (rinv K)
(closure H) (ein H) (lid H) (rid H) (invin H) (linv H) (rinv H)
(closure G) (ein G) (lid G) (rid G) (invin G) (linv G) (rinv G)
              : grp.
Local Hint Rewrite @assoc : grp.

Variable (a b c : C).
Local Infix "@" := G.(op) (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).

Lemma intersection_preserves_sgness : K ≤ G -> H ≤ G ->
  is_Subgroup_of G (fun x => x ∈ H /\ x ∈ K).
Proof with eatg.
  intros KsgG HsgG.
  pose proof KsgG as [KiG sok].
  pose proof HsgG as [HiG soh]. is_sgrp...
  - intros x [Hx Kx]...
  - intros x y [Hx Kx] [Hy Ky].
    split;[rewrite <- soh|rewrite <- sok];
    apply closure...
  - intros x y z [Hx _] [Hy _] [Hz _].
    apply assoc...
  - split; erewrite <- (subgroup_has_same_e)...
  - intros x [] []. rewrite lid...
  - intros x [] []. rewrite rid...
  - intros x [Hx Kx]. split;
    erewrite <- subgroup_has_same_invs...
  - intros x [Hx Kx]. rewrite linv...
  - intros x [Hx Kx]. rewrite rinv...
Qed.



Theorem comm_around_a_subgroup : a ∈ G ->
is_Subgroup_of G (fun x => x ∈ G /\ x @ a = a @ x).
Proof with atg.
  intros Ga. is_sgrp.
  - intros x [Gx _]...
  - intros x y [Gx xac] [Hy yac]; split.
    + apply closure...
    + rewrite assoc, yac, <- assoc,
      xac, assoc...
  - intros x y z [Gx _] [Gy _] [Gz _].
    apply assoc...
  - split... rewrite lid, rid...
  - intros x _ [Gx _]. rewrite lid...
  - intros x _ [Gx _]. rewrite rid...
  - intros x [Gx xac]. split...
    apply (@left_can C G x)...
    repeat rewrite <- assoc...
    rewrite rinv, lid, xac, assoc,
            rinv, rid...
  - intros x [Gx _]. apply linv...
  - intros x [Gx _]. apply rinv...
Qed.

End subgroups2.

Section semiconcreteSG.
Context {C : Type}.
Context {G: @ Group C}.
Variable (a b c : C).
Local Hint Resolve
(closure G) (ein G) (lid G) (rid G) (invin G) (linv G) (rinv G)
              : grp.
Local Hint Rewrite @assoc : grp.
Local Notation carrier := (carrier G).
Local Notation assoc := (assoc G).
Local Notation op := (op G).
Local Notation e := (e G).
Local Notation inv := (inv G).
Local Notation linv := (linv G).
Local Notation rinv := (rinv G).
Local Notation lid := (lid G).
Local Notation rid := (rid G).
Local Notation l_ident := (l_ident op).
Local Notation r_ident := (r_ident op).

Hypothesis Ga : a ∈ carrier.
Hypothesis Gb : b ∈ carrier.
Hypothesis Gc : c ∈ carrier.
Local Infix "@" := op (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).

Definition H_triv : @Group C.
Proof with atg.
  refine (mkgroup
    (fun x => x = e)
    op e inv
    _ _ _ _ _ _ _ _
  )...
  - intros x y -> ->. rewrite lid...
  - intros x y z -> -> ->.
    repeat rewrite lid...
  - intros x _ ->...
  - intros x _ ->...
  - intros x ->...
    rewrite e_own_inv...
  - intros x ->...
  - intros x ->...
Defined.

Theorem trivial_sg_con : H_triv ≤ G.
Proof with auto.
  split... intros x ->. exact G.(ein).
Qed.



Definition H_a : @Group C.
Proof with atg.
  refine (mkgroup
    (fun x => x ∈ carrier /\ x @ a = a @ x)
    op e inv
    _ _ _ _ _ _ _ _
  ).
  - intros x y [Gx xac] [Hy yac]; split.
    + apply closure...
    + rewrite assoc, yac, <- assoc,
      xac, assoc...
  - intros x y z [Gx _] [Gy _] [Gz _].
    apply assoc...
  - split... rewrite lid, rid...
  - intros x _ [Gx _] . rewrite lid...
  - intros x _ [Gx _]. rewrite rid...
  - intros x [Gx xac]. split...
    apply (@left_can C G x)...
    repeat rewrite <- assoc...
    rewrite rinv, lid, xac, assoc,
            rinv, rid...
  - intros x [Gx _]. apply linv...
  - intros x [Gx _]. apply rinv...
Defined.

Theorem comm_around_a_subgroup_con: H_a ≤ G.
Proof with auto.
  split... + intros x [Gx _]...
Qed.

Definition H_S : @Group C.
Proof with atg.
  refine (mkgroup
    (fun x => x ∈ carrier /\ ∀ S s (Sub:S ⊆ carrier) (Ss:s ∈ S),
                              x @ s = s @ x )
    op e inv
    _ _ _ _ _ _ _ _
  ).
  - intros x y [Gx Sxc] [Gy Syc].
    split... intros **.
    specialize (Sxc S s Sub Ss).
    specialize (Syc S s Sub Ss).
    rewrite assoc, Syc, <- assoc, Sxc,
    assoc...
  - intros x y z [Gx _] [Gy _] [Gz _].
    apply assoc...
  - split... intros **. rewrite lid, rid...
  - intros x _ [Gx _]. rewrite lid...
  - intros x _ [Gx _]. rewrite rid...
  - intros x [Gx Sxc]. split... intros **.
    apply (@left_can C G x)...
    repeat rewrite <- assoc...
    rewrite rinv, (Sxc _ _ Sub Ss),
    lid, assoc, rinv, rid...
  - intros x [Gx _]. rewrite linv...
  - intros x [Gx _]. rewrite rinv...
Defined.

Theorem comm_around_all_subsets_subgroup_con : H_S ≤ G.
Proof with auto.
  split... + intros x [Gx _]...
Qed.








End semiconcreteSG.

Section twoG.
Context {C D : Type}.
Context {G: @Group C} {H: @Group D}.
Variable (g g1 g2: C) (h h1 h2: D).
Local Hint Resolve
  (closure G) (ein G) (lid G) (rid G)
  (invin G) (linv G) (rinv G)
  (closure H) (ein H) (lid H) (rid H)
  (invin H) (linv H) (rinv H)
: grp.

(* Local Notation carrier := (carrier G).
Local Notation op := (op G).
Local Notation assoc := (assoc G).
Local Notation e := (e G).
Local Notation linv := (linv G).
Local Notation rinv := (rinv G).
Local Notation lid := (lid G).
Local Notation rid := (rid G).
Local Notation l_ident := (l_ident op).
Local Notation r_ident := (r_ident op). *)
Local Notation idempotent := (idempotent carrier op).
Local Notation order2 := (order2 carrier op e).

Hypothesis Gg : g  ∈ G.(carrier).
Hypothesis G1 : g1 ∈ G.(carrier).
Hypothesis G2 : g2 ∈ G.(carrier).
Hypothesis Hh : h  ∈ H.(carrier).
Hypothesis H1 : h2 ∈ H.(carrier).
Hypothesis H2 : h1 ∈ H.(carrier).

Local Infix "@" := G.(op) (at level 20, left associativity).
Local Infix "+" := H.(op) (at level 50, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).
Local Notation "a '!'" := (inv H a) (at level 2, left associativity).

Open Scope group_scope.

Variable (f: isomorphism G H).

Theorem iso_preserves_id : ((f: fn) G.(e)) = H.(e).
Proof with atg.
  diso f. destruct (sur H.(e) H.(ein)) as [eG [GeG X]].
  pose proof (sp G.(e) eG) as Z. rewrite G.(lid) in Z...
  rewrite X in Z at 2. rewrite H.(rid) in Z...
  apply inj in Z... rewrite <- Z...
Qed.

Theorem iso_preserves_inv : (f:fn) g ' = ((f:fn) g) !.
Proof with atg.
  diso f. apply (left_can H (f g))...
  rewrite <- sp, rinv, rinv...
  destruct (sur H.(e) H.(ein)) as [eG [GeG X]].
  pose proof (sp G.(e) eG) as Z. rewrite G.(lid) in Z...
  rewrite X in Z at 2. rewrite H.(rid) in Z...
  apply inj in Z... rewrite <- Z...
Qed.

Theorem g_conjugate_iso : is_Isomorphism G G (fun x => g @ x @ g ').
Proof with atg.
    assert (is_Homomorphism G G (λ x : C, g @ x @ g ')). {
      split.
      - intros x Gx. apply closure...
      - intros a b Ga Gb.
        rewrite (assoc G (g@a)), <- (assoc G (g ')),
                <- (assoc G (g ')), linv, lid...
        repeat rewrite assoc...
    }
  exists H0.
    assert (is_Homomorphism G G (fun x => g ' @ x @ g)). {
      split. - intros x Gx. apply closure...
      - intros **. rewrite (assoc G (g '@a)),
                   <- (assoc G (g)),
                   <- (assoc G (g)), rinv, lid...
        repeat rewrite assoc...
    }
  exists (mkhomo _ _ H3). split.
  - intros x Gx. simpl.
    repeat rewrite assoc...
    rewrite linv, rid, <- assoc, linv...
  - intros x Gx. simpl.
    repeat rewrite assoc...
    rewrite rinv, rid, <- assoc, rinv...  
Qed.


Theorem bill : is_Isomorphic G G.
Proof with atg.
  assert (is_Homomorphism G G (fun x => x)).
  split... intros x... 
  assert (is_Isomorphism G G (fun x => x)). {
  exists H0.
  unfold Bijective. exists (mkhomo _ _ H0).
  split; intros ? ?... }
  
  exists (mkiso _ _ H3).
  
  unfold is_Isomorphism.


End twoG.