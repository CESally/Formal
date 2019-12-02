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
Local Notation left_can := (left_can G).
Local Notation right_can := (right_can G).
Hypothesis Ga : a ∈ G.
Hypothesis Gb : b ∈ G.
Hypothesis Gc : c ∈ G.
Local Infix "@" := op (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).


(* Theorem rep_aux_in : ∀ {x p} {Gx: x ∈ G},
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
Admitted. *)



Theorem idem__ident : ∀ x, x ∈ G ->
  (idempotent x) -> ident x.
Proof with atg.
  intros ? ? [Gx idem] y Gy. split.
  - apply (left_can x)...
    rewrite <- assoc, idem...
  - apply (right_can x)...
    rewrite assoc, idem...
Qed.

Theorem idem__ident2 : ∀ x, x ∈ G ->
  (idempotent x) -> ident x.
Proof with atg.
  intros * Gx [_ idem].
  rewrite (e_is_lunique_sol_gg G x x)...
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
  intros o2 x y Gx Gy.
  apply (left_can x), (right_can y)...
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

Theorem stupid :
  a @ b @ c = e -> b @ c @ a = e.
Proof with atg.
  intros. apply (right_can a ')...
  rewrite assoc, rinv, rid, lid...
    assert (a = c ' @ b ') as ->. {
      apply (right_can b)...
      rewrite assoc, linv, rid...
      apply (right_can c)...
      rewrite linv... }
  rewrite inv_of_op, xii__x, xii__x...
Qed.

End elementary.

ab_squared__comm

Section subgroups2.
Context {C : Type}.
Context {K H G: @ Group C}.
Local Hint Resolve
(closure K) (lid K) (rid K) (invin K) (linv K) (rinv K)
(closure H) (lid H) (rid H) (invin H) (linv H) (rinv H)
(closure G) (lid G) (rid G) (invin G) (linv G) (rinv G)
              : grp.
Local Hint Rewrite @assoc : grp.

Variable (a b c : C).
Local Infix "@" := G.(op) (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).




Lemma intersection_preserves_sgness : K ≤ G -> H ≤ G ->
  is_Subgroup_of G (fun x => x ∈ H /\ x ∈ K).
Proof with eatg.
  intros KsgG HsgG. ef_sg KsgG KiG sok.
   ef_sg HsgG HiG soh. is_.
  - intros x [Hx Kx]...
  - intros x y [Hx Kx] [Hy Ky].
    split;[rewrite <- soh|rewrite <- sok];
    apply closure...
  - split; erewrite <- (subgroup_has_same_e)...
  - intros x [Hx Kx]. split;
    erewrite <- subgroup_has_same_invs...
Qed.



Theorem comm_around_a_subgroup : a ∈ G ->
is_Subgroup_of G (fun x => x ∈ G /\ x @ a = a @ x).
Proof with atg.
  intros Ga. is_.
  - intros x [Gx _]...
  - intros x y [Gx xac] [Hy yac]; split.
    + apply closure...
    + rewrite assoc, yac, <- assoc,
      xac, assoc...
  - split... rewrite lid, rid...
  - intros x [Gx xac]. split...
    apply (@left_can C G x)...
    repeat rewrite <- assoc...
    rewrite rinv, lid, xac, assoc,
            rinv, rid...
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
(closure H) (lid H) (rid H) (invin H) (linv H) (rinv H)
(closure G) (lid G) (rid G) (invin G) (linv G) (rinv G)
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

Hypothesis Gg : g  ∈ G.
Hypothesis G1 : g1 ∈ G.
Hypothesis G2 : g2 ∈ G.
Hypothesis Hh : h  ∈ H.
Hypothesis H1 : h2 ∈ H.
Hypothesis H2 : h1 ∈ H.

Local Infix "@" := G.(op) (at level 20, left associativity).
Local Infix "+" := H.(op) (at level 50, left associativity).
Local Notation "a '''" := (inv G a) (at level 12, left associativity).
Local Notation "a '!'" := (inv H a) (at level 12, left associativity).

Open Scope group_scope.

Variable (f: isomorphism G H).

Theorem iso_preserves_id : ((f: fn) G.(e)) = H.(e).
Proof with atg.
  diso f.
  destruct (sur H.(e) H.(ein)) as [eG [GeG X]].
  pose proof (sp G.(e) eG) as Z.
  rewrite lid, X, rid in Z...
  rewrite Z...
Qed.

Theorem iso_preserves_inv : (f:fn) (g ') = ((f:fn) g) !.
Proof with atg.
  diso f. apply (left_can H (f g))...
  rewrite <- sp, rinv, rinv...
  destruct (sur H.(e) H.(ein)) as [eG [GeG X]].
  pose proof (sp G.(e) eG) as Z.
  rewrite lid, X, rid in Z...
  rewrite Z...
Qed.

Theorem conjugate_g__is_iso : is_Isomorphism G G (fun x => g @ x @ g ').
Proof with atg.
  is_.
  - intros x Gx. apply closure...
  - intros **. rewrite (G.(assoc) (g@a) (g '))
    , <- (G.(assoc) (g '))
    , <- (G.(assoc) (g ')), linv, lid...
    repeat rewrite assoc...
  - exists (λ x : C, g ' @ x @ g). split;split;intros **.
    + intros x Gx.   apply closure...
    + rewrite (G.(assoc) (g '@a) (g))
      , <- (G.(assoc) g)
      , <- (G.(assoc) g), rinv, lid...
      repeat rewrite assoc...
    + repeat rewrite assoc...
      rewrite linv, rid, <- assoc, linv...
    + repeat rewrite assoc...
      rewrite rinv, rid, <- assoc, rinv...
Qed.




End twoG.