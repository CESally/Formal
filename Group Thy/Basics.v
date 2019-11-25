Require Import Defns.
Import Pos.


Open Scope group_scope.
Section oneG.
Context {C : Type}.
Variable (G: @Group C).
Variable (a b c (* id *): C).
Local Hint Resolve (closure G) ein (invin G) (linv G) (rinv G)
             (lid G) (rid G): grp.
Local Hint Rewrite @assoc : grp.

Local Notation carrier := (carrier G).
Local Notation op := (op G).
Local Notation assoc := (assoc G).
Local Notation e := (e G).
Local Notation linv := (linv G).
Local Notation rinv := (rinv G).
Local Notation lid := (lid G).
Local Notation rid := (rid G).
Local Notation l_ident := (l_ident op).
Local Notation r_ident := (r_ident op).
Local Notation rep_aux := (rep_aux G).
Local Notation idempotent := (idempotent carrier op).
Local Notation order2 := (order2 carrier op e).

Hypothesis Ga : a ∈ carrier.
Hypothesis Gb : b ∈ carrier.
Hypothesis Gc : c ∈ carrier.
(* Hypothesis Gi : id ∈ carrier. *)

Local Infix "@" := op (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).

Theorem left_can : forall z {x y},
  x ∈ carrier ->
  y ∈ carrier ->
  z ∈ carrier ->
  z @ x = z @ y -> x = y.
Proof with atg.
  intros * Gz Gx Gy H.
  rewrite <- lid, <- (lid y)...
  rewrite <- (linv z)...
  repeat rewrite assoc...
  rewrite H...
Qed.

Theorem right_can : forall z {x y},
  x ∈ carrier ->
  y ∈ carrier ->
  z ∈ carrier ->
  x @ z = y @ z -> x = y.
Proof with atg.
  intros * Gz Gx Gy H.
  rewrite <- rid, <- (rid y)...
  rewrite <- (rinv z)...
  repeat rewrite <- assoc...
  rewrite H...
Qed.

Theorem e_own_inv : e ' = e.
Proof with atg.
  apply (left_can e)...
  rewrite rinv, lid...
Qed.

Theorem xii__x : forall x, x ∈ carrier -> x ' ' = x.
Proof with atg.
  intros **. apply (left_can (x '))...
  rewrite rinv, linv...
Qed.

Theorem id_unique : ∀ id, id ∈ carrier -> ident carrier op id -> id = e.
Proof with atg.
  intros **. destruct (H0 e)...
  apply (left_can e)...
  symmetry; rewrite H2...
Qed.

Theorem inv_unique : ∀ a', a' ∈ carrier -> a' @ a = e -> a @ a' = e ->
  a' = a '.
Proof with atg.
  intros **. apply (left_can a)...
  symmetry; rewrite H1...
Qed.

Theorem inv_of_op : ∀ x y
  (Gx: x ∈ carrier)
  (Gy: y ∈ carrier),
  (x @ y) ' = y ' @ x '.
Proof with atg.
  intros **.
  apply (left_can (x @ y))...
  symmetry;
  rewrite rinv,
          <- assoc,
          (assoc x),
          rinv,
          rid...
Qed.

Theorem rep_aux_in : ∀ {x p} {Gx: x ∈ carrier},
  rep_aux x p ∈ carrier.
Proof with auto.
  intros **. unfold rep_aux.
  apply iter_invariant;[| exact G.(ein)].
  intros **. apply closure...
Qed.

Theorem rep_in : ∀ i, @rep C G a i ∈ carrier.
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
  destruct i; simpl.
  - exact e_own_inv.
  - induction p. 3:{
    unfold rep_aux. simpl.
    repeat rewrite rid...
    apply invin... }
    +
 unfold rep_aux in *. simpl.
  rewrite inv_of_op.
  rewrite <- IHp.
      apply iter_invariant.
intros **. rewrite <- H.

  simpl.

Qed.



Theorem idem__ident : ∀ x, x ∈ carrier -> (idempotent x) -> ident carrier op x.
Proof with atg.
  intros ? ? [Gx idem] y Gy. split.
  - apply (left_can x)...
    rewrite <- assoc, idem...
  - apply (right_can x)...
    rewrite assoc, idem...
Qed.

Theorem idem__unique : ∀ x y,
  x ∈ carrier ->
  y ∈ carrier ->
  (idempotent x) ->
  (idempotent y) -> x = y.
Proof with atg.
  intros.
  apply idem__ident, id_unique in H1...
  apply idem__ident, id_unique in H2...
  rewrite H1, H2...  
Qed.

Theorem lunique_sol: exists! x, x ∈ carrier /\ x @ a = b.
Proof with atg.
  exists (b @ a '); split.
  - split... rewrite assoc, linv...
  - intros ? []. rewrite <- H0, assoc, rinv...
Qed.

Theorem runique_sol: exists! x, x ∈ carrier /\ a @ x = b.
Proof with atg.
  exists (a ' @ b); split.
  - rewrite <- assoc, rinv...
  - intros ? []. rewrite <- H0, <- assoc, linv...
Qed.

Theorem order2__abelian : (∀ x, order2 x) -> is_comm carrier op.
Proof with atg.
  intros o2 x y Gx Gy. apply (left_can x), (right_can y)...
  repeat rewrite <- assoc...
  pose proof (o2 x) as [_ o2x].
  pose proof (o2 y) as [_ o2y].
  pose proof (o2 (x@y)) as [_ o2xy].
  rewrite o2x, lid, o2y, (assoc (x@y))...
Qed.

Theorem inv_comm__abelian : (a @ b) ' = a ' @ b ' <-> a @ b = b @ a.
Proof with atg.
  rewrite inv_of_op. split; intros H.
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

End oneG.

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
(* Section isomorphism. *)
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



End twoG.









End Trivialities.








Local Open Scope Z_scope.



Local Open Scope positive_scope.



Theorem rep_i_j__ij : forall (i j: Z), rep i @ rep j = rep (i + j).
Proof with eauto.
  pose proof G.(ein). pose proof rep_in.
  pose proof @rep_aux_in.
  destruct i;[intros; simpl; rewrite G.(lid);auto| |];
  destruct j; simpl; try rewrite G.(rid)...
  3:{ apply H2. apply invin... }
  - unfold rep_aux. apply iter_invariant.
    + intros x A. rewrite assoc...
      rewrite A. 
  -
  -
  - 

 destruct i, j; intros *;
  simpl; try progress [rewrite G.(lid) | ; auto; try eapply rep_aux_in]. -
  rewrite G.(lid);auto; try eapply rep_aux_in.
  eapply rep_aux_in.
  - simpl. rewrite G.(lid)...

  - unfold rep.
  
  induction i as [|i IHi]; simpl; intros j.
  - rewrite lid... apply rep_in.
  - rewrite <- IHi. apply assoc; try apply rep_in.
    destruct b... apply invin...
Qed.

Theorem rep_i_j__ij : for

Theorem cyclicSG : is_Group
  (fun x => x ∈ G.(carrier) /\ exists n, rep n = x)
  G.(op)
  G.(e)
  G.(inv).
Proof with auto.
  split;[|split;[|split;[|split;[|split;[|split;[|split]]]]]].
  - intros x y [Gx [i gi]] [Gy [j gj]]. split.
    + apply closure...
    + exists (i + j). rewrite <- rep_i_j__ij.
      subst...
  - intros x * [Gx _] [Gy _] [Gz _].
    apply assoc...
  - split;[exact G.(ein) | exists 0]...
  - intros x [Gx _]. rewrite G.(lid)...
  - intros x [Gx _]. rewrite G.(rid)...
  - intros x [Gx [i gi]]. split.
    + apply G.(invin)...
    + .
  - intros x [Gx _]. apply G.(linv)...
  - intros x [Gx _]. apply G.(rinv)...
Qed.
    
    
    
  do 2 split. 2: split.
  3: split.
4: split.
5: split. admit. admit. admit. admit. admit.
split. admit. split.
3:{ split.

 2: split.
  repeat split.
  
  apply closure. 
  unfold In in H0.
Qed.

