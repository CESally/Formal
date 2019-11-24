Require Import Defns.

Module Trivialities.
Include Defns.Groups.
Open Scope group_scope.
Section top.
Context {C : Type}.
Variable (G: @Group C).
Variable (a b c (* id *): C).
Hint Resolve (closure G) ein (invin G) (linv G) (rinv G)
             (lid G) (rid G): grp.
Hint Rewrite @assoc : grp.

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
Local Notation idempotent := (idempotent carrier op).
Local Notation order2 := (order2 carrier op e).

Hypothesis Ga : a ∈ carrier.
Hypothesis Gb : b ∈ carrier.
Hypothesis Gc : c ∈ carrier.
(* Hypothesis Gi : id ∈ carrier. *)

Local Infix "@" := op (at level 20, left associativity).
Local Notation "a '''" := (inv G a) (at level 2, left associativity).

Theorem left_can : forall z x y, 
  z ∈ carrier ->
  x ∈ carrier ->
  y ∈ carrier ->
  z @ x = z @ y -> x = y.
Proof with atg.
  intros * Gz Gx Gy H.
  rewrite <- lid, <- (lid y)...
  rewrite <- (linv z)...
  repeat rewrite assoc...
  rewrite H...
Qed.

Theorem right_can : forall z x y, 
  z ∈ carrier ->
  x ∈ carrier ->
  y ∈ carrier ->
  x @ z = y @ z -> x = y.
Proof with atg.
  intros * Gz Gx Gy H.
  rewrite <- rid, <- (rid y)...
  rewrite <- (rinv z)...
  repeat rewrite <- assoc...
  rewrite H...
Qed.

Theorem x_is_own_inv : forall x, x ∈ carrier -> x ' ' = x.
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

Theorem inv_of_op : (a @ b) ' = b ' @ a '.
Proof with atg.
  apply (left_can (a @ b))...
  symmetry;
  rewrite rinv,
          <- assoc,
          (assoc a),
          rinv,
          rid...
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

Goal (a @ b) ' = a ' @ b ' <-> a @ b = b @ a.
Proof with atg.
  split; intros H.
  - pose proof inv_of_op.
    apply (left_can (a '))...
    rewrite <- assoc, linv, lid...
    apply (right_can (a '))...
    repeat rewrite assoc...
    rewrite rinv, rid...
    apply (left_can (b '))...
    rewrite <- assoc, linv, lid,
            <- assoc, <- H0, H,
            assoc, linv, rid...
  - rewrite inv_of_op.
    
  



End top.
End Trivialities.