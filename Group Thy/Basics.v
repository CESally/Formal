Require Import Notions.



Require Import Defns.

Module Trivialities.
Include Defns.Groups.
Open Scope group_scope.
Section top.
Context {C : Type}.
Variable (G: @Group C).


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



Variable (a b c  id: C).
Hypothesis Ga : a ∈ carrier.
Hypothesis Gb : b ∈ carrier.
Hypothesis Gc : c ∈ carrier.
Hypothesis Gi : id ∈ carrier.
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

Theorem id_unique : ident carrier op id -> id = e.
Proof with atg.
  intros H. destruct (H e)...
  apply (left_can e)...
  symmetry; rewrite H1...
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


Theorem order2__comm : ∀ (x_sq: ∀ x, x @ x = e), a @ b = b @ a.
Proof with atg.
  intros **. apply (left_can a), (right_can b)...
  repeat rewrite <- assoc...
  rewrite x_sq, lid, x_sq, (assoc (a@b))...
Qed.

Theorem unit_power__ident : ∀ x, x ∈ carrier -> x @ x = x -> ident carrier op x.
Proof with atg.
  intros ** y ?. split.
  - apply (left_can x)...
    rewrite <- assoc, H0...
  - apply (right_can x)...
    rewrite assoc, H0...
Qed.

End top.
End Trivialities.