(* Author : CESally *)
Require Import Defns ZArith_base.
Open Scope group_scope.
Open Scope Z.

Print Module BinIntDef.Z.
Print Module ZArith.BinInt.
Include ZArith.BinInt.Z.


Lemma intsWplus : @Group Z.
Proof with auto with grp.
  refine (@mkgroup
    Z
    (fun x => True)
    add
    0
    opp
    (fun _ _ _ _ => I)
    _
    I
    _ _ _ _ _
  ).
  - intros x y z _ _ _.
    apply Zplus_assoc_reverse.
  - simpl...
  - intros []...
  - intros x _...
  - intros [] ?; try apply pos_sub_diag...
  - intros [] ?; try apply pos_sub_diag...
Defined.

Hint Unfold intsWplus : grp.

Lemma evenIntsWplus: @Group Z.
Proof with auto with grp.
  refine (@mkgroup
    Z
    (fun x => Even x)
    add
    0
    opp
    _
    _
    _ _ _ _ _ _
  ).
  - intros x y [hx ->] [hy ->].
    exists (hx + hy).
    destruct hx, hy; simpl...
  - intros x y z _ _ _.
    apply Zplus_assoc_reverse.
  - exists 0...
  - simpl...
  - intros []...
  - intros x [hx ->].
    exists (- hx).
    destruct hx; simpl...
  - intros [] ?; try apply pos_sub_diag...
  - intros [] ?; try apply pos_sub_diag...
Defined.

Example evens_sg_intsWplus_con :
  evenIntsWplus ≤ intsWplus.
Proof with atg.
  constructor...
  -  intros x _; simpl...
Qed.

Example even_sg_intsWplus :
  is_Subgroup_of intsWplus (fun x => Even x).
Proof with atg.
  is_...
  - intros x [hx ->]. exact I.
  - intros x y [hx ->] [hy ->].
    exists (hx + hy).
    destruct hx, hy; simpl...
  - exists 0...
  - intros x [hx ->].
    exists (- hx).
    destruct hx; simpl...
Qed.

Close Scope group_scope.
Close Scope Z.