Require Import Defns ZArith_base.
Open Scope group_scope.
Open Scope Z.

Print Module BinIntDef.Z.
Print Module ZArith.BinInt.
Include ZArith.BinInt.Z.


Lemma intsWplus : Group Z.
Proof with auto with grp.
  refine (@mkgroup
    Z
    (fun x => True)
    add
    0
    opp
    (fun _ _ _ _ => I)
    Zplus_assoc_reverse
    I
    _ _ _ _ _
  ).
  - simpl...
  - intros []...
  - intros x _...
  - intros []; try apply pos_sub_diag...
  - intros []; try apply pos_sub_diag...
Defined.

Lemma evenIntsWplus: Group Z.
Proof with auto with grp.
  refine (@mkgroup
    Z
    (fun x => Even x)
    add
    0
    opp
    _
    Zplus_assoc_reverse
    _ _ _ _ _ _
  ).
  - intros x y [hx ->] [hy ->].
    exists (hx + hy).
    destruct hx, hy; simpl...
  - exists 0...
  - simpl...
  - intros []...
  - intros x [hx ->].
    exists (- hx).
    destruct hx; simpl...
  - intros []; try apply pos_sub_diag...
  - intros []; try apply pos_sub_diag...
Defined.

Example evens_sg_intsWplus:
  evenIntsWplus ≤ intsWplus.
Proof with auto with grp.
  constructor...
  -  intros x _; simpl...
Qed.

Close Scope group_scope.
Close Scope Z.