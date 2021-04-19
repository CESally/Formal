Require Import List.

Theorem MasterOfInduction: forall (X:Type) (x:X)
 (L : list (nat * X)) n ,
 (nth_error L n  = Some (n, x)) ->
  nth_error (map snd L) n = Some x.
Proof with auto.
  intros *. generalize n at 2 as m.
  intros m. revert n.
  induction L as [| [e1 e2] L IH], n; simpl;
  [ inversion 1
  | inversion 1
  | injection 1 as -> ->
  | ]...
Qed.

Inductive Tree : Set :=
  | Leaf : Tree
  | Node : Tree -> Tree -> Tree.



(* Inductive left_skewed : Tree -> Prop :=
  | lsL : left_skewed Leaf
  | lsN : forall tll tlr tr,
          left_skewed tll ->
          left_skewed tlr ->
          left_skewed tr  ->
          left_skewed (Node (Node tll tlr) tr).

Inductive right_skewed : Tree -> Prop :=
  | rsL : right_skewed Leaf
  | rsN : forall tl trl trr,
          right_skewed tl ->
          right_skewed trl ->
          right_skewed trr ->
          right_skewed (Node tl (Node trl trr)).

Fixpoint deep_swap (t: Tree) :=
  match t with
  | Leaf     => t
  | Node l r => Node (deep_swap r) (deep_swap l)
  end.


Lemma swap_skew :
  forall t, left_skewed t -> right_skewed (deep_swap t).
Proof with auto.
  induction 1; simpl. left. right...
Qed. *)



Fixpoint left_skewed (t : Tree) : Prop :=
  match t with
    | Leaf => True
    | Node (Node t11 t12) t2 => 
            left_skewed t11 /\ left_skewed t12 /\ left_skewed t2
    | _ => False
  end.

Fixpoint right_skewed (t : Tree) : Prop :=
  match t with
    | Leaf => True
    | Node t1 (Node t21 t22) => 
            right_skewed t1 /\ right_skewed t21 /\ right_skewed t22
    | _ => False
  end.

Fixpoint deep_swap (t: Tree) :=
  match t with
  | Leaf     => t
  | Node l r => Node (deep_swap r) (deep_swap l)
  end.


Lemma left_skewed_ind : forall P : Tree -> Prop,
  P Leaf ->
  (forall tll tlr tr,
  left_skewed tll -> P tll ->
  left_skewed tlr -> P tlr ->
  left_skewed tr  -> P tr  ->
  P (Node (Node tll tlr) tr)) ->
  forall t, left_skewed t -> P t.
Proof with auto.
  intros ? A B. induction t as [| [|tll tlr] IHl tr IHr]; simpl...
  inversion 1.
  - intros [X [Y Z]]. apply B...
Qed.


Lemma swap_skew :
  forall t, left_skewed t -> right_skewed (deep_swap t).
Proof with auto.
  induction 1.





Qed.