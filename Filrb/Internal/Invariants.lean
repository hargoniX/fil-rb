import Filrb.Internal.Raw

/-!
This module defines the red black tree invariants and proves that the mutating operations on
red black trees preserve these invariants.
-/

namespace Filrb
namespace Internal

variable [Preorder α] [Ord α] [LawfulOrd α]

namespace LawfulOrd

@[simp]
theorem compare_eq_lt {x y : α} : compare x y = .lt ↔ x < y := by
  have := LawfulOrd.compares x y
  match h : compare x y with
  | .lt => simp_all
  | .eq => simp_all
  | .gt =>
    simp only [h, Ordering.compares_gt, gt_iff_lt, reduceCtorEq, false_iff, not_lt, ge_iff_le] at *
    apply le_of_lt
    assumption

@[simp]
theorem compare_eq_eq {x y : α} : compare x y = .eq ↔ x = y := by
  have := LawfulOrd.compares x y
  match h : compare x y with
  | .lt =>
    simp only [h, Ordering.compares_lt, reduceCtorEq, false_iff, ne_eq] at *
    exact ne_of_lt this
  | .eq => simp_all
  | .gt =>
    simp only [h, Ordering.compares_gt, gt_iff_lt, reduceCtorEq, false_iff, ne_eq] at *
    exact ne_of_gt this

@[simp]
theorem compare_eq_gt {x y : α} : compare x y = .gt ↔ y < x := by
  have := LawfulOrd.compares x y
  match h : compare x y with
  | .lt =>
    simp only [h, Ordering.compares_lt, reduceCtorEq, false_iff, not_lt, ge_iff_le] at *
    apply le_of_lt
    assumption
  | .eq => simp_all
  | .gt => simp_all

end LawfulOrd

namespace Raw

/--
A tree is a binary search tree.
-/
inductive BST : Raw α → Prop where
  | nil : BST .nil
  | node (hleft1 : ∀ x ∈ left, x < data) (hleft2 : BST left)
         (hright1 : ∀ x ∈ right, data < x) (hright2 : BST right) : BST (.node left data color right)

theorem bst_insert_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.insert x) := sorry
theorem bst_erase_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.erase x) := sorry

/--
The child invariant for red black trees: Red nodes must have black children.
-/
inductive ChildInv : Raw α → Prop where
  | nil : ChildInv .nil
  | black (hleft : ChildInv left) (hright : ChildInv right) : ChildInv (.node left data .black right)
  | red (hleft1 : ChildInv left) (hleft2 : left.rootColor = .black) (hright1 : ChildInv right)
        (hright2 : right.rootColor = .black) : ChildInv (.node left data .red right)

theorem childInv_insert_of_bst (x : α) (t : Raw α) (h : ChildInv t) : ChildInv (t.insert x) := sorry
theorem childInv_erase_of_bst (x : α) (t : Raw α) (h : ChildInv t) : ChildInv (t.erase x) := sorry

/- Lemmas for balanced deletion, somehow they make use of baliL and baliR? -/
--lemma eight_four :
--    (invh l ∧ invh r ∧ bh l + 1 = bh r ∧ invc2 l ∧ invc r ∧ t' = baldL l a r) →
--    (invh t' ∧ bh t' = bh r ∧ invc2 t' ∧ (color r = Black → invc t')) := by sorry

--lemma eight_five :
--    (invh l ∧ invh r ∧ bh l = bh r + 1 ∧ invc l ∧ invc2 r ∧ t' = baldR l a r) →
--    (invh t' ∧ bh t' = bh l ∧ invc2 t' ∧ (color l = Black αrrow invc t')) := by sorry

/- Those make use of baldL and baldR -/
--lemma eight_one :
--    (split_min t = (x, t') ∧ t ≠ Raw.nil ∧ invh t ∧ invc t) →
--    (invh t' ∧ (color t = Red → bh t' = bh t ∧ invc t') ∧
--    (color t = Black → bh t' = (bh t -1) ∧ invc2 t')) := by sorry

--lemma eight_two :
--  (invh t ∧ invc t ∧ t' = erase x t) →
--  (invh t' ∧
--    (color t = Red → bh t' = bh t ∧ invc t') ∧
--    (color t = Black → bh t' = bh t -1 ∧ invc2 t')) := by sorry

-- what does it mean that something is a rbt? should be invariants no?
--lemma eight_three : rbt t → rbt (erase x t) := by sorry

def ChildInv2 (t : Raw α) : Prop :=
  match t with
  | nil => ChildInv t
  | node _ _ .black _ => ChildInv t
  | node l x .red r => ChildInv (.node l x .black r)

def blackHeightLeft (t : Raw α) : Nat :=
  match t with
  | .nil => 0
  | .node left _ color _ =>
    match color with
    | .black => blackHeightLeft left + 1
    | .red => blackHeightLeft left

/--
The height invariant for red black trees: Every path from a given node to any of its leaves goes
through the same number of black nodes.

The particular variant here is based on
[Functional Algorithms Verified](https://functional-algorithms-verified.org/functional_data_structures_algorithms.pdf)
and uses a sufficient condition instead of directly encoding the above.
-/
inductive HeightInv : Raw α → Prop where
  | nil : HeightInv .nil
  | node (hleft : HeightInv left) (hright : HeightInv right)
         (h : left.blackHeightLeft = right.blackHeightLeft) : HeightInv (.node left data color right)

theorem heightInv_insert_of_bst (x : α) (t : Raw α) (h : HeightInv t) : HeightInv (t.insert x) := sorry
theorem heightInv_erase_of_bst (x : α) (t : Raw α) (h : HeightInv t) : HeightInv (t.erase x) := sorry

end Raw
end Internal
end Filrb
