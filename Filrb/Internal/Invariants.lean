import Filrb.Internal.Raw
import Mathlib.Data.Nat.Log

/-!
This module defines the red black tree invariants and proves that the mutating operations on
red black trees preserve these invariants.
-/

namespace Filrb
namespace Internal

namespace Raw

variable [Preorder α] [Ord α] [LawfulOrd α]

/--
A tree is a binary search tree.
-/
inductive BST : Raw α → Prop where
  | nil : BST .nil
  | node (hleft1 : ∀ x ∈ left, x < data) (hleft2 : BST left)
         (hright1 : ∀ x ∈ right, data < x) (hright2 : BST right) : BST (.node left data color right)

omit [Ord α] [LawfulOrd α] in
theorem bst_nil : BST (.nil : Raw α) := BST.nil


omit [Ord α] [LawfulOrd α] in
theorem bst_color_independent {l r : Raw α} (h : BST (.node l d c r)) : BST (.node l d c' r) := by
  cases h
  apply BST.node <;> assumption

omit [Ord α] [LawfulOrd α] in
theorem bst_paintColor_of_bst (c : Color) (t : Raw α) (h : BST t) : BST (t.paintColor c) := by
  unfold paintColor
  split
  . assumption
  . apply bst_color_independent h

/- change of color won't change the membership of its nodes-/
lemma node_color_independent (x d : α) (l r : Raw α) (h: x ∈ l.node d .black r) : x ∈ l.node d .red r := by
  cases h
  · apply Mem.here
  · apply Mem.left; assumption
  · apply Mem.right; assumption

/- the balance-left operation preserves the bst property-/
theorem bst_baliL_bst (tl tr : Raw α) (hl : BST tl) (hr : BST tr) (Hl : ∀ x ∈ tl, x < d) (Hr : ∀ x ∈ tr, d < x) : BST (baliL d tl tr) := by
      unfold baliL
      split
      · next hx1 hx ht1 hd1 ht2 hd2 ht3 => cases hl /- left-balance variant 1.-/
                                           next hleft2 hleft1 hright2 hright1 =>
                                            apply BST.node
                                            · intro x hx
                                              apply hleft1
                                              apply node_color_independent; assumption
                                            · apply bst_color_independent hleft2
                                            · intro x hx
                                              cases hx
                                              · apply Hl; apply Mem.here
                                              · next hright2 => apply hright1; apply hright2
                                              · next hright3 => have h : x ∈ tr := by apply hright3
                                                                apply lt_trans _ (Hr x h)
                                                                apply Hl; apply Mem.here
                                            · apply BST.node
                                              · intro x hx
                                                apply (Hl  x (by sorry))-- hint : ht3 is the left tree of root d
                                              · assumption
                                              · intro x hx
                                                apply Hr x; assumption
                                              · assumption
      · next x1 x2 t1 d1 t2 d2 t3 hx => cases hl /- left-balance variant 2.-/
                                        next hleft2 hleft1 hright2 hright1 =>
                                          apply BST.node
                                          · sorry--hint: after rotation, the left tree is smaller than the root
                                          · sorry--hint: after rotation, the left tree is still a bst
                                          · sorry--hint: after rotation, the right tree is bigger than the root
                                          · sorry--hint: after rotation, the right tree is still a bst
      · next h1 h2 h3 h4 => apply BST.node
                            · intro x hx
                              sorry --hint: left tree is smaller than root
                            · assumption
                            · intro x hx
                              sorry --hint: right tree is bigger than root
                            · assumption

/- the balance-right operation preserves the bst property-/
lemma bst_baliR_bst (tl tr : Raw α) (hl : BST tl) (hr : BST tr) (d : α) (Hl : ∀ x ∈ tl, x < d) (Hr : ∀ x ∈ tr, d < x) : BST (baliR d tl (ins d tr)) := by sorry

/- the ins operation preserves the bst property-/
lemma bst_ins_bst (d : α) (t : Raw α) (h : BST t) : BST (ins d t) := by
  unfold ins
  split
  · apply BST.node
    · intro x hx; contradiction
    · apply BST.nil
    · intro x hx; contradiction
    · apply BST.nil
  · split
    · apply bst_baliL_bst
      · sorry
      · sorry
      · sorry
      · sorry
    · assumption
    · sorry

/- the insertion operation preserves the bst property-/
theorem bst_insert_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.insert x) := by
  unfold insert
  apply bst_paintColor_of_bst
  apply bst_ins_bst; assumption

theorem bst_erase_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.erase x) := sorry

/--
The child invariant for red black trees: Red nodes must have black children.
-/
inductive ChildInv : Raw α → Prop where
  | nil : ChildInv .nil
  | black (hleft : ChildInv left) (hright : ChildInv right) : ChildInv (.node left data .black right)
  | red (hleft1 : ChildInv left) (hleft2 : left.rootColor = .black) (hright1 : ChildInv right)
        (hright2 : right.rootColor = .black) : ChildInv (.node left data .red right)

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem childInv_nil : ChildInv (.nil : Raw α) := ChildInv.nil

theorem childInv_insert_of_bst (x : α) (t : Raw α) (h : ChildInv t) : ChildInv (t.insert x) := sorry
theorem childInv_erase_of_bst (x : α) (t : Raw α) (h : ChildInv t) : ChildInv (t.erase x) := sorry

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

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem heightInv_nil : HeightInv (.nil : Raw α) := HeightInv.nil

theorem heightInv_insert_of_bst (x : α) (t : Raw α) (h : HeightInv t) : HeightInv (t.insert x) := sorry
theorem heightInv_erase_of_bst (x : α) (t : Raw α) (h : HeightInv t) : HeightInv (t.erase x) := sorry

theorem height_le_log_size {t : Raw α} (h1 : ChildInv t) (h2 : HeightInv t) :
    t.height ≤ 2 * Nat.log 2 t.size + 2 := by
    induction t with
    | nil => simp[height, size]
    | node left data color right hleft hright => sorry

end Raw
end Internal
end Filrb
