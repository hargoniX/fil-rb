import Filrb.Internal.Raw
import Filrb.Internal.Mem

/-!
This module proves that our functionality preserves the `BST` invariant.
-/

namespace Filrb
namespace Internal

namespace Raw

variable [Preorder α] [Ord α] [LawfulOrd α]

omit [Ord α] [LawfulOrd α] in
@[simp]
theorem bst_nil : BST (.nil : Raw α) := BST.nil

omit [Ord α] [LawfulOrd α] in
@[simp]
theorem bst_node {l r : Raw α} :
    BST (.node l d c r) ↔ (∀ x ∈ l, x < d) ∧ BST l ∧ (∀ x ∈ r, d < x) ∧ BST r := by
  constructor
  · intro h
    cases h
    simp_all
  · rintro ⟨_, _, _, _⟩
    apply BST.node <;> assumption

omit [Ord α] [LawfulOrd α] in
theorem bst_ordered {l r : Raw α} (h : BST (.node l d c r)) : ∀ x ∈ l, ∀ y ∈ r, x < y := by
  intro l hl r hr
  cases h with
  | node hl1 hl2 hr1 hr2 =>
    apply lt_trans (hl1 l hl) _
    apply hr1
    assumption

omit [Ord α] [LawfulOrd α] in
theorem bst_color_independent {l r : Raw α} (h : BST (.node l d c r)) : BST (.node l d c' r) := by
  cases h
  apply BST.node <;> assumption

omit [Ord α] [LawfulOrd α] in
@[aesop safe apply]
theorem bst_paintColor_of_bst (c : Color) (t : Raw α) (h : BST t) : BST (t.paintColor c) := by
  unfold paintColor
  split
  . assumption
  . apply bst_color_independent h


omit [Ord α] [LawfulOrd α] in
/- the balance-left operation preserves the bst property-/
@[aesop safe apply]
theorem bst_baliL_of_bsts (tl tr : Raw α) (Hl : ∀ x ∈ tl, x < d) (hl : BST tl)
    (Hr : ∀ x ∈ tr, d < x) (hr : BST tr) :
    BST (baliL d tl tr) := by
  unfold baliL
  split
  · apply BST.node
    · aesop
    · aesop
    · intro x hx
      rw [mem_node] at hx
      rcases hx with hx | hx | hx
      · aesop
      · aesop
      · apply lt_trans _ (Hr x hx)
        aesop
    · aesop
  · rw [bst_node] at hl
    rcases hl with ⟨hleft2, hleft1, hright2, hright1⟩
    apply BST.node
    · intro x h
      rw [mem_node] at h
      rcases h with h | h | h
      · apply lt_trans (hleft2 x h) (_)
        aesop
      · aesop
      · aesop
    · aesop
    · intro x h
      rw [mem_node] at h
      rcases h with h | h | h
      · aesop
      · aesop
      · apply lt_trans _ (Hr x h)
        aesop
    · aesop
  · aesop

omit [Ord α] [LawfulOrd α] in
/- the balance-right operation preserves the bst property-/
@[aesop safe apply]
theorem bst_baliR_of_bst (tl tr : Raw α) (Hl : ∀ x ∈ tl, x < d) (hl : BST tl) (Hr : ∀ x ∈ tr, d < x)
    (hr : BST tr) :
    BST (baliR d tl tr) := by
  unfold baliR
  split
  · apply BST.node
    · intro x hx
      rw [mem_node] at hx
      rcases hx with hx | hx | hx
      · apply lt_trans (Hl x hx) (_)
        aesop
      · aesop
      · aesop
    · aesop
    · aesop
    · aesop
  · rw [bst_node] at hr
    rcases hr with ⟨hleft1, hleft2, hright1, hright2⟩
    apply BST.node
    · intro x hx
      rw [mem_node] at hx
      rcases hx with hx | hx | hx
      · apply lt_trans (Hl x hx) (_)
        aesop
      · aesop
      · aesop
    · aesop
    · intro x hx
      rw [mem_node] at hx
      rcases hx with hx | hx | hx
      · aesop
      · aesop
      · apply lt_trans (_) (hright1 x hx)
        aesop
    · aesop
  · aesop

/- the ins operation preserves the bst property-/
theorem bst_ins_bst (d : α) (t : Raw α) (h : BST t) : BST (ins d t) := by
  unfold ins
  split
  · simp
  · split <;> aesop (add safe apply bst_ins_bst)
  · split <;> aesop (add safe apply bst_ins_bst)
termination_by t

/- the insertion operation preserves the bst property-/
theorem bst_insert_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.insert x) := by
  unfold insert
  apply bst_paintColor_of_bst
  apply bst_ins_bst
  assumption

omit [Preorder α] [LawfulOrd α] in
@[simp]
theorem erase_nil : erase x (.nil : Raw α) = .nil := by
  simp [erase, paintColor, del]

omit [Ord α] [LawfulOrd α] in
@[aesop safe apply]
theorem bst_baldL_of_bsts (x : α) (left right : Raw α)
    (hleft1 : ∀ y ∈ left, y < x) (hleft2 : BST left)
    (hright1 : ∀ y ∈ right, x < y) (hright2 : BST right) : BST (baldL x left right) := by
  unfold baldL
  split
  . aesop
  . aesop
  . cases hright2
    next hl1 hl2 _ hr2 =>
      apply BST.node
      . intro x hmem
        rcases hmem with _ | h | h
        . simp_all
        . apply lt_trans (hleft1 x h) _
          apply hright1
          simp
        . simp_all
      . aesop
      . intro x hmem
        have := mem_of_mem_baliR hmem
        rcases this with h | h | h
        . simp_all
        . rw [mem_iff_paintColor_mem] at h
          apply lt_trans _ (hr2 x h)
          simp_all
        . simp_all
      . aesop
  . apply BST.node hleft1 hleft2 hright1 hright2

omit [Ord α] [LawfulOrd α] in
@[aesop safe apply]
theorem bst_baldR_of_bsts (x : α) (left right : Raw α)
    (hleft1 : ∀ y ∈ left, y < x) (hleft2 : BST left)
    (hright1 : ∀ y ∈ right, x < y) (hright2 : BST right) : BST (baldR x left right) := by
  unfold baldR
  split
  . aesop
  . aesop
  . cases hleft2
    next hl1 hl2 _ hr2 =>
      apply BST.node
      . intro x hmem
        have := mem_of_mem_baliL hmem
        rcases this with h | h | h
        . rw [mem_iff_paintColor_mem] at h
          apply lt_trans (hl2 x h) _
          simp_all
        . simp_all
        . simp_all
      . aesop
      . intro x hmem
        rcases hmem with _ | h | h
        . simp_all
        . simp_all
        . apply lt_trans _ (hright1 x h)
          apply hleft1
          simp
      . aesop
  . apply BST.node hleft1 hleft2 hright1 hright2

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem appendTrees_root {left right : Raw α} (heq : appendTrees left right = .node l d c r) :
    ∀ x, x ∈ l ∨ x = d ∨ x ∈ r → x ∈ left ∨ x ∈ right := by
  intro x
  have : x ∈ appendTrees left right ↔ x ∈ Raw.node l d c r := by rw [heq]
  rw [mem_node] at this
  rw [← this]
  apply mem_of_mem_appendTrees

-- aesop really seems to struggle here performance wise
omit [Ord α] [LawfulOrd α] in
set_option maxHeartbeats 0 in
@[aesop safe apply]
theorem bst_appendTrees_of_bsts {left right : Raw α} (hleft : BST left) (hright : BST right)
    (hord : ∀ y ∈ left, ∀ x ∈ right, y < x) : BST (appendTrees left right) := by
  unfold appendTrees
  split
  . assumption
  . assumption
  . split
    . simp_all only [bst_node, mem_node, true_or, or_true, implies_true, true_and, and_self, and_true]
      rename_i left1 data1 right1 left2 data2 right2 heq left3 data3 right3 heq
      have BST_right1 := hleft.right.right.right
      have BST_left2 := hright.right.left
      have memAppendTrees := appendTrees_root heq
      refine ⟨?_,⟨?_,?_⟩,?_,?_,?_⟩
      . intro x h
        have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        have mem_data3 := memAppendTrees data3 (by simp)
        rcases h with h | h | h
        . apply lt_trans (hleft.left x h) _
          cases mem_data3 <;> aesop
        . cases mem_data3 <;> aesop
        . aesop
      . intro x h
        have mem_subtree := memAppendTrees x (by simp [h])
        cases mem_subtree <;> aesop
      . have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        aesop
      . intro x h
        have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        have mem_data3 := memAppendTrees data3 (by simp)
        rcases h with h | h | h
        . aesop
        . cases mem_data3 <;> aesop
        . have := hright.right.right.left
          apply lt_trans _ (this x h)
          cases mem_data3 <;> aesop
      . intro x h
        have mem_subtree := memAppendTrees x (by simp [h])
        cases mem_subtree <;> aesop
      . have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        aesop
    . aesop (add norm appendTrees, safe bst_appendTrees_of_bsts)
  -- TODO: this is COMPLETELY identical to the one above, maybe there is a way to better split it?
  . split
    . simp_all only [bst_node, mem_node, true_or, or_true, implies_true, true_and, and_self, and_true]
      rename_i left1 data1 right1 left2 data2 right2 heq left3 data3 right3 heq
      have BST_right1 := hleft.right.right.right
      have BST_left2 := hright.right.left
      have memAppendTrees := appendTrees_root heq
      refine ⟨?_,⟨?_,?_⟩,?_,?_,?_⟩
      . intro x h
        have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        have mem_data3 := memAppendTrees data3 (by simp)
        rcases h with h | h | h
        . apply lt_trans (hleft.left x h) _
          cases mem_data3 <;> aesop
        . cases mem_data3 <;> aesop
        . aesop
      . intro x h
        have mem_subtree := memAppendTrees x (by simp [h])
        cases mem_subtree <;> aesop
      . have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        aesop
      . intro x h
        have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        have mem_data3 := memAppendTrees data3 (by simp)
        rcases h with h | h | h
        . aesop
        . cases mem_data3 <;> aesop
        . have := hright.right.right.left
          apply lt_trans _ (this x h)
          cases mem_data3 <;> aesop
      . intro x h
        have mem_subtree := memAppendTrees x (by simp [h])
        cases mem_subtree <;> aesop
      . have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        aesop
    . aesop (add norm appendTrees, safe bst_appendTrees_of_bsts)
  . aesop (add norm appendTrees, safe bst_appendTrees_of_bsts)
  . aesop (add norm appendTrees, safe bst_appendTrees_of_bsts)
termination_by (left, right)

theorem bst_del_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.del x) := by
  unfold del
  split
  . assumption
  . split
    . split <;> aesop (add safe apply bst_del_of_bst)
    . have := bst_ordered h
      aesop
    . split <;> aesop (add safe apply bst_del_of_bst)
termination_by t

theorem bst_erase_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.erase x) := by
  unfold erase
  apply bst_paintColor_of_bst
  apply bst_del_of_bst
  exact h

end Raw
end Internal
end Filrb
