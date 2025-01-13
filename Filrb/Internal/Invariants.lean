import Filrb.Internal.Raw
import Filrb.Internal.Mem
import Mathlib.Data.Nat.Log

/-!
This module defines the red black tree invariants and proves that the mutating operations on
red black trees preserve these invariants.
-/

namespace Filrb
namespace Internal

namespace Raw

@[simp]
theorem size_nil : (.nil : Raw α).size = 0 := by
  rfl

@[simp]
theorem size_node : (.node l d c r : Raw α).size = l.size + r.size + 1 := by
  rfl

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
  . simp
  . apply bst_color_independent h

@[aesop safe apply]
theorem bst_baliL_of_bsts(x : α) (left right : Raw α)
    (hleft1 : ∀ y ∈ left, y < x) (hleft2 : BST left)
    (hright1 : ∀ y ∈ right, x < y) (hright2 : BST right) : BST (baliL x left right) := by
  sorry

@[aesop safe apply]
theorem bst_baliR_of_bsts(x : α) (left right : Raw α)
    (hleft1 : ∀ y ∈ left, y < x) (hleft2 : BST left)
    (hright1 : ∀ y ∈ right, x < y) (hright2 : BST right) : BST (baliR x left right) := by
  sorry

theorem mem_of_mem_baliL {d : α} (h : x ∈ baliL d left right) : x ∈ left ∨ x ∈ right ∨ x = d := by
  sorry

theorem mem_of_mem_baliR {d : α} (h : x ∈ baliR d left right) : x ∈ left ∨ x ∈ right ∨ x = d := by
  sorry

theorem bst_insert_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.insert x) := sorry

omit [Preorder α] [LawfulOrd α] in
@[simp]
theorem erase_nil : erase x (.nil : Raw α) = .nil := by
  simp [erase, paintColor, del]

@[aesop safe forward]
theorem mem_of_mem_baldL {d : α} (h : x ∈ baldL d t₁ t₂) : x ∈ t₁ ∨ x ∈ t₂ ∨ x = d := by
  unfold baldL at h
  split at h
  . aesop
  . have := mem_of_mem_baliR h
    aesop
  . rcases h with _ | h | h
    . simp
    . aesop
    . have := mem_of_mem_baliR h
      aesop
  . aesop

@[aesop safe forward]
theorem mem_of_mem_baldR {d : α} (h : x ∈ baldR d t₁ t₂) : x ∈ t₁ ∨ x ∈ t₂ ∨ x = d := by
  unfold baldR at h
  split at h
  . aesop
  . have := mem_of_mem_baliL h
    aesop
  . rcases h with _ | h | h
    . simp
    . have := mem_of_mem_baliL h
      aesop
    . aesop
  . aesop

@[aesop safe forward]
theorem mem_of_mem_appendTrees {t₁ t₂ : Raw α} (h : x ∈ appendTrees t₁ t₂) : x ∈ t₁ ∨ x ∈ t₂  := by
  induction t₁, t₂ using appendTrees.induct <;> aesop (add safe h, norm appendTrees)

@[aesop safe forward]
theorem mem_of_mem_del {d : α} (h : x ∈ del d t) : x ∈ t := by
  unfold del at h
  split at h
  . assumption
  . split at h
    . split at h <;> aesop (add safe forward mem_of_mem_del)
    . aesop
    . split at h <;> aesop (add safe forward mem_of_mem_del)

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

theorem appendTrees_root {left right : Raw α} (heq : appendTrees left right = .node l d c r) :
    ∀ x, x ∈ left ∨ x ∈ right ↔ x ∈ l ∨ x ∈ r ∨ x = d := by
  --aesop (add norm appendTrees)
  sorry

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
        have mem_data3 := (memAppendTrees data3).mpr (by simp)
        rcases h with h | h | h
        . apply lt_trans (hleft.left x h) _
          cases mem_data3 <;> aesop
        . cases mem_data3 <;> aesop
        . aesop
      . intro x h
        have mem_subtree := (memAppendTrees x).mpr (by simp [h])
        cases mem_subtree <;> aesop
      . have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        aesop
      . intro x h
        have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        have mem_data3 := (memAppendTrees data3).mpr (by simp)
        rcases h with h | h | h
        . aesop
        . cases mem_data3 <;> aesop
        . have := hright.right.right.left
          apply lt_trans _ (this x h)
          cases mem_data3 <;> aesop
      . intro x h
        have mem_subtree := (memAppendTrees x).mpr (by simp [h])
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
        have mem_data3 := (memAppendTrees data3).mpr (by simp)
        rcases h with h | h | h
        . apply lt_trans (hleft.left x h) _
          cases mem_data3 <;> aesop
        . cases mem_data3 <;> aesop
        . aesop
      . intro x h
        have mem_subtree := (memAppendTrees x).mpr (by simp [h])
        cases mem_subtree <;> aesop
      . have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        aesop
      . intro x h
        have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        have mem_data3 := (memAppendTrees data3).mpr (by simp)
        rcases h with h | h | h
        . aesop
        . cases mem_data3 <;> aesop
        . have := hright.right.right.left
          apply lt_trans _ (this x h)
          cases mem_data3 <;> aesop
      . intro x h
        have mem_subtree := (memAppendTrees x).mpr (by simp [h])
        cases mem_subtree <;> aesop
      . have ih := bst_appendTrees_of_bsts BST_right1 BST_left2 (by aesop)
        aesop
    . aesop (add norm appendTrees, safe bst_appendTrees_of_bsts)
  . aesop (add norm appendTrees, safe bst_appendTrees_of_bsts)
  . aesop (add norm appendTrees, safe bst_appendTrees_of_bsts)

theorem bst_del_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.del x) := by
  unfold del
  split
  . assumption
  . split
    . split <;> aesop (add safe apply bst_del_of_bst)
    . have := bst_ordered h
      aesop
    . split <;> aesop (add safe apply bst_del_of_bst)

theorem bst_erase_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.erase x) := by
  unfold erase
  apply bst_paintColor_of_bst
  apply bst_del_of_bst
  exact h

/--
The child invariant for red black trees: Red nodes must have black children.
-/
inductive ChildInv : Raw α → Prop where
  | nil : ChildInv .nil
  | black (hleft : ChildInv left) (hright : ChildInv right) : ChildInv (.node left data .black right)
  | red (hleft1 : ChildInv left) (hleft2 : left.rootColor = .black) (hright1 : ChildInv right)
        (hright2 : right.rootColor = .black) : ChildInv (.node left data .red right)

attribute [pp_nodot] ChildInv

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
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

attribute [pp_nodot] HeightInv

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem heightInv_nil : HeightInv (.nil : Raw α) := HeightInv.nil

theorem heightInv_insert_of_bst (x : α) (t : Raw α) (h : HeightInv t) : HeightInv (t.insert x) := sorry
theorem heightInv_erase_of_bst (x : α) (t : Raw α) (h : HeightInv t) : HeightInv (t.erase x) := sorry

theorem height_le_log_size {t : Raw α} (h1 : ChildInv t) (h2 : HeightInv t) :
    t.height ≤ 2 * Nat.log 2 t.size + 2 := sorry

end Raw
end Internal
end Filrb
