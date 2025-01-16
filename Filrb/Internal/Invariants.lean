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
theorem bst_color_independent {l r : Raw α} (h : BST (.node l d c r)) : BST (.node l d c' r) := by
  cases h
  apply BST.node <;> assumption

omit [Ord α] [LawfulOrd α] in
theorem bst_paintColor_of_bst (c : Color) (t : Raw α) (h : BST t) : BST (t.paintColor c) := by
  unfold paintColor
  split
  . assumption
  . apply bst_color_independent h

/- the balance-left operation preserves the bst property-/
@[aesop safe apply]
theorem bst_baliL_of_bsts (tl tr : Raw α) (Hl : ∀ x ∈ tl, x < d) (hl : BST tl) (Hr : ∀ x ∈ tr, d < x) (hr : BST tr)  : BST (baliL d tl tr) := by
      unfold baliL
      split
      · next hx1 hx ht1 hd1 ht2 hd2 ht3 => cases hl
                                           next hleft2 hleft1 hright2 hright1 =>
                                            apply BST.node
                                            · aesop
                                            · aesop
                                            · intro x hx
                                              cases hx
                                              · aesop
                                              · aesop
                                              · next hright3 => have h : x ∈ tr := by apply hright3
                                                                apply lt_trans _ (Hr x h)
                                                                aesop
                                            · aesop
      · next x1 x2 t1 d1 t2 d2 t3 hx => cases hl
                                        next hleft2 hleft1 hright2 hright1 =>
                                          apply BST.node
                                          · intro x h
                                            cases h
                                            · aesop
                                            · next hleft => have h : x ∈ t1 := by apply hleft
                                                            apply lt_trans (hleft1 x h) (_)
                                                            aesop
                                            · aesop
                                          · aesop
                                          · intro x h
                                            cases h
                                            · aesop
                                            · aesop
                                            · next hright => have hhx : x ∈ tr := by apply hright
                                                             apply lt_trans _ (Hr x hhx)
                                                             aesop
                                          · aesop
      · aesop

/- the balance-right operation preserves the bst property-/
@[aesop safe apply]
theorem bst_baliR_of_bst (tl tr : Raw α) (Hl : ∀ x ∈ tl, x < d) (hl : BST tl) (Hr : ∀ x ∈ tr, d < x) (hr : BST tr) : BST (baliR d tl tr) := by
  unfold baliR
  split
  · next t1 t2 t3 d1 t4 d5 t6 h => cases hr
                                   next hleft2 hleft1 hright2 hright1 =>
                                    apply BST.node
                                    · intro x hx
                                      cases hx
                                      · aesop
                                      · next hleft => have h1 : x ∈ tl := by apply hleft
                                                      apply lt_trans (Hl x h1) (_)
                                                      aesop
                                      · aesop
                                    · aesop
                                    · aesop
                                    · aesop
  · next t1 t2 t3 d1 t4 d5 t6 h => cases hr
                                   next hleft2 hleft1 hright2 hright1 =>
                                   apply BST.node
                                   · intro x hx
                                     cases hx
                                     · aesop
                                     · next hleft => have h1 : x ∈ tl := by apply hleft
                                                     apply lt_trans (Hl x h1) (_)
                                                     aesop
                                     · aesop
                                   · aesop
                                   · intro x hx
                                     cases hx
                                     · aesop
                                     · aesop
                                     · next hright => have h1 : x ∈ t6 := by apply hright
                                                      apply lt_trans (_) (hright1 x h1)
                                                      aesop
                                   · aesop
  · aesop

@[aesop safe forward]
theorem mem_of_mem_baliL {d : α} (h : x ∈ baliL d left right) : x ∈ left ∨ x ∈ right ∨ x = d := by
  unfold baliL at h
  split at h <;> aesop

@[aesop safe forward]
theorem mem_of_mem_baliR {d : α} (h : x ∈ baliR d left right) : x ∈ left ∨ x ∈ right ∨ x = d := by
  unfold baliR at h
  split at h <;> aesop

@[aesop safe forward]
theorem mem_of_mem_ins (t : Raw α) (x d : α) (h1 : BST t) (h2 : x ∈ ins d t) : x = d ∨ x ∈ t := by
  unfold ins at h2
  split at h2 <;> aesop (add safe forward mem_of_mem_ins)
/- the ins operation preserves the bst property-/
theorem bst_ins_bst (d : α) (t : Raw α) (h : BST t) : BST (ins d t) := by
  unfold ins
  split
  · simp
  · split <;> aesop (add safe apply bst_ins_bst)
  · split <;> aesop (add safe apply bst_ins_bst)

/- the insertion operation preserves the bst property-/
theorem bst_insert_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.insert x) := by
  unfold insert
  apply bst_paintColor_of_bst
  apply bst_ins_bst; assumption

omit [Preorder α] [LawfulOrd α] in
@[simp]
theorem erase_nil : erase x (.nil : Raw α) = .nil := by
  simp [erase, paintColor, del]

@[aesop safe apply]
theorem bst_baldL_of_bsts (x : α) (left right : Raw α)
    (hleft1 : ∀ y ∈ left, y < x) (hleft2 : BST left)
    (hright1 : ∀ y ∈ right, x < y) (hright2 : BST right) : BST (baldL x left right) := by
  unfold baldL
  split
  . apply BST.node
    . intro x hmem
      apply hleft1
      apply mem_color_independent
      assumption
    . apply bst_color_independent
      assumption
    . intro x hmem
      apply hright1
      assumption
    . assumption
  . apply bst_baliR_of_bst
    . sorry
    . assumption
    . sorry
    . apply bst_color_independent
      assumption
  . cases hright2
    next hl1 hl2 _ hr2 =>
      apply BST.node
      . intro x hmem
        cases hl1
        next _ hll2 _ hlr2 =>
          rcases hmem with _ | h | h
          . simp_all -- case doesnt happen
          . simp at h
            have x_lt_x3:= hleft1 x h
            have h1 := hright1
            sorry
          . simp_all -- case doesnt happen
      . apply BST.node hleft1 hleft2
        . intro x hmem
          apply hright1
          simp [hmem]
        . cases hl1
          assumption
      . intro x hmem
        sorry
      . apply bst_baliR_of_bst
        . sorry
        . cases hl1
          assumption
        . sorry
        . apply bst_paintColor_of_bst
          assumption
  . apply BST.node hleft1 hleft2 hright1 hright2

@[aesop safe apply]
theorem bst_baldR_of_bsts (x : α) (left right : Raw α)
    (hleft1 : ∀ y ∈ left, y < x) (hleft2 : BST left)
    (hright1 : ∀ y ∈ right, x < y) (hright2 : BST right) : BST (baldR x left right) := by
  unfold baldR
  split
  . apply BST.node
    . intro x hmem
      apply hleft1
      assumption
    . assumption
    . intro x hmem
      apply hright1
      apply mem_color_independent
      assumption
    . apply bst_color_independent
      assumption
  . apply bst_baliL_of_bsts
    . sorry
    . apply bst_color_independent
      assumption
    . assumption
    . sorry
  . sorry
  . apply BST.node hleft1 hleft2 hright1 hright2

@[aesop safe apply]
theorem bst_appendTrees_of_bsts {t₁ t₂ : Raw α} (h₁ : BST t₁) (h₂ : BST t₂): BST (appendTrees t₁ t₂) := by
  unfold appendTrees
  split
  . assumption
  . assumption
  . split
    . next h =>
      apply BST.node
      . sorry
      . sorry
      . sorry
      . sorry
    . next h => sorry
  . sorry
  . sorry
  . sorry

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
theorem mem_of_mem_appendTrees (h : x ∈ appendTrees t₁ t₂) : x ∈ t₁ ∨ x ∈ t₂  := by
  unfold appendTrees at h
  split at h
  . simp [h]
  . simp [h]
  . split at h
    . next heq =>
        rcases h with _ | h | h
        . sorry
        . simp at h
          rcases h with h | h | h
          . simp_all
          . simp_all
          . sorry
        . sorry
    . sorry
  . split at h
    . sorry
    . sorry
  . sorry
  . sorry

@[aesop safe forward]
theorem mem_of_mem_del {d : α} (h : x ∈ del d t) : x ∈ t := by
  unfold del at h
  split at h
  . assumption
  . split at h
    . split at h <;> aesop (add safe forward mem_of_mem_del)
    . aesop
    . split at h <;> aesop (add safe forward mem_of_mem_del)

theorem bst_del_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.del x) := by
  unfold del
  split
  . assumption
  . cases h
    split
    . split <;> aesop (add safe apply bst_del_of_bst)
    . aesop
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
    t.height ≤ 2 * Nat.log 2 t.size + 2 := by
    induction t with
    | nil => simp[height, size]
    | node left data color right hleft hright => sorry

end Raw
end Internal
end Filrb
