import Filrb.Internal.Raw
import Filrb.Internal.Invariants.BST
/-!
This module proves that our functionality preserves the `ChildInv` invariant.
-/

namespace Filrb
namespace Internal

namespace Raw

variable [Preorder α] [Ord α] [LawfulOrd α]

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


lemma childInv_branch_left_bst {l r : Raw α} (h : ChildInv (.node l d c r)) : ChildInv l := by sorry

lemma childInv_branch_right_bst {l r : Raw α} (h : ChildInv (.node l d c r)) : ChildInv r := by sorry

lemma childInv_paintColor_black_of_bst (t: Raw α) (h: ChildInv t) : ChildInv (t.paintColor .black) := by
  unfold paintColor
  split
  · assumption
  · apply ChildInv.black
    apply childInv_branch_left_bst h
    apply childInv_branch_right_bst h

lemma childInv_baliL_of_bst (tl tr : Raw α) (Hl : ∀ x ∈ tl, x < d) (hl : ChildInv tl)
    (Hr : ∀ x ∈ tr, d < x) (hr : ChildInv tr) : ChildInv (baliL d tl tl) := sorry

lemma childInv_baliR_of_bst (tl tr : Raw α) (Hl : ∀ x ∈ tl, x < d) (hl : ChildInv tl)
    (Hr : ∀ x ∈ tr, d < x) (hr : ChildInv tr) : ChildInv (baliR d tl tl) := sorry

lemma childInv_ins_of_bst (d : α) (t : Raw α) (h : ChildInv t) : ChildInv (ins d t) := by
  unfold ins
  split
  · apply ChildInv.red
    · assumption
    · sorry
    · assumption
    · sorry
  · split
    · sorry
    · sorry
    · sorry
  · split
    · sorry
    · sorry
    · sorry

theorem childInv_insert_of_bst (x : α) (t : Raw α) (h : ChildInv t) : ChildInv (t.insert x) := by
  rcases h with h | h | h
  · apply ChildInv.black <;> apply ChildInv.nil
  · unfold insert
    apply childInv_paintColor_black_of_bst
    apply childInv_ins_of_bst
    apply ChildInv.black <;> assumption
  · unfold insert
    apply childInv_paintColor_black_of_bst
    apply childInv_ins_of_bst
    apply ChildInv.red <;> assumption

theorem childInv_erase_of_bst (x : α) (t : Raw α) (h : ChildInv t) : ChildInv (t.erase x) := sorry

end Raw
end Internal
end Filrb
