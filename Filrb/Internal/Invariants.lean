import Filrb.Internal.Raw
import Filrb.Internal.Mem

namespace Filrb
namespace Internal
namespace Raw

variable [LinearOrder α]

inductive BST : Raw α → Prop where
  | nil : BST .nil
  | node (hleft : ∀ x ∈ left, x < data) (hright : ∀ x ∈ right, data < x) : BST (.node left data color right)

theorem bst_insert_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.insert x) := sorry
theorem bst_erase_of_bst (x : α) (t : Raw α) (h : BST t) : BST (t.erase x) := sorry

def rootColor (t : Raw α) : Color :=
  match t with
  | .nil => .black
  | .node _ _ c _ => c

inductive ChildInv : Raw α → Prop where
  | nil : ChildInv .nil
  | black (hleft : ChildInv left) (hright : ChildInv right) : ChildInv (.node left data .black right)
  | red (hleft1 : ChildInv left) (hleft2 : left.rootColor = .black) (hright1 : ChildInv right)
        (hright2 : right.rootColor = .black) : ChildInv (.node left data .red right)

theorem childInv_insert_of_bst (x : α) (t : Raw α) (h : ChildInv t) : ChildInv (t.insert x) := sorry
theorem childInv_erase_of_bst (x : α) (t : Raw α) (h : ChildInv t) : ChildInv (t.erase x) := sorry

def blackHeightLeft (t : Raw α) : Nat :=
  match t with
  | .nil => 0
  | .node left _ color _ =>
    match color with
    | .black => blackHeightLeft left + 1
    | .red => blackHeightLeft left

inductive HeightInv : Raw α → Prop where
  | nil : HeightInv .nil
  | node (hleft : HeightInv left) (hright : HeightInv right)
         (h : left.blackHeightLeft = right.blackHeightLeft) : HeightInv (.node left data color right)

theorem heightInv_insert_of_bst (x : α) (t : Raw α) (h : HeightInv t) : HeightInv (t.insert x) := sorry
theorem heightInv_erase_of_bst (x : α) (t : Raw α) (h : HeightInv t) : HeightInv (t.erase x) := sorry

end Raw
end Internal
end Filrb
