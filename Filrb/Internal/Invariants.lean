import Filrb.Internal.Invariants.BST
import Filrb.Internal.Invariants.RBInv
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

theorem height_le_log_size {t : Raw α} (h1 : ChildInv t) (h2 : HeightInv t) :
    t.height ≤ 2 * Nat.log 2 t.size + 2 := by
    induction t with
    | nil => simp[height, size]
    | node left data color right hleft hright => sorry

end Raw
end Internal
end Filrb
