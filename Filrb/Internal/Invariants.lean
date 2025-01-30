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


@[simp]
theorem height_nil : (.nil : Raw α).height = 0 := by
  rfl

@[simp]
theorem height_node : (.node l d c r : Raw α).height = max l.height r.height + 1 := by
  rfl

theorem height_le_blackHeight' {t : Raw α} (h1 : ChildInv t) (h2 : HeightInv t) :
    t.height ≤ 2 * t.blackHeightLeft + (if t.rootColor = .black then 0 else 1) := by
  induction t with
  | nil => simp
  | node left data color right lih rih => aesop (add unsafe tactic (by omega))

theorem height_le_blackHeight {t : Raw α} (h1 : ChildInv t) (h2 : HeightInv t)
    (h : t.rootColor = .black) :
    t.height ≤ 2 * t.blackHeightLeft := by
  have := height_le_blackHeight' h1 h2
  simp_all

theorem blackHeight_le_size {t : Raw α} (h1 : ChildInv t) (h2 : HeightInv t) :
    2 ^ t.blackHeightLeft ≤ t.size + 1 := by
  induction t with
  | nil => simp
  | node l d c r lih rih =>
    cases c <;> aesop (add unsafe tactic (by omega))

theorem height_le_log_size {t : Raw α} (h1 : ChildInv t) (h2 : HeightInv t)
    (h : t.rootColor = .black) :
    t.height ≤ 2 * Nat.log 2 (t.size + 1) := by
  calc
    t.height ≤ 2 * t.blackHeightLeft := height_le_blackHeight h1 h2 h
    _ ≤ 2 * Nat.log 2 (t.size + 1) := by
      have ha2 := Nat.log_mono_right (b := 2) (blackHeight_le_size h1 h2)
      rw [Nat.log_pow (hb := by decide)] at ha2
      omega

end Raw
end Internal
end Filrb
