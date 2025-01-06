import Mathlib.Order.Compare

namespace Filrb


class LawfulOrd (α : Type u) [LT α] [Ord α] where
  compares : ∀ (a b : α), (compare a b).Compares a b

instance [Preorder α] [Ord α] [LawfulOrd α] : LinearOrder α :=
  linearOrderOfCompares compare LawfulOrd.compares

instance : LawfulOrd Nat := sorry
instance : LawfulOrd Int := sorry
instance : LawfulOrd (Fin n) := sorry
instance : LawfulOrd String := sorry

end Filrb
