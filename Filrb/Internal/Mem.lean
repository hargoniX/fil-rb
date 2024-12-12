import Filrb.Internal.Raw

/-!
This module defines the notion of membership in a raw red black tree and proves that `Raw.contains`
corresponds to this notion.
-/

namespace Filrb
namespace Internal
namespace Raw

/--
`x` is a member of a red black tree.
-/
inductive Mem (x : α) : Raw α → Prop where
  | here : Mem x (.node left x color right)
  | left (hleft : Mem x left) : Mem x (.node left y color right)
  | right (hright : Mem x right) : Mem x (.node left y color right)

instance : Membership α (Raw α) where
  mem t x := Mem x t

theorem mem_of_contains_eq_true {x : α} {t : Raw α} (h : t.contains x = true) : x ∈ t := sorry
theorem contains_eq_true_of_mem {x : α} {t : Raw α} (h : x ∈ t) : t.contains x = true := sorry

/--
`contains` decides `Mem`.
-/
instance {x : α} {t : Raw α} : Decidable (x ∈ t) :=
  decidable_of_decidable_of_iff (Iff.intro mem_of_contains_eq_true contains_eq_true_of_mem)

end Raw
end Internal
end Filrb
