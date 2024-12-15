import Filrb.Internal.Raw
import Filrb.Internal.Invariants

/-!
This module defines the notion of membership in a raw red black tree and proves that `Raw.contains`
corresponds to this notion.
-/

namespace Filrb
namespace Internal
namespace Raw

variable [LinearOrder α]

theorem mem_of_contains_eq_true {x : α} {t : Raw α} (h1 : t.contains x = true) (h2 : BST t) :
    x ∈ t := sorry

theorem contains_eq_true_of_mem {x : α} {t : Raw α} (h1 : x ∈ t) (h2 : BST t) :
    t.contains x = true := sorry

end Raw
end Internal
end Filrb
