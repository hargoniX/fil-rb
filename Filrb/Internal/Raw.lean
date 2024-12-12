import Mathlib.Order.Defs.LinearOrder

namespace Filrb
namespace Internal

variable [LinearOrder α]

inductive Color where
  | black
  | red

inductive Raw (α : Type u) where
  | nil : Raw α
  | node (left : Raw α) (data : α) (color : Color) (right : Raw α) : Raw α

namespace Raw

def insert (t : Raw α) (d : α) : Raw α := sorry
def erase (t : Raw α) (d : α) : Raw α := sorry
def contains (t : Raw α) (d : α) : Bool := sorry

end Raw

end Internal
end Filrb
