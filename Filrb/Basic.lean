import Filrb.Internal

namespace Filrb

structure Set (α : Type u) [Preorder α] [Ord α] [LawfulOrd α] where
  raw : Internal.Raw α
  bst: Internal.Raw.BST raw
  color : Internal.Raw.ChildInv raw
  height : Internal.Raw.HeightInv raw

namespace Set

variable [Preorder α] [Ord α] [LawfulOrd α]

def empty : Set α := sorry

instance : EmptyCollection (Set α) where
  emptyCollection := sorry

def isEmpty (s : Set α) : Bool := sorry

def insert (set : Set α) (x : α) : Set α := sorry

def contains (set : Set α) (x : α) : Bool := sorry

instance : Membership α (Set α) where
  mem := sorry

instance {x : α} {set : Set α} : Decidable (x ∈ set) := sorry

def erase (set : Set α) (x : α) : Set α := sorry

def size (set : Set α) : Nat := sorry

end Set

end Filrb
