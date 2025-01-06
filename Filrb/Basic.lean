import Filrb.Internal.Invariants
import Filrb.Internal.Mem

namespace Filrb

structure Set (α : Type u) [Preorder α] [Ord α] [LawfulOrd α] where
  raw : Internal.Raw α
  bst: Internal.Raw.BST raw
  color : Internal.Raw.ChildInv raw
  height : Internal.Raw.HeightInv raw

namespace Set

variable [Preorder α] [Ord α] [LawfulOrd α]

def empty : Set α :=
  {
    raw := .nil
    bst := Internal.Raw.bst_nil
    color := Internal.Raw.childInv_nil
    height := Internal.Raw.heightInv_nil
  }

instance : EmptyCollection (Set α) where
  emptyCollection := empty

def isEmpty (s : Set α) : Bool := s.raw.isEmpty

def insert (set : Set α) (x : α) : Set α :=
  let ⟨raw, bst, color, height⟩ := set
  {
    raw := raw.insert x
    bst := Internal.Raw.bst_insert_of_bst x raw bst
    color := Internal.Raw.childInv_insert_of_bst x raw color
    height := Internal.Raw.heightInv_insert_of_bst x raw height
  }

def contains (set : Set α) (x : α) : Bool := set.raw.contains x

instance : Membership α (Set α) where
  mem set x := x ∈ set.raw

theorem contains_eq_true_iff_mem {set : Set α} {x : α} : set.contains x = true ↔ x ∈ set :=
  Internal.Raw.contains_eq_true_iff_mem_of_bst set.bst

instance {x : α} {set : Set α} : Decidable (x ∈ set) :=
  decidable_of_iff (set.contains x) contains_eq_true_iff_mem

def erase (set : Set α) (x : α) : Set α :=
  let ⟨raw, bst, color, height⟩ := set
  {
    raw := raw.erase x
    bst := Internal.Raw.bst_erase_of_bst x raw bst
    color := Internal.Raw.childInv_erase_of_bst x raw color
    height := Internal.Raw.heightInv_erase_of_bst x raw height
  }

def size (set : Set α) : Nat := set.raw.size

end Set

end Filrb
