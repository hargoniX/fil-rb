import Filrb.Internal.Invariants
import Filrb.Internal.Mem

/-!
This module contains the definition of the red black tree based set-like container `Filrb.Set`,
together with basic operations on top of it.
-/

namespace Filrb

/--
The `Set` container implemented as the `Internal.Raw` red black tree together with the relevant
invariants. Due to Lean's FFI representation this has the same memory layout as just using
`Internal.Raw` directly so we don't pay anything for this abstraction.
-/
structure Set (α : Type u) [Preorder α] [Ord α] [LawfulOrd α] where
  raw : Internal.Raw α
  bst: Internal.Raw.BST raw
  color : Internal.Raw.ChildInv raw
  height : Internal.Raw.HeightInv raw

namespace Set

variable [Preorder α] [Ord α] [LawfulOrd α]

/--
The empty set.
-/
@[inline]
def empty : Set α :=
  {
    raw := .nil
    bst := Internal.Raw.bst_nil
    color := Internal.Raw.childInv_nil
    height := Internal.Raw.heightInv_nil
  }

instance : EmptyCollection (Set α) where
  emptyCollection := empty

/--
Whether `set` is an empty set.
-/
@[inline]
def isEmpty (set : Set α) : Bool := set.raw.isEmpty

/--
Insert `x` into `set`.
-/
@[inline]
def insert (set : Set α) (x : α) : Set α :=
  let ⟨raw, bst, color, height⟩ := set
  {
    raw := raw.insert x
    bst := Internal.Raw.bst_insert_of_bst x raw bst
    color := Internal.Raw.childInv_insert_of_bst x raw color
    height := Internal.Raw.heightInv_insert_of_bst x raw height
  }

/--
Check whether `x` is contained within `set`.
-/
@[inline]
def contains (set : Set α) (x : α) : Bool := set.raw.contains x

instance : Membership α (Set α) where
  mem set x := x ∈ set.raw

theorem contains_eq_true_iff_mem {set : Set α} {x : α} : set.contains x = true ↔ x ∈ set :=
  Internal.Raw.contains_eq_true_iff_mem_of_bst set.bst

instance {x : α} {set : Set α} : Decidable (x ∈ set) :=
  decidable_of_iff (set.contains x) contains_eq_true_iff_mem

/--
Erase `x` from `set`, if `x` is not in `set` leave it untouched.
-/
@[inline]
def erase (set : Set α) (x : α) : Set α :=
  let ⟨raw, bst, color, height⟩ := set
  {
    raw := raw.erase x
    bst := Internal.Raw.bst_erase_of_bst x raw bst
    color := Internal.Raw.childInv_erase_of_bst x raw color
    height := Internal.Raw.heightInv_erase_of_bst x raw height
  }

/--
Returns the amount of elements in `set`.
-/
@[inline]
def size (set : Set α) : Nat := set.raw.size

end Set

end Filrb
