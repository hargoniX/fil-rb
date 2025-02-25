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
structure Set (α : Type u) [Preorder α] [Ord α] where
  raw : Internal.Raw α
  hbst: Internal.Raw.BST raw
  hcolor : Internal.Raw.ChildInv raw
  hheight : Internal.Raw.HeightInv raw
  hroot : raw.rootColor = .black

namespace Set

variable [Preorder α] [Ord α] [LawfulOrd α]

/--
The empty set.
-/
@[inline]
def empty : Set α :=
  {
    raw := .nil
    hbst := Internal.Raw.bst_nil
    hcolor := Internal.Raw.childInv_nil
    hheight := Internal.Raw.heightInv_nil
    hroot := Internal.Raw.rootColor_nil
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
  let ⟨raw, bst, color, height, _⟩ := set
  {
    raw := raw.insert x
    hbst := Internal.Raw.bst_insert_of_bst x raw bst
    hcolor := (Internal.Raw.rbInv_insert_of_rbInv x raw color height).left
    hheight := (Internal.Raw.rbInv_insert_of_rbInv x raw color height).right
    hroot := Internal.Raw.rootColor_insert_eq_black
  }

/--
Check whether `x` is contained within `set`.
-/
@[inline]
def contains (set : Set α) (x : α) : Bool := set.raw.contains x

instance : Membership α (Set α) where
  mem set x := x ∈ set.raw

theorem contains_eq_true_iff_mem {set : Set α} {x : α} : set.contains x = true ↔ x ∈ set :=
  Internal.Raw.contains_eq_true_iff_mem_of_bst set.hbst

instance {x : α} {set : Set α} : Decidable (x ∈ set) :=
  decidable_of_iff (set.contains x) contains_eq_true_iff_mem

/--
Erase `x` from `set`, if `x` is not in `set` leave it untouched.
-/
@[inline]
def erase (set : Set α) (x : α) : Set α :=
  let ⟨raw, bst, color, height, _⟩ := set
  {
    raw := raw.erase x
    hbst := Internal.Raw.bst_erase_of_bst x raw bst
    hcolor := (Internal.Raw.rbInv_erase_of_rbInv x raw color height).left
    hheight := (Internal.Raw.rbInv_erase_of_rbInv x raw color height).right
    hroot := Internal.Raw.rootColor_erase_eq_black
  }

/--
Returns the amount of elements in `set`.
-/
@[inline]
def size (set : Set α) : Nat := set.raw.size

/--
Returns the height of the tree backing `set`.
-/
@[inline]
def height (set : Set α) : Nat := set.raw.height

end Set

end Filrb
