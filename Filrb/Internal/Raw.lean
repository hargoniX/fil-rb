import Filrb.LawfulOrd


/-!
This module defines the raw red black tree data structure and the basic operations on it.
The definition we choose is specifically geared towards an efficient memory layout and
FBIP usage, consider the following alternative definitions:

1. From [Functional Algorithms Verified](https://functional-algorithms-verified.org/functional_data_structures_algorithms.pdf)
   ```
   datatype 'a tree = Leaf | Node ('a tree) 'a ('a tree)
   type_synonym 'a rbt = ('a × color) tree
   ```
   This introduces an additional pointer indirection through the data/color tuple.
2. Directly encoding the color in different tree constructors. This will destroy FBIP as the
   implementation of FBIP within Lean only reuses memory across the same constructor so changing
   the color of a node would inhibit FBIP. The definition of color chosen below makes Lean encode
   it as just an 8 bit integer that is stored within the node. We believe this to be an acceptable
   overhead compared to calling the allocator more often than necessary.

-/

namespace Filrb
namespace Internal

variable [Preorder α] [Ord α] [LawfulOrd α]

/--
Colors of red black tree nodes.
-/
inductive Color where
  | black
  | red

/--
The basic red black tree data structure without any invariant etc. attached.
-/
inductive Raw (α : Type u) where
  /--
  The empty tree.
  -/
  | nil : Raw α
  /--
  A node with left and right successor, its color and a piece of data
  -/
  | node (left : Raw α) (data : α) (color : Color) (right : Raw α) : Raw α

namespace Raw

def isEmpty (t : Raw α) : Bool :=
  match t with
  | .nil => true
  | _ => false

/--
Insert `d` into `t`.
-/
def insert (t : Raw α) (d : α) : Raw α := sorry

/--
Erase `d` from `t`, if `d` is not in `t` leave it untouched.
-/
def erase (t : Raw α) (d : α) : Raw α := sorry

/--
Check whether `d` is contained within `t`.
-/
def contains (t : Raw α) (d : α) : Bool :=
  match t with
  | .nil => false
  | .node left data _ right =>
    match compare d data with
    | .lt => left.contains d
    | .eq => true
    | .gt => right.contains d

/--
`x` is a member of a red black tree.
-/
inductive Mem (x : α) : Raw α → Prop where
  | here : Mem x (.node left x color right)
  | left (hleft : Mem x left) : Mem x (.node left y color right)
  | right (hright : Mem x right) : Mem x (.node left y color right)

instance : Membership α (Raw α) where
  mem t x := Mem x t

def size (t : Raw α) : Nat :=
  match t with
  | .nil => 0
  | .node l _ _ r => size l + size r + 1

end Raw

end Internal
end Filrb
