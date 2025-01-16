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

variable [Preorder α] [Ord α]

/--
Colors of red black tree nodes.
-/
inductive Color where
  | black
  | red
  deriving DecidableEq

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

attribute [pp_nodot] Raw.node

namespace Raw

/--
Whether `t` is an empty set.
-/
@[inline]
def isEmpty (t : Raw α) : Bool :=
  match t with
  | .nil => true
  | _ => false

/--
Fetch the color of the root of `t`.
-/
@[inline]
def rootColor (t : Raw α) : Color :=
  match t with
  | .nil => .black
  | .node _ _ c _ => c

/--
Paint the color of the root of `t` to given color `c`.
-/
@[inline]
def paintColor (c : Color) (t : Raw α) : Raw α :=
  match t with
  | .nil => .nil
  | .node l d _ r => .node l d c r

@[inline]
def isBlack (t : Raw α) : Bool :=
  match t with
  | .node _ _ .black _ => true
  | _             => false

-- Balanced insert into the left child, fixing red on red sequences on the way.
@[inline]
def baliL (d : α) : Raw α → Raw α → Raw α
  | .node (.node t₁ data₁ .red t₂) data₂ .red t₃, right
  | .node t₁ data₁ .red (.node t₂ data₂ .red t₃), right =>
      .node (.node t₁ data₁ .black t₂) data₂ .red (.node t₃ d .black right)
  | left, right => .node left d .black right

-- Balanced insert into the right child, fixing red on red sequences on the way.
@[inline]
def baliR (d : α) : Raw α → Raw α → Raw α
  | left, .node t₁ data₁ .red (.node t₂ data₂ .red t₃)
  | left, .node (.node t₁ data₁ .red t₂) data₂ .red t₃ =>
      .node (.node left d .black t₁) data₁ .red (.node t₂ data₂ .black t₃)
  | left, right => .node left d .black right

-- TODO: Immutable beans says that, due to FBIP stuff, instead of:
-- insert (T B a y b) x = balance1 y b (insert a x) if x < y and a is red
-- it is more efficient to do:
-- insert (T B a y b) x = balance1 (T B E y b) (insert a x) if x < y and a is red
-- but that doesnt seem to be done in lean4-std?
def ins (d : α) (t : Raw α) : Raw α :=
  match t with
  | .nil => .node .nil d .red  .nil
  | .node left data .black right =>
    match compare d data with
    | .lt => baliL data (ins d left) right
    | .eq => t
    | .gt => baliR data left (ins d right)
  | .node left data .red right =>
    match compare d data with
    | .lt => .node (ins d left) data .red right
    | .eq => t
    | .gt => .node left data .red (ins d right)

/--
Insert `d` into `t`.
-/
def insert (d : α) (t : Raw α) : Raw α :=
  paintColor .black (ins d t)

-- Balance a tree on the way up from deletion, prioritizing the left side.
def baldL (d : α) : Raw α → Raw α → Raw α
  | .node t₁ data .red t₂, right =>
      .node (.node t₁ data .black t₂) d .red right
  | left, .node t₁ data .black t₂ =>
      baliR d left (.node t₁ data .red t₂)
  | left, .node (.node t₁ data₁ .black t₂) data₂ .red t₃ =>
      .node (.node left d .black t₁) data₁ .red (baliR data₂ t₂ (paintColor .red t₃))
  | left, right => .node left d .red right

-- Balance a tree on the way up from deletion, prioritizing the right side.
def baldR (d : α) : Raw α → Raw α → Raw α
  | left, .node t₁ data .red t₂ =>
      .node left d .red (.node t₁ data .black t₂)
  | .node t₁ data .black t₂, right =>
      baliL d (.node t₁ data .red t₂) right
  | .node t₁ data₁ .red (.node t₂ data₂ .black t₃), right =>
      .node (baliL data₁ (paintColor .red t₁) t₂) data₂ .red (.node t₃ d .black right)
  | left, right => .node left d .red right

-- Appends one tree to another while painting the correct color
def appendTrees : Raw α → Raw α → Raw α
  | .nil, t => t
  | t, .nil => t
  | .node left₁ data₁ .red right₁, .node left₂ data₂ .red right₂ =>
    match appendTrees right₁ left₂ with
    | .node left₃ data₃ .red right₃ =>
        .node (.node left₁ data₁ .red left₃) data₃ .red (.node right₃ data₂ .red right₂)
    | t                             => .node left₁ data₁ .red (.node t data₂ .red right₂)
  | .node left₁ data₁ .black right₁, .node left₂ data₂ .black right₂ =>
    match appendTrees right₁ left₂ with
    | .node left₃ data₃ .red right₃ =>
        .node (node left₁ data₁ .black left₃) data₃ .red (.node right₃ data₂ .black right₂)
    | t                             => baldL data₁ left₁ (.node t data₂ .black right₂)
  | t, .node left data .red right => .node (appendTrees t left) data .red right
  | .node left data .red right, t => .node left data .red (appendTrees right t)

def del (d : α) : Raw α → Raw α
  | .nil => .nil
  | .node left data _ right =>
    match compare d data with
    | .lt =>
      if left.isBlack then
        baldL data (del d left) right
      else
        .node (del d left) data .red right
    | .eq => appendTrees left right
    | .gt =>
      if right.isBlack then
        baldR data left (del d right)
      else
        .node left data .red (del d right)

/--
Erase `d` from `t`, if `d` is not in `t` leave it untouched.
-/
def erase (d : α) (t : Raw α) : Raw α :=
  paintColor .black (del d t)

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

def inorder : Raw α → List α
  | Raw.nil => []
  | Raw.node l x _ r => inorder l ++ [x] ++ inorder r

private def inorder2 : Raw α → List α → List α
  | Raw.nil, l => l
  | Raw.node l x _ r, xs => inorder2 l <| x :: inorder2 r xs

example : inorder2 t xs = inorder t ++ xs := by
  induction t generalizing xs with
  | nil => simp [inorder2, inorder]
  | node _ _ _ _ ihl ihr => simp [inorder2, inorder, ihl, ihr]

/--
Compute the height of `t`.
-/
def height (t : Raw α) : Nat :=
  match t with
  | .nil => 0
  | .node left _ _ right => max (height left) (height right) + 1

/--
Transform a tree into a graphviz compatible format.
-/
def toGraphviz {α : Type} [ToString α] (t : Raw α) : String :=
  let ⟨graph, _⟩ := go "Digraph tree {\n  node [style=filled];" 1 t
  graph ++ "\n}"
where
  go {α : Type} [ToString α] (acc : String) (idx : Nat) (t : Raw α) : String × Nat :=
    match t  with
    | Raw.nil =>
      ⟨acc ++ s!"\n  {idx} [shape=point];", idx⟩
    | Raw.node l x c r =>
      let node := s!"\n  {idx} [label=\"{x}\",{colorEdgeStyle c}, shape=circle];"
      let ⟨lnode, lidx⟩ := go (acc ++ node) (idx+1) l
      let ⟨rnode, ridx⟩ := go lnode (lidx+1) r
      let edges := s!"\n  {idx} -> {idx+1} [label=\"l\"];\n  {idx} -> {lidx+1} [label=\"r\"];"
      ⟨rnode ++ edges, ridx⟩
  colorEdgeStyle : Color → String
    | .red => " color=red"
    | .black => " color=grey"

/--
`x` is a member of a red black tree.
-/
inductive Mem (x : α) : Raw α → Prop where
  | here : Mem x (.node left x color right)
  | left (hleft : Mem x left) : Mem x (.node left y color right)
  | right (hright : Mem x right) : Mem x (.node left y color right)

instance : Membership α (Raw α) where
  mem t x := Mem x t

/--
A tree is a binary search tree.
-/
inductive BST : Raw α → Prop where
  | nil : BST .nil
  | node (hleft1 : ∀ x ∈ left, x < data) (hleft2 : BST left)
         (hright1 : ∀ x ∈ right, data < x) (hright2 : BST right) : BST (.node left data color right)

attribute [pp_nodot] BST

/--
Returns the amount of elements in `t`.
-/
def size (t : Raw α) : Nat :=
  match t with
  | .nil => 0
  | .node l _ _ r => size l + size r + 1

end Raw

end Internal
end Filrb
