import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Ordering.Basic
import Mathlib.Order.Compare


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

class LawfulOrd (α : Type u) [LT α] [Ord α] where
  compares : ∀ (a b : α), (compare a b).Compares a b

instance [Preorder α] [Ord α] [LawfulOrd α] : LinearOrder α :=
  linearOrderOfCompares compare LawfulOrd.compares

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

/--
Fetch the color of the root of `t`.
-/
def rootColor (t : Raw α) : Color :=
  match t with
  | .nil => .black
  | .node _ _ c _ => c

/--
Paint the color of the root of `t` to given color `c`.
-/
def paintColor (c : Color) (t : Raw α) : Raw α :=
  match t with
  | .nil => .nil
  | .node l d _ r => .node l d c r

/-
  Insertion: Helper Functions
-/

-- Balanced insert into the left child, fixing red on red sequences on the way.
def baliL (d : α) : Raw α → Raw α → Raw α
  | .node (.node t₁ data₁ .red t₂) data₂ .red t₃, right =>
      .node (.node t₁ data₁ .black t₂) data₂ .red (.node t₃ d .black right)
  | .node t₁ data₁ .red (.node t₂ data₂ .red t₃), right =>
      .node (.node t₁ data₁ .black t₂) data₂ .red (.node t₃ d .black right)
  | left, right => .node left d .black right

-- Balanced insert into the right child, fixing red on red sequences on the way.
def baliR (d : α) : Raw α → Raw α → Raw α
  | left, .node t₁ data₁ .red (.node t₂ data₂ .red t₃)=>
      .node (.node left d .black t₁) data₁ .red (.node t₂ data₂ .black t₃)
  | left, .node (.node t₁ data₁ .red t₂) data₂ .red t₃=>
      .node (.node left d .black t₁) data₁ .red (.node t₂ data₂ .black t₃)
  | left, right => .node left d .black right

def ins (t : Raw α) (d : α) : Raw α :=
  match t with
  | .nil => .node .nil d .red  .nil
  | .node left data .black right =>
    match compare d data with
    | .lt => baliL data (ins left d) right
    | .eq => t
    | .gt => baliR data left (ins right d)
  | .node left data .red right =>
    match compare d data with
    | .lt => .node (ins left d) data .red right
    | .eq => t
    | .gt => .node left data .red (ins right d)

/--
Insert `d` into `t`.
-/
def insert (t : Raw α) (d : α) : Raw α :=
  paintColor .black (ins t d)

/--
  Helper Functions for deletion
-/
-- Balanced deletion of an element from the left child, fixing red on red sequences on the way.
def baldL (d : α) : Raw α → Raw α → Raw α
  | .node t₁ data .red t₂, right =>
      .node (.node t₁ data .black t₂) d .red right
  | left, .node t₁ data .black t₂ =>
      baliR d left (.node t₁ data .red t₂)
  | left, .node (.node t₁ data₁ .black t₂) data₂ .red t₃ =>
      .node (.node left d .black t₁) data₁ .red (baliR data₂ t₂ (paintColor .red t₃))
  | left, right => .node left d .red right

-- Balanced deletion of an element from the right child, fixing red on red sequences on the way.
def baldR (d : α) : Raw α → Raw α → Raw α
  | left, .node t₁ data .red t₂ =>
      .node left d .red (.node t₁ data .black t₂)
  | .node t₁ data .black t₂, right =>
      baliL d (.node t₁ data .red t₂) right
  | .node  t₁ data₁ .red (.node t₂ data₂ .black t₃), right =>
      .node (baliL data₁ (paintColor .red t₁) t₂) data₁ .red (.node t₃ data₂ .black right)
  | left, right => .node left d .red right


def del (t : Raw α) (d : α) : Raw α :=
  match t with
  | .nil => .nil
  | .node left data _ right =>
    match compare d data with
    | .lt =>
      let left' := del left d
      match left with
      | .nil => .node left' data .red right
      | .node _ _ .black _ => baldL d left' right
      | .node _ _ _ _ => .node left' data .red right
    | .eq =>
      match right with
      | .nil => left
      | .node _ _ _ _ =>
          match split_min right with
          | none => .nil -- TODO: the book gives the impression that this codepath is dead
          | some ⟨data',right'⟩ => match rootColor right with
            | .black => baldR data' left right'
            | .red => .node left data' .red right'
    | .gt =>
      let right' := del right d
      match right with
      | .nil => .node left data .red right'
      | .node _ _ .black _ => baldL d left right'
      | .node _ _ _ _ => .node left data .red right'
  where
    -- We adapt the function of the book since it doesnt handle the (dead) code path of .nil
    -- It computes the minimum value a tree has stored inside of it and its corresponding node?
    split_min : Raw α → Option (α × Raw α)
    | .nil => none
    | .node left data _ right =>
      match left with
      | .nil => some ⟨data, right⟩
      | .node _ _ _ _ =>
          match split_min left with
          | none => none
          | some ⟨data',left'⟩ => match rootColor left with
            | .black => some ⟨data', baldL data left' right⟩
            | .red => some ⟨data', .node left' data .red right⟩

/--
Erase `d` from `t`, if `d` is not in `t` leave it untouched.
-/
def erase (t : Raw α) (d : α) : Raw α :=
  paintColor .black (del t d)

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

def inorder2 : Raw α → List α → List α
| Raw.nil, l => l
| Raw.node l x _ r, xs => inorder2 l <| x :: inorder2 r xs

example : inorder2 t xs = inorder t ++ xs := by
  induction t generalizing xs with
  | nil => simp [inorder2, inorder]
  | node _ _ _ _ ihl ihr => simp [inorder2, inorder, ihl, ihr]

/--
Transform a tree into a graphviz compatible format.
-/
def toGraphviz {α : Type} [BEq α] [ToString α] [Hashable α] (t : Raw α) : String :=
  let ⟨graph, _⟩ := go "" 1 t
  "Digraph tree {\n  node [style=filled];" ++ graph ++ "\n}"
where
  go {α : Type} [ToString α] (acc : String) (idx : Nat) (t : Raw α) : String × Nat :=
    match t  with
    | Raw.nil =>
      ⟨acc ++ s!"\n  {idx} [shape=point];", idx⟩
    | Raw.node l x c r =>
      let node := s!"\n  {idx} [label=\"{x}\",{colorEdgeStyle c}, shape=circle];"
      let ⟨lnode, lidx⟩ := go "" (idx+1) l
      let ⟨rnode, ridx⟩ := go "" (lidx+1) r
      let edges := s!"\n  {idx} -> {idx+1} [label=\"l\"];\n  {idx} -> {lidx+1} [label=\"r\"];"
      ⟨acc ++ node ++ lnode ++ rnode ++ edges, ridx⟩
  colorEdgeStyle : Color → String
    | .red => " color=red"
    | .black => " color=grey"

/--
Transform a tree into a graphviz compatible format without explicit leafs.
-/
def toGraphviz2 {α : Type} [BEq α] [ToString α] [Hashable α] (t : Raw α) : String :=
  let graph := go "" t
  "Digraph tree {\n  node [style=filled];" ++ graph ++ "\n}"
where
  go {α : Type} [ToString α] (acc : String) (t : Raw α) : String :=
    match t  with
    | Raw.nil => acc
    | Raw.node l x c r =>
      let node := s!"\n  {x} [label=\"{x}\",{colorEdgeStyle c}, shape=circle];"
      let ledge := graphEdge x "l" l
      let redge := graphEdge x "r" r
      let lnode := go "" l
      let rnode := go "" r
      acc ++ node ++ lnode ++ rnode ++ ledge ++ redge
  colorEdgeStyle : Color → String
    | .red => " color=red"
    | .black => " color=grey"
  graphEdge {α : Type} [ToString α] (parentVal : α) (label : String) : Raw α → String
    | .nil => ""
    | .node _ x _ _ => s!"\n  {parentVal} -> {x} [label=\"{label}\"];"

def exTree1 : Raw Int := insert (insert (insert .nil 0) 2) 4
def exTree2 : Raw Int := insert exTree1 1
def exTree3 : Raw Int := erase exTree2 1
def exTree4 : Raw Int := insert (insert (insert (insert (insert .nil 100) 0) 500) 110) 105
#eval IO.FS.writeFile "examples/tree-preinsert.gv" exTree1.toGraphviz
#eval IO.FS.writeFile "examples/tree-postinsert.gv" exTree2.toGraphviz
#eval IO.FS.writeFile "examples/tree-postdeletion.gv" exTree3.toGraphviz
#eval IO.FS.writeFile "examples/tree-4.gv" exTree4.toGraphviz

/--
`x` is a member of a red black tree.
-/
inductive Mem (x : α) : Raw α → Prop where
  | here : Mem x (.node left x color right)
  | left (hleft : Mem x left) : Mem x (.node left y color right)
  | right (hright : Mem x right) : Mem x (.node left y color right)

instance : Membership α (Raw α) where
  mem t x := Mem x t

end Raw

end Internal
end Filrb
