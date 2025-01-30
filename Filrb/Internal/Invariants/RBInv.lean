import Filrb.Internal.Raw
import Filrb.Internal.Invariants.BST

/-!
This module proves that our functionality preserves the `RedBlackTree` invariant,
which is a combination of the `ChildInv` and the `HeightInv` invariant.
-/

namespace Filrb
namespace Internal

namespace Raw

variable [Preorder α] [Ord α] [LawfulOrd α]

-- TODO: Find a place for these, but this will require some maintenance
omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem paintColor_nil : paintColor c (.nil : Raw α) = Raw.nil := by
  simp [paintColor]

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem paintColor_node : paintColor c (.node l d c' r) = .node l d c r := by
  simp [paintColor]

omit [Preorder α] [LawfulOrd α] in
@[simp]
theorem del_nil {x : α} : del x Raw.nil = Raw.nil := by
  simp [del]

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem rootColor_nil : (Raw.nil : Raw α).rootColor = Color.black := by
  simp [rootColor]

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem rootColor_node : (Raw.node l d c r).rootColor = c := by
  simp [rootColor]

@[simp]
theorem isBlack_node : (node l d c r).isBlack = (c == .black) := by
  cases c <;> simp [isBlack]

/--
The child invariant for red black trees: Red nodes must have black children.
-/
inductive ChildInv : Raw α → Prop where
  | nil : ChildInv .nil
  | black (hleft : ChildInv left) (hright : ChildInv right) : ChildInv (.node left data .black right)
  | red (hleft1 : ChildInv left) (hleft2 : left.rootColor = .black) (hright1 : ChildInv right)
        (hright2 : right.rootColor = .black) : ChildInv (.node left data .red right)

attribute [pp_nodot] ChildInv

/--
A weaker child invariant for red black trees,
where only the childs of a node have to preserve the invariant.
-/
def ChildInv2 (t : Raw α) : Prop :=
  ChildInv (paintColor .black t)

attribute [pp_nodot] ChildInv2

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem childInv_nil : ChildInv (.nil : Raw α) := ChildInv.nil

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem childInv2_nil : ChildInv2 (.nil : Raw α) := ChildInv.nil

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem childInv_red_node {l r : Raw α} :
    ChildInv (.node l d .red r) ↔ ChildInv l ∧ (l.rootColor = .black) ∧ ChildInv r ∧ (r.rootColor = .black) := by
  constructor
  · intro h
    cases h
    simp_all
  · rintro ⟨_, _, _, _⟩
    apply ChildInv.red <;> assumption

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem childInv_black_node {l r : Raw α} :
    ChildInv (.node l d .black r) ↔ ChildInv l ∧ ChildInv r := by
  constructor
  · intro h
    cases h
    simp_all
  · rintro ⟨_, _⟩
    apply ChildInv.black <;> assumption

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[aesop safe forward]
theorem childInv_node {l r : Raw α} (h : ChildInv (.node l d c r)) :
    ChildInv l ∧ ChildInv r := by
  rcases h <;> simp_all

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem childInv2_node {l r : Raw α} :
    ChildInv2 (.node l d c r) ↔ ChildInv l ∧ ChildInv r := by
  constructor
  · intro h
    cases h
    simp_all
  · rintro ⟨_, _⟩
    apply ChildInv.black <;> assumption

def blackHeightLeft (t : Raw α) : Nat :=
  match t with
  | .nil => 0
  | .node left _ color _ =>
    match color with
    | .black => blackHeightLeft left + 1
    | .red => blackHeightLeft left

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem blackHeight_nil : (.nil : Raw α).blackHeightLeft = 0 := by
  simp [blackHeightLeft]

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem blackHeight_black_node {l r : Raw α} :
    (node l d .black r).blackHeightLeft = l.blackHeightLeft + 1 := by
  simp [blackHeightLeft]

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem blackHeight_red_node {l r : Raw α} :
    (node l d .red r).blackHeightLeft = l.blackHeightLeft := by
  simp [blackHeightLeft]

/--
The height invariant for red black trees: Every path from a given node to any of its leaves goes
through the same number of black nodes.

The particular variant here is based on
[Functional Algorithms Verified](https://functional-algorithms-verified.org/functional_data_structures_algorithms.pdf)
and uses a sufficient condition instead of directly encoding the above.
-/
inductive HeightInv : Raw α → Prop where
  | nil : HeightInv .nil
  | node (hleft : HeightInv left) (hright : HeightInv right)
         (h : left.blackHeightLeft = right.blackHeightLeft) : HeightInv (.node left data color right)

attribute [pp_nodot] HeightInv

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem heightInv_nil : HeightInv (.nil : Raw α) := HeightInv.nil

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem heightInv_node {l r : Raw α} :
    HeightInv (node l d c r) ↔
    HeightInv l ∧ HeightInv r ∧ l.blackHeightLeft = r.blackHeightLeft := by
  constructor
  · intro h
    cases h
    simp_all
  · rintro ⟨_, _, _⟩
    apply HeightInv.node <;> assumption

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem heightInv_paintColor_independent {t : Raw α} {c : Color} :
    HeightInv (t.paintColor c) ↔ HeightInv t := by
  unfold paintColor
  aesop

theorem rbInv_insert_of_rbInv (x : α) (t : Raw α) (hc : ChildInv t) (hh : HeightInv t) :
    ChildInv (t.insert x) ∧ HeightInv (t.insert x) := by
  sorry

theorem rbInv_baldL_of_rbInv {x : α} {l r t : Raw α}
    (hcl : ChildInv2 l) (hcr : ChildInv r)
    (hhl : HeightInv l) (hhr : HeightInv r)
    (hbh : blackHeightLeft l + 1 = blackHeightLeft r) (heq : baldL x l r = t) :
    (if r.isBlack then ChildInv t ∧ ChildInv2 t else ChildInv2 t)
    ∧ HeightInv t ∧ blackHeightLeft t = blackHeightLeft r := by
  sorry

theorem rbInv_baldR_of_rbInv {x : α} {l r t : Raw α}
    (hcl : ChildInv l) (hcr : ChildInv2 r)
    (hhl : HeightInv l) (hhr : HeightInv r)
    (hbh : blackHeightLeft l = blackHeightLeft r + 1) (heq : baldR x l r = t) :
    (if l.isBlack then ChildInv t ∧ ChildInv2 t else ChildInv2 t)
    ∧ HeightInv t ∧ blackHeightLeft t = blackHeightLeft l := by
  sorry

-- 8.1 has a requirement that for `split_min t = (x,t')` t has to be not nil?
theorem rbInv_appendTrees_of_rbInv {l r t : Raw α} (hc : ChildInv (.node l d c r))
    (hh : HeightInv (.node l d c r)) (heq : appendTrees l r = t) :
    (if c = .black then
      blackHeightLeft t = blackHeightLeft l - 1 ∧ ChildInv2 t
    else
      blackHeightLeft t = blackHeightLeft l ∧ ChildInv t)
    ∧ HeightInv t' := by
  sorry

theorem rbInv_del_of_rbInv {t t' : Raw α}
    (hc : ChildInv t) (hh : HeightInv t) (heq : del x t = t') :
    (if t.isBlack then
      blackHeightLeft t' = blackHeightLeft t - 1 ∧ ChildInv2 t'
    else
      blackHeightLeft t' = blackHeightLeft t ∧ ChildInv t')
    ∧ HeightInv t' := by
  sorry

theorem rbInv_erase_of_rbInv (x : α) (t : Raw α) (hc : ChildInv t) (hh : HeightInv t) :
    ChildInv (t.erase x) ∧ HeightInv (t.erase x) := by
  sorry

end Raw
end Internal
end Filrb
