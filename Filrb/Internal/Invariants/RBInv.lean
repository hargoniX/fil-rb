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
theorem childInv_color_independent {l r : Raw α} (h : ChildInv (.node l d c r)) :
    ChildInv (.node l d .black r) := by
  rw [childInv_black_node]
  apply childInv_node h

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem childInv_paintColorBlack_of_childInv (t : Raw α) (h : ChildInv t) :
    ChildInv (t.paintColor .black) := by
  unfold paintColor
  split <;> aesop

@[aesop safe apply]
theorem childInv2_of_childInvL (hl : ChildInv l) (hr : ChildInv r) :
    ChildInv2 (.node l d c r) := by
  simp [ChildInv2, paintColor, hl, hr]

def blackHeightLeft (t : Raw α) : Nat :=
  match t with
  | .nil => 0
  | .node left _ color _ =>
    match color with
    | .black => blackHeightLeft left + 1
    | .red => blackHeightLeft left

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
