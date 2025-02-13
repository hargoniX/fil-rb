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

@[aesop safe forward]
theorem rootColor_of_isBlack (h : t.isBlack) : rootColor t = .black := by
  unfold isBlack at h
  split at h
  . simp
  . simp_all

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[aesop safe forward]
theorem node_of_isBlack {t : Raw α} (h : t.isBlack) :
    ∃ l d r, t = .node l d .black r := by
  cases t with
  | nil => simp_all [isBlack]
  | node l d c r =>
    exists l, d, r
    unfold isBlack at h
    split at h <;> simp_all

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[aesop safe forward]
theorem node_of_rootColor_eq_red {t : Raw α} (h : t.rootColor = .red) :
    ∃ l d r, t = .node l d .red r := by
  cases t with
  | nil => simp_all
  | node l d c r =>
    exists l, d, r
    simp_all

@[simp]
theorem red_of_not_black {c : Color} : c ≠ .black ↔ c = .red := by
  cases c <;> simp_all

@[simp]
theorem black_of_not_red {c : Color} : c ≠ .red  ↔ c = .black := by
  cases c <;> simp_all


omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem rootColor_black_of_not_red {t : Raw α}
    (h : ∀ (l : Raw α) (d : α) (r : Raw α), t = node l d .red r → False) :
    rootColor t = .black := by
  cases ht : t with
  | nil => simp
  | node l d c r =>
    have := h l d r
    aesop

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem paintColor_black_rootColor_eq_black {t : Raw α} :
    (t.paintColor .black).rootColor = .black := by
  cases t <;> simp

omit [Preorder α] [LawfulOrd α] in
@[simp]
theorem rootColor_insert_eq_black {t : Raw α} {x : α} : (t.insert x).rootColor = .black := by
  cases t <;> simp [insert]

omit [Preorder α] [LawfulOrd α] in
@[simp]
theorem rootColor_erase_eq_black {t : Raw α} {x : α} : (t.erase x).rootColor = .black := by
  cases t <;> simp [erase]

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem nil_appendTrees {t : Raw α} :
    (nil : Raw α).appendTrees t = t := by
  simp [appendTrees]

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem appendTrees_nil {t : Raw α} :
    t.appendTrees (nil : Raw α) = t := by
  cases t <;> simp [appendTrees]

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem black_appendTrees {l r : Raw α} (h : rootColor (l.appendTrees r) = .black) :
    rootColor l = .black ∧ rootColor r = .black := by
  induction l, r using appendTrees.induct with
  | case1 => aesop
  | case2 => aesop
  | case3 =>
    apply False.elim
    simp only [appendTrees] at h
    aesop
  | case4 => simp [appendTrees] at h
  | case5 => aesop
  | case6 => aesop
  | case7 => simp [appendTrees] at h
  | case8 => simp [appendTrees] at h

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
  cases h <;> simp_all

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

-- TODO: Unable to make this as an aesop rule since any node will be simped into ChildInvs again :/
omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem childInv2_of_childInv {t : Raw α} (h : ChildInv t) : ChildInv2 t := by
  cases t
  . simp
  . have := childInv_node h
    simp [this]

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem childInv2_of_paintColor_childInv {t : Raw α} (hc : ChildInv t) :
    ChildInv2 (paintColor .red t) := by
  unfold paintColor
  aesop

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

theorem rbInv_baliL_of_rbInv {x : α} {l r : Raw α}
    (hcl : ChildInv2 l) (hcr : ChildInv r)
    (hhl : HeightInv l) (hhr : HeightInv r)
    (hbh : blackHeightLeft l = blackHeightLeft r) :
    ChildInv (baliL x l r) ∧ HeightInv (baliL x l r) ∧ blackHeightLeft (baliL x l r) = blackHeightLeft l + 1 := by
  sorry

theorem rbInv_baliR_of_rbInv {x : α} {l r : Raw α}
    (hcl : ChildInv l) (hcr : ChildInv2 r)
    (hhl : HeightInv l) (hhr : HeightInv r)
    (hbh : blackHeightLeft l = blackHeightLeft r) :
    ChildInv (baliR x l r) ∧ HeightInv (baliR x l r) ∧ blackHeightLeft (baliR x l r) = blackHeightLeft l + 1 := by
  sorry

lemma rbInv_baliL_of_rbInv (l r : Raw α) (hl : HeightInv l) (hr : HeightInv r) (hcl: ChildInv2 l)
    (hcr: ChildInv r) (hh: blackHeightLeft l = blackHeightLeft r) :
    (ChildInv (baliL x l r)) ∧ HeightInv (baliL x l r) ∧ blackHeightLeft (baliL x l r) = blackHeightLeft l + 1 := sorry

lemma rbInv_baliR_of_rbInv (l r : Raw α) (hl : HeightInv l) (hr : HeightInv r) (hcl: ChildInv l)
    (hcr: ChildInv2 r) (hh: blackHeightLeft l = blackHeightLeft r) :
    (ChildInv (baliR x l r)) ∧ HeightInv (baliR x l r) ∧ blackHeightLeft (baliR x l r) = blackHeightLeft l + 1 := sorry


lemma rbInv_ins_of_rbInv (x : α) (t : Raw α) (hc1 : ChildInv t) (hh : HeightInv t) :
    (if t.rootColor == .black then ChildInv (ins x t) else ChildInv2 (ins x t) ) ∧ (HeightInv (ins x t)) := by
     induction t with
     | nil =>
        simp_all only [childInv_nil, heightInv_nil, rootColor_nil, beq_self_eq_true, ↓reduceIte]
        apply And.intro
        · unfold ins; aesop
        · unfold ins; aesop
     | node left data color right lih rih =>
        have hcl : ChildInv left := by aesop
        have hhl : HeightInv left := by aesop
        have hcr : ChildInv right := by aesop
        have hhr : HeightInv right := by aesop
        have hl := lih hcl hhl -- new ih for left
        have hr := rih hcr hhr -- new ih for right
        -- the goal contains an ∧ operator, but it seems like I cannot split it
        -- baliL and baliR make their job especially during HeightInv
        split
        · next h =>-- big case 1: root color is black, ChildInv
          sorry
        · -- big case 2: root color is red, ChildInv2
          sorry



theorem rbInv_insert_of_rbInv (x : α) (t : Raw α) (hc : ChildInv t) (hh : HeightInv t) :
    ChildInv (t.insert x) ∧ HeightInv (t.insert x) := by
    simp[insert]
    simp[paintColor]
    split
    · simp_all
    · next t1 left data c right heq =>
      have := rbInv_ins_of_rbInv x t hc hh
      split at this <;> aesop

theorem rbInv_baldL_of_rbInv {x : α} {l r t : Raw α}
    (hcl2 : ChildInv2 l) (hcr : ChildInv r)
    (hhl : HeightInv l) (hhr : HeightInv r)
    (hbh : blackHeightLeft l + 1 = blackHeightLeft r) (heq : baldL x l r = t) :
    (if r.isBlack then ChildInv t else ChildInv2 t)
    ∧ HeightInv t ∧ blackHeightLeft t = blackHeightLeft r := by
  unfold baldL at heq
  split at heq
  . aesop
  . rename_i lnr
    simp only [isBlack_node, beq_self_eq_true, ↓reduceIte, blackHeight_black_node]
    simp only [blackHeight_black_node, Nat.add_right_cancel_iff] at hbh
    rw [← hbh]
    subst heq
    have := rootColor_black_of_not_red lnr
    cases l <;> apply rbInv_baliR_of_rbInv <;> aesop
  . rename_i rll rld rlr rd rr lnr
    have : ChildInv2 (paintColor Color.red rr) := by
      apply childInv2_of_paintColor_childInv
      aesop
    have : rlr.blackHeightLeft = (paintColor Color.red rr).blackHeightLeft := by
      aesop (add norm paintColor)
    have := rbInv_baliR_of_rbInv (x := rd) (l := rlr) (r := paintColor .red rr)
    have := rootColor_black_of_not_red lnr
    cases l <;> aesop
  -- Given our Invariants, the last case of baldL cannot be reached.
  -- We can easily proof this by case analysis on ChildInv r
  . cases hcr
    -- Cannot be nil due to the height difference
    . simp only [blackHeight_nil, Nat.add_one_ne_zero] at hbh
    -- Cannot be black since an earlier case already handles r as a black node
    . aesop
    -- Cannot be red:
    -- - with nil childs: since right has a higher bh than left
    -- - with red node childs: since ChildInv r doesnt allow for red-red connections
    -- - with black node childs: since its an earlier case
    . rename_i lnr rl rr rd hl1 hl2 hr1 hr2 rnb rnr
      simp only [node.injEq, true_and, imp_false, not_and, forall_apply_eq_imp_iff₂, forall_apply_eq_imp_iff] at rnr
      simp only [isBlack, Bool.false_eq_true, ↓reduceIte, blackHeight_red_node]
      cases rl with
      | nil =>
        simp only [heightInv_node, heightInv_nil, true_and] at hhr
        simp [← hhr.right] at hbh
      | node => aesop

theorem rbInv_baldR_of_rbInv {x : α} {l r t : Raw α}
    (hcl : ChildInv l) (hcr : ChildInv2 r)
    (hhl : HeightInv l) (hhr : HeightInv r)
    (hbh : blackHeightLeft l = blackHeightLeft r + 1) (heq : baldR x l r = t) :
    (if l.isBlack then ChildInv t else ChildInv2 t)
    ∧ HeightInv t ∧ blackHeightLeft t = blackHeightLeft l := by
  unfold baldR at heq
  split at heq
  . aesop
  . rename_i rnr
    simp only [isBlack_node, beq_self_eq_true, ↓reduceIte, blackHeight_black_node]
    simp only [blackHeight_black_node, Nat.add_right_cancel_iff] at hbh
    subst heq
    have := rootColor_black_of_not_red rnr
    cases r <;> apply rbInv_baliL_of_rbInv <;> aesop
  . rename_i lll lld llr ld lr rnr
    have : ChildInv2 (paintColor Color.red lll) := by
      apply childInv2_of_paintColor_childInv
      aesop
    have : (paintColor Color.red lll).blackHeightLeft = llr.blackHeightLeft := by
      simp only [blackHeight_red_node] at hbh
      aesop (add norm paintColor)
    have := rbInv_baliL_of_rbInv (x := lld) (l := paintColor .red lll) (r := llr)
    have := rootColor_black_of_not_red rnr
    cases r <;> aesop
  -- Given our Invariants, the last case of baldR cannot be reached.
  -- We can easily proof this by case analysis on ChildInv l
  . cases hcl
    -- Cannot be nil due to the height difference
    . simp only [blackHeight_nil, Nat.self_eq_add_left, Nat.add_one_ne_zero] at hbh
    -- Cannot be black since an earlier case already handles l as a black node
    . aesop
    -- Cannot be red:
    -- - with nil childs: since left has a higher bh than right
    -- - with red node childs: since ChildInv l doesnt allow for red-red connections
    -- - with black node childs: since its an earlier case
    . rename_i rnr ll lr ld hl1 hl2 hr1 hr2 lnb lnr
      simp only [node.injEq, true_and, imp_false, not_and, forall_apply_eq_imp_iff₂, forall_apply_eq_imp_iff] at lnr
      simp only [isBlack, Bool.false_eq_true, ↓reduceIte, blackHeight_red_node]
      cases ll with
      | nil =>
        simp only [heightInv_node, heightInv_nil, true_and] at hhl
        simp [← hhl.right] at hbh
      | node lll lld llc llr =>
        cases lr with
        | nil => simp_all
        | node lrl lrd lrc lrr =>
          have := lnr (.node lll lld llc llr) ld
          aesop

-- In contrast to Lemma 8.1, which reasons about split_min,
-- appendTrees is way simpler in its input/output relations.
-- We know: appendTrees reduces the tree height if the node was black
-- This is maybe not as precise as it could be, but it is enough for what we need it.
theorem rbInv_appendTrees_of_rbInv {l r : Raw α}
    (hc : ChildInv (.node l d c r)) (hh : HeightInv (.node l d c r)) :
    (if c = .black then
       ChildInv2 (appendTrees l r) ∧
       blackHeightLeft (appendTrees l r) = blackHeightLeft (.node l d c r) - 1
     else
       ChildInv (appendTrees l r) ∧
       blackHeightLeft (appendTrees l r) = blackHeightLeft (.node l d c r))
    ∧ HeightInv (appendTrees l r) := by
  unfold appendTrees
  split
  . rename_i hcb
    split
    . aesop (add safe forward childInv2_of_childInv)
    . aesop (add safe forward childInv2_of_childInv)
    . rename_i left1 data1 right1 left2 data2 right2
      simp only [hcb, childInv_black_node, childInv_red_node, heightInv_node,
        blackHeight_red_node] at hc hh
      have := rbInv_appendTrees_of_rbInv (d := d) (c := .red) (l := right1) (r := left2)
      aesop (add safe forward rootColor_black_of_not_red)
    . rename_i left1 data1 right1 left2 data2 right2
      simp only [hcb, blackHeight_black_node, Nat.add_one_sub_one]
      simp only [hcb, childInv_black_node, heightInv_node, blackHeight_black_node,
        Nat.add_right_cancel_iff] at hc hh
      split
      . have := rbInv_appendTrees_of_rbInv (d := d) (c := .black) (l := right1) (r := left2)
        aesop
      . rename_i happnr
        have := rootColor_black_of_not_red happnr
        have := rbInv_appendTrees_of_rbInv (d := d) (c := .red) (l := right1) (r := left2)
        have := rbInv_baldL_of_rbInv (x := data1) (l := left1)
            (r := .node (right1.appendTrees left2) data2 .black right2)
            (t := baldL data1 left1 (node (right1.appendTrees left2) data2 .black right2))
        aesop (add safe forward [childInv2_of_childInv, black_appendTrees])
    . rename_i left data _ _ hlnr
      have := rootColor_black_of_not_red hlnr
      have := rbInv_appendTrees_of_rbInv (d := d) (c := .red) (l := l) (r := left)
      aesop
    . rename_i right hrnl hrnr _
      simp only [hcb, childInv_black_node, childInv_red_node, heightInv_node, blackHeight_red_node] at hc hh
      have := rootColor_black_of_not_red hrnr
      have := rbInv_appendTrees_of_rbInv (d := d) (c := .red) (l := right) (r := r)
      aesop
  . rename_i hcnb
    simp only [red_of_not_black] at hcnb
    split
    . aesop
    . aesop
    . simp_all
    . rename_i left1 data1 right1 left2 data2 right2
      simp only [hcnb, blackHeight_red_node, blackHeight_black_node]
      simp only [hcnb, childInv_red_node, childInv_black_node, rootColor_node, and_true, true_and,
        heightInv_node, blackHeight_black_node, Nat.add_right_cancel_iff] at hc hh
      split
      . have := rbInv_appendTrees_of_rbInv (d := d) (c := .black) (l := right1) (r := left2)
        aesop
      . rename_i happnr
        have := rootColor_black_of_not_red happnr
        have := rbInv_appendTrees_of_rbInv (d := d) (c := .red) (l := right1) (r := left2)
        have := rbInv_baldL_of_rbInv (x := data1) (l := left1)
          (r := .node (right1.appendTrees left2) data2 .black right2)
          (t := baldL data1 left1 (node (right1.appendTrees left2) data2 .black right2))
        aesop (add safe forward [childInv2_of_childInv, black_appendTrees])
    . simp_all
    . simp_all

theorem rbInv_del_of_rbInv {t t' : Raw α}
    (hc : ChildInv t) (hh : HeightInv t) (heq : del x t = t') :
    (if t.rootColor = .black then
      blackHeightLeft t' = blackHeightLeft t - 1 ∧ ChildInv2 t'
    else
      blackHeightLeft t' = blackHeightLeft t ∧ ChildInv t')
    ∧ HeightInv t' := by
  induction t using del.induct generalizing t' with
  | d =>  exact x
  | case1 => aesop
  | case2 l d c r hord lb ih =>
    simp only [del, hord] at heq
    simp only [lb, ↓reduceIte, rootColor_of_isBlack lb, forall_apply_eq_imp_iff₂] at heq ih
    have ⟨hhl, hhr, hht⟩ := heightInv_node.mp hh
    have : (del x l).blackHeightLeft + 1 = r.blackHeightLeft := by
      symm at hht
      aesop
    have := rbInv_baldL_of_rbInv (x := d) (l := del x l) (r := r) (t := t')
    split at this
    . aesop (add safe forward childInv2_of_childInv)
    -- (l-black,) r-red -> .node l d c r has to be black
    -- We actually require heightInv to prove that the right node is red,
    -- since we only yet know that it is not a black _node_ but it could be a (black) nil
    . have hb : c = .black := by
        cases r with
        | nil => aesop
        | node rl rd rc rr =>
          cases hc
          . simp
          . aesop
      aesop
  | case3 l d c r hord lb ih =>
    have := childInv_node hc
    simp only [hord, del, lb, Bool.false_eq_true, ↓reduceIte] at heq ih
    cases l <;> aesop
  | case4 l d c r hord =>
    simp only [hord, del] at heq
    have := rbInv_appendTrees_of_rbInv hc hh
    split <;> aesop
  | case5 l d c r hord rb ih =>
    simp only [del, hord] at heq
    simp only [rb, ↓reduceIte, rootColor_of_isBlack rb, forall_apply_eq_imp_iff₂] at heq ih
    have ⟨hhl, hhr, hht⟩ := heightInv_node.mp hh
    have ⟨hcl, hcr⟩ := childInv_node hc
    have : l.blackHeightLeft = (del x r).blackHeightLeft + 1 := by aesop
    have := rbInv_baldR_of_rbInv (x := d) (l := l) (r := del x r) (t := t')
    split at this
    . aesop (add safe forward childInv2_of_childInv)
    . rename_i hrnb
      -- l-red (, r-black) -> .node l d c r has to be black
      -- We actually require heightInv to prove that the right node is red,
      -- since we only yet know that it is not a black _node_ but it could be a (black) nil
      have hb : c = .black := by
        cases l with
        | nil => aesop
        | node ll ld lc lr =>
          cases hc
          . simp
          . aesop
      aesop
  | case6 l d c r hord rb ih =>
    have := childInv_node hc
    simp only [del, hord, rb, Bool.false_eq_true, ↓reduceIte] at heq ih
    cases r <;> aesop

theorem rbInv_erase_of_rbInv (x : α) (t : Raw α) (hc : ChildInv t) (hh : HeightInv t) :
    ChildInv (t.erase x) ∧ HeightInv (t.erase x) := by
  rw [erase]
  cases heq : del x t with
  | nil => simp
  | node l d c r =>
    have := rbInv_del_of_rbInv hc hh heq
    split at this <;> aesop

end Raw
end Internal
end Filrb
