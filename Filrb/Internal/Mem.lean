import Filrb.Internal.Raw
import Aesop

/-!
This module defines the notion of membership in a raw red black tree and proves that `Raw.contains`
corresponds to this notion.
-/

namespace Filrb
namespace Internal
namespace Raw

@[simp]
theorem Mem_iff_mem {x : α} {t : Raw α} : Mem x t ↔ x ∈ t := by
  rfl

theorem mem_of_mem_left (x : α) (left : Raw α) (data : α) (color : Color) (right : Raw α) :
    x ∈ left → x ∈ (Raw.node left data color right) := by
  intro h
  apply Mem.left
  exact h

theorem mem_of_mem_right (x : α) (left : Raw α) (data : α) (color : Color) (right : Raw α) :
    x ∈ right → x ∈ (Raw.node left data color right) := by
  intro h
  apply Mem.right
  exact h

theorem mem_of_eq (x : α) (left : Raw α) (data : α) (color : Color) (right : Raw α) :
    x = data → x ∈ (Raw.node left data color right) := by
  intro h
  rw [h]
  apply Mem.here

theorem mem_color_independent (h : x ∈ (Raw.node l d c r)) : x ∈ (Raw.node l d c' r) := by
  rcases h with _ | h | h
  . simp [mem_of_eq]
  . apply mem_of_mem_left
    apply h
  . apply mem_of_mem_right
    apply h

@[simp]
theorem mem_iff_paintColor_mem (x : α) (c : Color) (t : Raw α) : x ∈ t.paintColor c  ↔ x ∈ t:= by
  rcases t
  . simp [paintColor]
  . rw [paintColor]
    constructor <;> apply mem_color_independent

variable [Ord α]

@[simp]
theorem nil_contains {x : α} : Raw.nil.contains x = false := by
  simp [contains]

omit [Ord α] in
@[simp]
theorem mem_nil {x : α} : ¬x ∈ Raw.nil := by
  intro h
  cases h

omit [Ord α] in
@[simp]
theorem mem_node {left right : Raw α} {color : Color} {data x : α} :
    x ∈ (Raw.node left data color right) ↔ (x ∈ left ∨ x = data ∨ x ∈ right) := by
  constructor
  · intro h
    cases h <;> simp_all
  · intro h
    rcases h with h1 | h2 | h3
    · apply mem_of_mem_left
      assumption
    · apply mem_of_eq
      assumption
    · apply mem_of_mem_right
      assumption

variable [Preorder α] [LawfulOrd α]

theorem mem_of_contains_eq_true {x : α} {t : Raw α} (h1 : t.contains x = true) :
    x ∈ t := by
  induction t, x using contains.induct with
  | case1 => simp at h1
  | case2 x left data color right hlt ih =>
    apply mem_of_mem_left
    apply ih
    simpa [contains, hlt] using h1
  | case3 x left data color right heq =>
    apply mem_of_eq
    simp_all
  | case4 x left data color right hlt ih =>
    apply mem_of_mem_right
    apply ih
    simpa [contains, hlt] using h1

theorem contains_eq_true_of_mem {x : α} {t : Raw α} (h1 : x ∈ t) (h2 : BST t) :
    t.contains x = true := by
  induction t, x using contains.induct with
  | case1 => cases h1
  | case2 x left data color right hlt ih =>
    simp only [contains, hlt]
    rcases h2 with rfl | ⟨hleft1, hleft2, hright1, _⟩
    apply ih
    · simp only [LawfulOrd.compare_eq_lt] at hlt
      cases h1 with
      | left => assumption
      | here =>
        exfalso
        apply lt_irrefl x
        assumption
      | right hmemright =>
        specialize hright1 x hmemright
        exfalso
        exact lt_asymm hlt hright1
    · assumption
  | case3 x left data color right heq => simp [contains, heq]
  | case4 x left data color right hlt ih =>
    simp only [contains, hlt]
    rcases h2 with rfl | ⟨hleft1, _, hright1, hright2⟩
    apply ih
    · simp only [LawfulOrd.compare_eq_gt] at hlt
      cases h1 with
      | left hmemleft =>
        specialize hleft1 x hmemleft
        exfalso
        apply lt_asymm hlt hleft1
      | here =>
        exfalso
        apply lt_irrefl x
        assumption
      | right hmemright => assumption
    · assumption

theorem contains_eq_true_iff_mem_of_bst {x : α} {t : Raw α} (h : BST t) :
    t.contains x = true ↔ x ∈ t := by
  constructor
  · apply mem_of_contains_eq_true
  · intro h
    apply contains_eq_true_of_mem <;> assumption

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[aesop safe forward]
theorem mem_of_mem_baliL {d : α} (h : x ∈ baliL d left right) : x ∈ left ∨ x ∈ right ∨ x = d := by
  unfold baliL at h
  split at h <;> aesop

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[aesop safe forward]
theorem mem_of_mem_baliR {d : α} (h : x ∈ baliR d left right) : x ∈ left ∨ x ∈ right ∨ x = d := by
  unfold baliR at h
  split at h <;> aesop

@[aesop safe forward]
theorem mem_of_mem_ins (t : Raw α) (x d : α) (h : x ∈ ins d t) : x = d ∨ x ∈ t := by
  unfold ins at h
  split at h <;> aesop (add safe forward mem_of_mem_ins)
termination_by t

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[aesop safe forward]
theorem mem_of_mem_baldL {d : α} (h : x ∈ baldL d t₁ t₂) : x ∈ t₁ ∨ x ∈ t₂ ∨ x = d := by
  unfold baldL at h
  split at h
  . aesop
  . have := mem_of_mem_baliR h
    aesop
  . rcases h with _ | h | h
    . simp
    . aesop
    . have := mem_of_mem_baliR h
      aesop
  . aesop

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[aesop safe forward]
theorem mem_of_mem_baldR {d : α} (h : x ∈ baldR d t₁ t₂) : x ∈ t₁ ∨ x ∈ t₂ ∨ x = d := by
  unfold baldR at h
  split at h
  . aesop
  . have := mem_of_mem_baliL h
    aesop
  . rcases h with _ | h | h
    . simp
    . have := mem_of_mem_baliL h
      aesop
    . aesop
  . aesop

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[aesop safe forward]
theorem mem_of_mem_appendTrees {t₁ t₂ : Raw α} (h : x ∈ appendTrees t₁ t₂) : x ∈ t₁ ∨ x ∈ t₂  := by
  induction t₁, t₂ using appendTrees.induct <;> aesop (add norm appendTrees)

@[aesop safe forward]
theorem mem_of_mem_del {d : α} (h : x ∈ del d t) : x ∈ t := by
  unfold del at h
  split at h
  . assumption
  . split at h
    . split at h <;> aesop (add safe forward mem_of_mem_del)
    . aesop
    . split at h <;> aesop (add safe forward mem_of_mem_del)
termination_by t

end Raw
end Internal
end Filrb
