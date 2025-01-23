import Mathlib.Data.List.Sort
import Filrb.Internal.Invariants
import Filrb.Internal.Mem
import Filrb.Basic

/-!
This module contains the infrastructure to lower theorems about red black tree sets to theorems
about operations on sorted lists, as well as theorems about said lists to close goals that might
arise from such lowerings.

The file is roughly structured into the following parts:
1. Define the sorted list infrastructure
2. Prove that `Internal.Raw` operations correspond to sorted list operations (potentially under
   assumptions such as the `Internal.Raw` being a binary search tree)
3. Prove lemmas about the behavior of sorted list operations.
4. Lift the lemmas from 3 and 4 onto `Set`, in particular we can use the invariants stored in `Set`
   to fulfill the previously mentioned assumptions about being a binary search tree. Furthermore
   we provide a custom tactic `simp_to_model using thm` that automatically applies all congruence
   theorems from 2. and optionally a behavior lemma from 3 to the goal.
-/

namespace Filrb
namespace Internal

variable [Preorder α] [Ord α] [LawfulOrd α]

abbrev Sorted (l : List α) := List.Sorted (· < ·) l

def sortedInsert (xs : List α) (a : α) : List α :=
  match xs with
  | [] => [a]
  | x :: xs =>
    match compare a x with
    | .lt => a :: x :: xs
    | .eq => a :: xs
    | .gt => x :: sortedInsert xs a

abbrev sortedErase (xs : List α) (a : α) : List α := List.erase xs a

omit [Preorder α] [LawfulOrd α] in
@[simp]
theorem sortedInsert_nil {a : α} : sortedInsert [] a = [a] := by
  rfl

@[simp]
theorem sortedInsert_cons_self {x : α} {xs : List α} : sortedInsert (x :: xs) x = x :: xs := by
  simp [sortedInsert]

theorem sortedInsert_cons_lt {x a : α} {xs : List α} (h : a < x) :
    sortedInsert (x :: xs) a = a :: x :: xs := by
  rw [← LawfulOrd.compare_eq_lt] at h
  simp [sortedInsert, h]

theorem sortedInsert_cons_gt {x a : α} {xs : List α} (h : x < a) :
    sortedInsert (x :: xs) a = x :: sortedInsert xs a := by
  rw [← LawfulOrd.compare_eq_gt] at h
  simp [sortedInsert, h]

theorem length_sortedInsert_of_mem {xs : List α} {k : α} (h1 : Sorted xs) (h2 : k ∈ xs) :
    (sortedInsert xs k).length = xs.length := by
  induction xs with
  | nil => simp at h2
  | cons x xs ih =>
    rw [List.mem_cons] at h2
    rcases h2 with h2 | h2
    · simp [h2]
    · rw [Sorted, List.sorted_cons] at h1
      rcases h1 with ⟨h1, h3⟩
      specialize ih h3 h2
      specialize h1 k h2
      rw [sortedInsert_cons_gt]
      · simp [ih]
      · assumption

theorem length_sortedInsert_of_not_mem {xs : List α} {k : α} (h1 : Sorted xs) (h2 : k ∉ xs) :
    (sortedInsert xs k).length = xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [Sorted, List.sorted_cons] at h1
    rcases h1 with ⟨h3, h4⟩
    rw [List.mem_cons, not_or] at h2
    rcases h2 with ⟨h5, h6⟩
    specialize ih h4 h6
    rcases lt_trichotomy k x with hlt | heq | hgt
    · rw [sortedInsert_cons_lt]
      · simp
      · assumption
    · contradiction
    · rw [sortedInsert_cons_gt]
      · simp [ih]
      · assumption

namespace Raw

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem inorder_nil : (.nil : Raw α).inorder = [] := by
  rfl

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem inorder_node : (.node l x c r : Raw α).inorder = inorder l ++ [x] ++ inorder r := by
  rfl

namespace Model

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem mem_iff_mem {t : Raw α} (x : α) : x ∈ t ↔ x ∈ t.inorder := by
  induction t generalizing x with
  | nil => simp
  | node left data color right lih rih => simp_all

end Model

end Raw

-- TODO: this is probably useful in Mathlib
omit [Ord α] [LawfulOrd α] in
theorem Sorted_append_cons_iff {left right : List α} {data : α} :
    Sorted (left ++ data :: right)
      ↔
    (∀ x ∈ right, data < x) ∧ (∀ x ∈ left, x < data) ∧ Sorted left ∧ Sorted right := by
  induction left with
  | nil => simp
  | cons l ls ih =>
    simp_all
    constructor
    · aesop
    · intro h
      rcases h with ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩, h6⟩
      constructor
      · intro b hb
        rcases hb with hb | hb | hb
        · apply h4
          assumption
        · rwa [hb]
        · apply lt_trans
          · exact h2
          · exact h1 b hb
      · simp_all

omit [Ord α] [LawfulOrd α] in
theorem bst_iff_sorted_inorder {t : Raw α} : t.BST ↔ Sorted t.inorder := by
  induction t with
  | nil => simp
  | node left data color right lih rih =>
    constructor
    · intro h
      cases h with
      | node hleft1 hleft2 hright1 hright2 =>
        simp only [Raw.inorder_node, List.append_assoc, List.singleton_append,
          Sorted_append_cons_iff]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [Raw.Model.mem_iff_mem] using hright1
        · simpa [Raw.Model.mem_iff_mem] using hleft1
        · rwa [← lih]
        · rwa [← rih]
    · intro h
      simp only [Raw.inorder_node, List.append_assoc, List.singleton_append,
        Sorted_append_cons_iff] at h
      rcases h with ⟨h1, h2, h3, h4⟩
      apply Raw.BST.node
      · simpa [Raw.Model.mem_iff_mem]
      · rwa [lih]
      · simpa [Raw.Model.mem_iff_mem]
      · rwa [rih]

namespace Raw
namespace Model

omit [Preorder α] [Ord α] [LawfulOrd α] in
@[simp]
theorem inorder_paintColor_independent (t : Raw α) :
    (t.paintColor c).inorder = t.inorder := by
  unfold paintColor
  split <;> simp

theorem baliL_inorder_independent {l r : Raw α}
    (hl1 : ∀ y ∈ l, y < x) (hl2 : BST l)
    (hr1 : ∀ y ∈ r, x < y) (hr2 : BST r)
    : (baliL x l r).inorder = l.inorder ++ x :: r.inorder := by
  sorry

theorem baliR_inorder_independent {l r : Raw α}
    (hl1 : ∀ y ∈ l, y < x) (hl2 : BST l)
    (hr1 : ∀ y ∈ r, x < y) (hr2 : BST r)
    : (baliR x l r).inorder = l.inorder ++ x :: r.inorder := by
  sorry

theorem inorder_insert_eq_insert_inorder {t : Raw α} (x : α) (h : Sorted t.inorder) :
    (t.insert x).inorder = sortedInsert t.inorder x := sorry

theorem baldL_inorder_independent {l r : Raw α}
    (hl1 : ∀ y ∈ l, y < x) (hl2 : BST l)
    (hr1 : ∀ y ∈ r, x < y) (hr2 : BST r)
    : (baldL x l r).inorder = l.inorder ++ x :: r.inorder := by
  unfold baldL
  split
  . aesop
  . aesop (add norm baliR_inorder_independent)
  . simp only [inorder_node]
    rw [baliR_inorder_independent] <;> aesop
  . aesop

theorem baldR_inorder_independent {l r : Raw α}
    (hl1 : ∀ y ∈ l, y < x) (hl2 : BST l)
    (hr1 : ∀ y ∈ r, x < y) (hr2 : BST r)
    : (baldR x l r).inorder = l.inorder ++ x :: r.inorder := by
  unfold baldR
  split
  . aesop
  . aesop (add norm baliL_inorder_independent)
  . rw [inorder_node]
    rw [baliL_inorder_independent] <;> aesop
  . aesop

theorem appendTrees_inorder_independent {l r : Raw α}
    (hl : BST l) (hr : BST r) (h : ∀ x ∈ l, ∀ y ∈ r, x < y) :
    (l.appendTrees r).inorder = l.inorder ++ r.inorder := by
  unfold appendTrees
  . split
    . simp
    . simp
    . split
      . next left1  _ right1 left2 _ right2 _ left3 data3 right3 heq =>
        rw [bst_node] at hl hr
        rcases hl with ⟨_,_,_,hlr2⟩
        rcases hr with ⟨_,hrl2,_,_⟩
        simp_all only [mem_node, true_or, or_true, inorder_node, List.append_assoc, true_and,
          List.cons_append, List.nil_append, List.append_cancel_left_eq, List.cons.injEq]
        have : right1.inorder ++ left2.inorder = left3.inorder ++ data3 :: right3.inorder := by
          have := appendTrees_inorder_independent hlr2 hrl2 (by aesop)
          rw [heq] at this
          simp [← this]
        rw [← List.append_assoc]
        simp [this]
      . rw [bst_node] at hl hr
        rcases hl with ⟨_,_,_,hlr2⟩
        rcases hr with ⟨_,hrl2,_,_⟩
        have := appendTrees_inorder_independent hlr2 hrl2 (by aesop)
        aesop
    . split
      . next left1  _ right1 left2 _ right2 _ left3 data3 right3 heq =>
        rw [bst_node] at hl hr
        rcases hl with ⟨_,_,_,hlr2⟩
        rcases hr with ⟨_,hrl2,_,_⟩
        simp_all only [mem_node, true_or, or_true, inorder_node, List.append_assoc, true_and,
          List.cons_append, List.nil_append, List.append_cancel_left_eq, List.cons.injEq]
        have : right1.inorder ++ left2.inorder = left3.inorder ++ data3 :: right3.inorder := by
          have := appendTrees_inorder_independent hlr2 hrl2 (by aesop)
          rw [heq] at this
          simp [← this]
        rw [← List.append_assoc]
        simp [this]
      . next left1 data1 right1 left2 data2 right2 _ _ =>
        rw [bst_node] at hl hr
        rcases hl with ⟨hll1,hll2,_,hlr2⟩
        rcases hr with ⟨_,hrl2,_,_⟩
        have := appendTrees_inorder_independent hlr2 hrl2 (by aesop)
        have : BST (node (right1.appendTrees left2) data2 Color.black right2) := by aesop
        have := baldL_inorder_independent hll1 hll2 (by aesop) this
        aesop
    . rw [bst_node] at hr
      rcases hr with ⟨_,hrl2,_,_⟩
      have := appendTrees_inorder_independent hl hrl2 (by aesop)
      aesop
    . aesop (add norm appendTrees, safe appendTrees_inorder_independent)

theorem erase_lt {l r : Raw α} (h : x < d) (hsort : Sorted (Raw.node l d c r).inorder) :
    (l.inorder ++ d :: r.inorder).erase x = (l.inorder.erase x ++ d :: r.inorder) := by
  rw [List.erase_append]
  split
  . simp
  . have h1 : l.inorder.erase x = l.inorder := by aesop
    simp only [h1, List.append_cancel_left_eq, List.erase_eq_self_iff, List.mem_cons, not_or]
    constructor
    · aesop
    · intro h2
      have : d < x := by aesop (add norm Sorted_append_cons_iff)
      exact lt_asymm h this

theorem erase_eq {l r : Raw α} (hsort : Sorted (Raw.node l d c r).inorder) :
    (l.inorder ++ d :: r.inorder).erase d = l.inorder ++ r.inorder := by
  rw [List.erase_append_right]
  . aesop
  . intro hlin
    apply lt_irrefl d
    simp only [inorder_node, List.append_assoc, List.singleton_append,
      Sorted_append_cons_iff] at hsort
    rcases hsort with ⟨h1, h2, h3, h4⟩
    exact h2 _ hlin

theorem erase_gt {l r : Raw α} (h : d < x) (hsort : Sorted (Raw.node l d c r).inorder) :
    (l.inorder ++ d :: r.inorder).erase x = (l.inorder ++ d :: (r.inorder.erase x)) := by
  rw [List.erase_append_right]
  . rw [List.erase_cons]
    aesop
  . intro hlin
    simp only [inorder_node, List.append_assoc, List.singleton_append,
      Sorted_append_cons_iff] at hsort
    rcases hsort with ⟨h1, h2, h3, h4⟩
    exact lt_asymm h (h2 _ hlin)

theorem inorder_del_eq_erase_inorder {t : Raw α} (x : α) (h : Sorted t.inorder) :
    (t.del x).inorder = List.erase t.inorder x := by
  unfold del
  split
  . simp
  . split
    . split <;>
      . next left data _ right _ heq _ =>
        have := bst_iff_sorted_inorder.mpr h
        rw [bst_node] at this
        rcases this with ⟨_,hl2,hr1,hr2⟩
        have hdel1 : ∀ y ∈ (del x left), y < data := by aesop
        have hdel2 : BST (del x left) := bst_del_of_bst x left hl2
        have := baldL_inorder_independent hdel1 hdel2 hr1 hr2
        simp only [this, inorder_node, List.append_assoc, List.singleton_append]
        rw [LawfulOrd.compare_eq_lt] at heq
        have := erase_lt heq h
        simp only [this, List.append_cancel_right_eq]
        apply inorder_del_eq_erase_inorder
        apply bst_iff_sorted_inorder.mp
        assumption
    . next left data _ right _ heq =>
        have := bst_iff_sorted_inorder.mpr h
        rw [bst_node] at this
        rcases this with ⟨hl1,hl2,hr1,hr2⟩
        have hord : ∀ x ∈ left, ∀ y ∈ right, x < y := by
          intro x xmem y ymem
          apply lt_trans (hl1 x xmem)
          apply hr1
          assumption
        have := appendTrees_inorder_independent hl2 hr2 hord
        rw [this]
        rw [LawfulOrd.compare_eq_eq] at heq
        subst heq
        have := erase_eq h
        simp [this]
    . split <;>
      . next data _ right _ heq _ =>
        have := bst_iff_sorted_inorder.mpr h
        rw [bst_node] at this
        rcases this with ⟨hl1,hl2,_,hr2⟩
        have hdel1 : ∀ y ∈ (del x right), data < y := by aesop
        have hdel2 : BST (del x right) := bst_del_of_bst x right hr2
        have := baldR_inorder_independent hl1 hl2 hdel1 hdel2
        simp only [this, inorder_node, List.append_assoc, List.singleton_append]
        rw [LawfulOrd.compare_eq_gt] at heq
        have := erase_gt heq h
        simp only [this, List.append_cancel_left_eq, List.cons.injEq, true_and]
        apply inorder_del_eq_erase_inorder
        apply bst_iff_sorted_inorder.mp
        assumption

theorem inorder_erase_eq_erase_inorder {t : Raw α} (x : α) (h : Sorted t.inorder) :
    (t.erase x).inorder = sortedErase t.inorder x := by
  unfold erase
  rw [inorder_paintColor_independent]
  rw [sortedErase]
  apply inorder_del_eq_erase_inorder
  assumption

theorem contains_iff_contains {t : Raw α} (x : α) (h : Sorted t.inorder) :
    t.contains x = (t.inorder).contains x := by
  rw [Bool.eq_iff_iff]
  rw [List.contains_iff_mem]
  rw [contains_eq_true_iff_mem_of_bst]
  · apply mem_iff_mem
  · rw [bst_iff_sorted_inorder]
    assumption

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem isEmpty_eq_isEmpty {t : Raw α} : t.isEmpty = t.inorder.isEmpty := by
  cases t <;> simp [Raw.isEmpty]

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem size_eq_length {t : Raw α} : t.size = t.inorder.length := by
  induction t with
  | nil => simp
  | node l d c r lih rih => simp_arith [lih, rih]

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem eq_nil_iff_nil {t : Raw α} : (t = .nil) ↔ t.inorder = [] := by
  cases t <;> simp

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem nil_eq_iff_nil {t : Raw α} : (.nil = t) ↔ t.inorder = [] := by
  cases t <;> simp

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem isEmpty_iff_eq_nil {xs : List α} : xs.isEmpty ↔ xs = [] := by
  simp

omit [LawfulOrd α] in
theorem isEmpty_sortedInsert {xs : List α} {k : α} (h : Sorted xs) :
    (sortedInsert xs k).isEmpty = false := by
  cases xs
  · simp
  · rw [sortedInsert]
    split <;> simp

theorem mem_sortedInsert {xs : List α} (k a : α) (h : Sorted xs) :
    a ∈ sortedInsert xs k ↔ a = k ∨ a ∈ xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [Sorted, List.sorted_cons] at h
    specialize ih h.right
    rcases lt_trichotomy k x with hlt | heq | hgt
    · rw [sortedInsert_cons_lt]
      · simp
      · assumption
    · simp [heq]
    · rw [sortedInsert_cons_gt]
      · aesop
      · assumption

theorem mem_sortedErase {xs : List α} (k a : α) (h : Sorted xs) :
    a ∈ sortedErase xs k ↔ a ≠ k ∧ a ∈ xs :=
  List.Nodup.mem_erase_iff (List.Sorted.nodup h)

theorem length_sortedInsert {xs : List α} (k : α) (h : Sorted xs) :
    (sortedInsert xs k).length = if k ∈ xs then xs.length else xs.length + 1 := by
  split
  · apply length_sortedInsert_of_mem <;> assumption
  · apply length_sortedInsert_of_not_mem <;> assumption

theorem length_sortedErase {xs : List α} (k : α) :
    (sortedErase xs k).length = if k ∈ xs then xs.length - 1 else xs.length :=
  List.length_erase ..

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem isEmpty_eq_length_eq_zero {xs : List α} : xs.isEmpty = (xs.length == 0) := by
  cases xs <;> simp

theorem sortedErase_nil {a : α} : sortedErase [] a = [] :=
  List.erase_nil ..

theorem isEmpty_sortedErase {xs : List α} {k : α} (h : Sorted xs) :
    (sortedErase xs k).isEmpty = (xs.isEmpty || xs.length == 1 && xs.contains k) := by
  rw [sortedErase, Bool.eq_iff_iff]
  simp
  constructor
  · intro h
    rcases h with h | h <;> simp [h]
  · intro h
    rcases h with h | h
    · simp [h]
    · cases xs
      · simp
      · aesop


end Model
end Raw

namespace Model

@[inline]
def inorder (set : Set α) : List α := set.raw.inorder

theorem inorder_sorted {t : Set α} : Sorted (inorder t) :=
  bst_iff_sorted_inorder.mp t.hbst

@[simp]
theorem inorder_empty : inorder (.empty : Set α) = [] :=
  Raw.inorder_nil

theorem inorder_insert_eq_insert_inorder {t : Set α} (x : α) :
    inorder (t.insert x) = sortedInsert (inorder t) x :=
  Raw.Model.inorder_insert_eq_insert_inorder x inorder_sorted

theorem inorder_erase_eq_erase_inorder {t : Set α} (x : α) :
    inorder (t.erase x) = sortedErase (inorder t) x :=
  Raw.Model.inorder_erase_eq_erase_inorder x inorder_sorted

theorem mem_iff_mem {t : Set α} (x : α) : x ∈ t ↔ x ∈ (inorder t) :=
  Raw.Model.mem_iff_mem x

theorem contains_iff_contains {t : Set α} (x : α) : t.contains x = (inorder t).contains x :=
  Raw.Model.contains_iff_contains x inorder_sorted

theorem isEmpty_eq_isEmpty {t : Set α} : t.isEmpty = (inorder t).isEmpty :=
  Raw.Model.isEmpty_eq_isEmpty

theorem size_eq_length {t : Set α} : t.size = (inorder t).length :=
  Raw.Model.size_eq_length

theorem eq_empty_iff_empty {t : Set α} : (t = .empty) ↔ (inorder t) = [] := by
  cases t
  simp [Set.empty, inorder, Raw.Model.eq_nil_iff_nil]

theorem empty_eq_iff_empty {t : Set α} : (.empty = t) ↔ (inorder t) = [] := by
  cases t
  simp [Set.empty, inorder, Raw.Model.nil_eq_iff_nil]

private def modelTheorems : Array Lean.Name :=
  #[``inorder_empty, ``inorder_insert_eq_insert_inorder, ``inorder_erase_eq_erase_inorder,
    ``mem_iff_mem, ``contains_iff_contains, ``isEmpty_eq_isEmpty, ``size_eq_length,
    ``eq_empty_iff_empty, ``empty_eq_iff_empty
  ]

scoped syntax "simp_to_model" ("using" term)? : tactic

scoped macro_rules
| `(tactic| simp_to_model $[using $using?]?) => do
  `(tactic|
    simp only [$[$(modelTheorems.map Lean.mkIdent):term],*];
    $[apply $(using?.toArray):term];*
  )

theorem isEmpty_iff_eq_nil {t : Set α} : (inorder t).isEmpty ↔ (inorder t) = [] :=
  Raw.Model.isEmpty_iff_eq_nil

theorem isEmpty_sortedInsert {t : Set α} {k : α} : (sortedInsert (inorder t) k).isEmpty = false :=
  Raw.Model.isEmpty_sortedInsert inorder_sorted

theorem mem_sortedInsert {t : Set α} (k a : α) :
    a ∈ sortedInsert (inorder t) k ↔ a = k ∨ a ∈ (inorder t) :=
  Raw.Model.mem_sortedInsert k a inorder_sorted

theorem mem_sortedErase {t : Set α} (k a : α) :
    a ∈ sortedErase (inorder t) k ↔ a ≠ k ∧ a ∈ (inorder t) :=
  Raw.Model.mem_sortedErase k a inorder_sorted

theorem length_sortedInsert {t : Set α} (k : α) :
    (sortedInsert (inorder t) k).length = if k ∈ (inorder t) then (inorder t).length else (inorder t).length + 1 :=
  Raw.Model.length_sortedInsert k inorder_sorted

theorem length_sortedErase {t : Set α} (k : α) :
    (sortedErase (inorder t) k).length = if k ∈ (inorder t) then (inorder t).length - 1 else (inorder t).length :=
  Raw.Model.length_sortedErase k

theorem isEmpty_eq_length_eq_zero {t : Set α} : (inorder t).isEmpty = ((inorder t).length == 0) :=
  Raw.Model.isEmpty_eq_length_eq_zero

theorem sortedErase_nil {a : α} : sortedErase [] a = [] :=
  Raw.Model.sortedErase_nil

theorem isEmpty_sortedErase {t : Set α} {k : α} :
    (sortedErase (inorder t) k).isEmpty = ((inorder t).isEmpty || (inorder t).length == 1 && (inorder t).contains k) :=
  Raw.Model.isEmpty_sortedErase inorder_sorted

end Model

end Internal

end Filrb
