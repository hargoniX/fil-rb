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
    match cmp a x with
    | .lt => a :: x :: xs
    | .eq => a :: xs
    | .gt => x :: sortedInsert xs a

def sortedErase (xs : List α) (a : α) : List α :=
  match xs with
  | [] => []
  | x :: xs =>
    if x = a then
      xs
    else
      x :: sortedErase xs a

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

theorem inorder_insert_eq_insert_inorder {t : Raw α} (x : α) (h : Sorted t.inorder) :
    (t.insert x).inorder = sortedInsert t.inorder x := by
  induction t with
  | nil => sorry
  | node => sorry

theorem inorder_erase_eq_erase_inorder {t : Raw α} (x : α) (h : Sorted t.inorder) :
    (t.erase x).inorder = sortedErase t.inorder x := sorry

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

theorem size_eq_length {t : Raw α} : t.size = t.inorder.length := sorry

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem eq_nil_iff_nil {t : Raw α} : (t = .nil) ↔ t.inorder = [] := by
  cases t <;> simp

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem nil_eq_iff_nil {t : Raw α} : (.nil = t) ↔ t.inorder = [] := by
  cases t <;> simp

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem isEmpty_iff_eq_nil {xs : List α} : xs.isEmpty ↔ xs = [] := by
  simp

theorem isEmpty_sortedInsert {xs : List α} {k : α} (h : Sorted xs) :
    (sortedInsert xs k).isEmpty = false := by
  cases xs
  · simp [sortedInsert]
  · rw [sortedInsert]
    split <;> simp

theorem mem_sortedInsert {xs : List α} (k a : α) (h : Sorted xs) :
    a ∈ sortedInsert xs k ↔ k = a ∨ a ∈ xs := sorry

theorem mem_sortedErase {xs : List α} (k a : α) (h : Sorted xs) :
    a ∈ sortedErase xs k ↔ k ≠ a ∧ a ∈ xs := sorry

theorem length_sortedInsert {xs : List α} (k : α) (h : Sorted xs) :
    (sortedInsert xs k).length = if k ∈ xs then xs.length else xs.length + 1 := sorry

theorem length_sortedErase {xs : List α} (k : α) (h : Sorted xs) :
    (sortedErase xs k).length = if k ∈ xs then xs.length - 1 else xs.length := sorry

omit [Preorder α] [Ord α] [LawfulOrd α] in
theorem isEmpty_eq_length_eq_zero {xs : List α} : xs.isEmpty = (xs.length == 0) := by
  cases xs <;> simp

theorem sortedErase_nil {a : α} : sortedErase [] a = [] := by
  simp [sortedErase]

theorem isEmpty_sortedErase {xs : List α} {k : α} (h : Sorted xs) :
    (sortedErase xs k).isEmpty = (xs.isEmpty || xs.length == 1 && xs.contains k) :=
  sorry


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
    a ∈ sortedInsert (inorder t) k ↔ k = a ∨ a ∈ (inorder t) :=
  Raw.Model.mem_sortedInsert k a inorder_sorted

theorem mem_sortedErase {t : Set α} (k a : α) :
    a ∈ sortedErase (inorder t) k ↔ k ≠ a ∧ a ∈ (inorder t) :=
  Raw.Model.mem_sortedErase k a inorder_sorted

theorem length_sortedInsert {t : Set α} (k : α) :
    (sortedInsert (inorder t) k).length = if k ∈ (inorder t) then (inorder t).length else (inorder t).length + 1 :=
  Raw.Model.length_sortedInsert k inorder_sorted

theorem length_sortedErase {t : Set α} (k : α) :
    (sortedErase (inorder t) k).length = if k ∈ (inorder t) then (inorder t).length - 1 else (inorder t).length :=
  Raw.Model.length_sortedErase k inorder_sorted

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
