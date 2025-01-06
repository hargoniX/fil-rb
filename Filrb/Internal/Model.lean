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

def sortedInsert (xs : List α) (x : α) : List α := sorry
def sortedErase (xs : List α) (x : α) : List α := sorry

theorem bst_iff_sorted_inorder {t : Raw α} : t.BST ↔ Sorted t.inorder := sorry

namespace Raw
namespace Model

@[simp]
theorem inorder_nil : (.nil : Raw α).inorder = [] := sorry

theorem inorder_insert_eq_insert_inorder {t : Raw α} (x : α) (h : Sorted t.inorder) :
    (t.insert x).inorder = sortedInsert t.inorder x := sorry

theorem inorder_erase_eq_erase_inorder {t : Raw α} (x : α) (h : Sorted t.inorder) :
    (t.erase x).inorder = sortedErase t.inorder x := sorry

theorem mem_iff_mem {t : Raw α} (x : α) (h : Sorted t.inorder) : x ∈ t ↔ x ∈ t.inorder := sorry

theorem contains_iff_contains {t : Raw α} (x : α) (h : Sorted t.inorder) : t.contains x = (t.inorder).contains x :=
  sorry

theorem isEmpty_eq_isEmpty {t : Raw α} : t.isEmpty = t.inorder.isEmpty := sorry

theorem size_eq_length {t : Raw α} : t.size = t.inorder.length := sorry

theorem eq_nil_iff_nil {t : Raw α} : (t = .nil) ↔ t.inorder = [] := sorry

theorem nil_eq_iff_nil {t : Raw α} : (.nil = t) ↔ t.inorder = [] := sorry

theorem isEmpty_iff_eq_nil {xs : List α} : xs.isEmpty ↔ xs = [] := sorry

theorem isEmpty_sortedInsert {xs : List α} {k : α} (h : Sorted xs) :
    (sortedInsert xs k).isEmpty = false :=
  sorry

theorem mem_sortedInsert {xs : List α} (k a : α) (h : Sorted xs) :
    a ∈ sortedInsert xs k ↔ k = a ∨ a ∈ xs := sorry

theorem mem_sortedErase {xs : List α} (k a : α) (h : Sorted xs) :
    a ∈ sortedErase xs k ↔ k ≠ a ∧ a ∈ xs := sorry

theorem length_sortedInsert {xs : List α} (k : α) (h : Sorted xs) :
    (sortedInsert xs k).length = if k ∈ xs then xs.length else xs.length + 1 := sorry

theorem length_sortedErase {xs : List α} (k : α) (h : Sorted xs) :
    (sortedErase xs k).length = if k ∈ xs then xs.length - 1 else xs.length := sorry

theorem isEmpty_eq_length_eq_zero {xs : List α} : xs.isEmpty = (xs.length == 0) :=
  sorry

theorem sortedErase_nil {a : α} : sortedErase [] a = [] := sorry

theorem isEmpty_sortedErase {xs : List α} {k : α} (h : Sorted xs) :
    (sortedErase xs k).isEmpty = (xs.isEmpty || xs.length == 1 && xs.contains k) :=
  sorry


end Model
end Raw

namespace Model

@[inline]
def inorder (set : Set α) : List α := set.raw.inorder

theorem inorder_sorted {t : Set α} : Sorted (inorder t) :=
  bst_iff_sorted_inorder.mp t.bst

@[simp]
theorem inorder_empty : inorder (.empty : Set α) = [] :=
  Raw.Model.inorder_nil

theorem inorder_insert_eq_insert_inorder {t : Set α} (x : α) :
    inorder (t.insert x) = sortedInsert (inorder t) x :=
  Raw.Model.inorder_insert_eq_insert_inorder x inorder_sorted

theorem inorder_erase_eq_erase_inorder {t : Set α} (x : α) :
    inorder (t.erase x) = sortedErase (inorder t) x :=
  Raw.Model.inorder_erase_eq_erase_inorder x inorder_sorted

theorem mem_iff_mem {t : Set α} (x : α) : x ∈ t ↔ x ∈ (inorder t) :=
  Raw.Model.mem_iff_mem x inorder_sorted

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
