import Filrb.Basic

namespace Filrb

namespace Set

variable [Preorder α] [Ord α] [LawfulOrd α]
variable  {set : Set α}

@[simp]
theorem isEmpty_empty : isEmpty (empty : Set α) = true := sorry

@[simp]
theorem isEmpty_emptyc : isEmpty (∅ : Set α) = true := sorry

@[simp]
theorem isEmpty_insert {x : α} : isEmpty (set.insert x) = false := sorry

@[simp]
theorem contains_empty {x : α} : contains (empty : Set α) x = false := sorry

@[simp]
theorem not_mem_empty {x : α} : ¬(x ∈ (empty : Set α)) := sorry

@[simp]
theorem contains_emptyc {x : α} : contains (∅ : Set α) x = false := sorry

@[simp]
theorem not_mem_emptyc {x : α} : ¬(x ∈ (∅ : Set α)) := sorry

theorem contains_of_isEmpty {a : α} : set.isEmpty → set.contains a = false := sorry

theorem not_mem_of_isEmpty {a : α} : set.isEmpty → ¬a ∈ set := sorry

theorem isEmpty_eq_false_iff_exists_contains_eq_true :
    set.isEmpty = false ↔ ∃ a, set.contains a = true := sorry

theorem isEmpty_eq_false_iff_exists_mem :
    set.isEmpty = false ↔ ∃ a, a ∈ set := sorry

theorem isEmpty_iff_forall_contains :
    set.isEmpty = true ↔ ∀ a, set.contains a = false := sorry

theorem isEmpty_iff_forall_not_mem :
    set.isEmpty = true ↔ ∀ a, ¬a ∈ set := sorry

@[simp]
theorem contains_insert {k a : α} : (set.insert k).contains a = (k = a ∨ set.contains a) := sorry

@[simp]
theorem mem_insert {k a : α} : a ∈ set.insert k ↔ k = a ∨ a ∈ set := sorry

theorem contains_of_contains_insert {k a : α} :
    (set.insert k).contains a → k ≠ a → set.contains a := sorry

theorem mem_of_mem_insert {k a : α} : a ∈ set.insert k → k ≠ a → a ∈ set := sorry

theorem contains_insert_self {k : α} : (set.insert k).contains k := by
  simp

theorem mem_insert_self {k : α} : k ∈ set.insert k := by
  simp

@[simp]
theorem size_empty : (empty : Set α).size = 0 := sorry

@[simp]
theorem size_emptyc : (∅ : Set α).size = 0 := sorry

theorem isEmpty_eq_size_eq_zero : set.isEmpty = (set.size == 0) := sorry

theorem size_insert {k : α} :
    (set.insert k).size = if k ∈ set then set.size else set.size + 1 :=
  sorry

theorem size_le_size_insert {k : α} : set.size ≤ (set.insert k).size := sorry

theorem size_insert_le {k : α} : (set.insert k).size ≤ set.size + 1 := sorry

@[simp]
theorem erase_empty {a : α} : (empty : Set α).erase a = empty := sorry

@[simp]
theorem erase_emptyc {a : α} : (∅ : Set α).erase a = ∅ := sorry

@[simp]
theorem isEmpty_erase {k : α} :
    (set.erase k).isEmpty = (set.isEmpty || (set.size == 1 && set.contains k)) := sorry

@[simp]
theorem contains_erase {k a : α} : (set.erase k).contains a = (k ≠ a && set.contains a) := sorry

@[simp]
theorem mem_erase {k a : α} : a ∈ set.erase k ↔ (k ≠ a) ∧ a ∈ set := sorry

theorem contains_of_contains_erase {k a : α} : (set.erase k).contains a → set.contains a := sorry

theorem mem_of_mem_erase {k a : α} : a ∈ set.erase k → a ∈ set := sorry

theorem size_erase {k : α} : (set.erase k).size = if k ∈ set then set.size - 1 else set.size :=
  sorry

theorem size_erase_le {k : α} : (set.erase k).size ≤ set.size := sorry

theorem size_le_size_erase {k : α} : set.size ≤ (set.erase k).size + 1 := sorry

end Set

end Filrb
