import Filrb.Basic

namespace Filrb

namespace Set

variable [Preorder α] [Ord α] [LawfulOrd α]
variable  {set : Set α}

theorem emptyc_eq_empty : (∅ : Set α) = (empty : Set α) := by
  rfl

theorem contains_eq_decide_mem {x : α} : set.contains x = decide (x ∈ set) := by
  simp [← contains_eq_true_iff_mem]

theorem contains_eq_false_iff_not_mem {x : α} : set.contains x = false ↔ ¬(x ∈ set) := by
  simp [← contains_eq_true_iff_mem]

theorem isEmpty_iff_eq_empty : isEmpty set ↔ set = empty := sorry

@[simp]
theorem isEmpty_empty : isEmpty (empty : Set α) = true := by
  simp [isEmpty_iff_eq_empty]

@[simp]
theorem isEmpty_emptyc : isEmpty (∅ : Set α) = true := by
  simp [emptyc_eq_empty]

@[simp]
theorem isEmpty_insert {x : α} : isEmpty (set.insert x) = false := sorry

@[simp]
theorem not_mem_empty {x : α} : ¬(x ∈ (empty : Set α)) := sorry

@[simp]
theorem contains_empty {x : α} : contains (empty : Set α) x = false := by
  simp [contains_eq_false_iff_not_mem]

@[simp]
theorem not_mem_emptyc {x : α} : ¬(x ∈ (∅ : Set α)) := by
  simp [emptyc_eq_empty]

@[simp]
theorem contains_emptyc {x : α} : contains (∅ : Set α) x = false := by
  simp [emptyc_eq_empty]

theorem not_mem_of_isEmpty {a : α} : set.isEmpty → ¬a ∈ set := by
  intro h
  simp_all [isEmpty_iff_eq_empty]

theorem contains_of_isEmpty {a : α} : set.isEmpty → set.contains a = false := by
  rw [contains_eq_false_iff_not_mem]
  apply not_mem_of_isEmpty

theorem isEmpty_eq_false_iff_exists_mem : set.isEmpty = false ↔ ∃ a, a ∈ set := sorry

theorem isEmpty_eq_false_iff_exists_contains_eq_true :
    set.isEmpty = false ↔ ∃ a, set.contains a = true := by
  simp [contains_eq_true_iff_mem, isEmpty_eq_false_iff_exists_mem]

theorem isEmpty_iff_forall_not_mem : set.isEmpty = true ↔ ∀ a, ¬a ∈ set := by
  constructor
  · intro h1 x
    apply not_mem_of_isEmpty
    assumption
  · intro h
    have := not_exists_of_forall_not h
    rw [← isEmpty_eq_false_iff_exists_mem] at this
    simpa using this

theorem isEmpty_iff_forall_contains : set.isEmpty = true ↔ ∀ a, set.contains a = false := by
  simp [contains_eq_false_iff_not_mem, isEmpty_iff_forall_not_mem]

@[simp]
theorem mem_insert {k a : α} : a ∈ set.insert k ↔ k = a ∨ a ∈ set := sorry

@[simp]
theorem contains_insert {k a : α} : (set.insert k).contains a = (k = a ∨ set.contains a) := by
  simp [contains_eq_true_iff_mem]

theorem mem_of_mem_insert {k a : α} : a ∈ set.insert k → k ≠ a → a ∈ set := by
  intro h1 h2
  simpa [h2] using h1

theorem contains_of_contains_insert {k a : α} :
    (set.insert k).contains a → k ≠ a → set.contains a := by
  rw [contains_eq_true_iff_mem, contains_eq_true_iff_mem]
  apply mem_of_mem_insert

theorem contains_insert_self {k : α} : (set.insert k).contains k := by
  simp

theorem mem_insert_self {k : α} : k ∈ set.insert k := by
  simp

@[simp]
theorem size_empty : (empty : Set α).size = 0 := sorry

@[simp]
theorem size_emptyc : (∅ : Set α).size = 0 := by
  simp [emptyc_eq_empty]

theorem isEmpty_eq_size_eq_zero : set.isEmpty = (set.size == 0) := sorry

theorem size_insert {k : α} :
    (set.insert k).size = if k ∈ set then set.size else set.size + 1 :=
  sorry

theorem size_le_size_insert {k : α} : set.size ≤ (set.insert k).size := by
  rw [size_insert]
  split <;> omega

theorem size_insert_le {k : α} : (set.insert k).size ≤ set.size + 1 := by
  rw [size_insert]
  split <;> omega

@[simp]
theorem erase_empty {a : α} : (empty : Set α).erase a = empty := sorry

@[simp]
theorem erase_emptyc {a : α} : (∅ : Set α).erase a = ∅ := by
  simp [emptyc_eq_empty]

@[simp]
theorem isEmpty_erase {k : α} :
    (set.erase k).isEmpty = (set.isEmpty || (set.size == 1 && set.contains k)) := sorry

@[simp]
theorem mem_erase {k a : α} : a ∈ set.erase k ↔ k ≠ a ∧ a ∈ set := sorry

@[simp]
theorem contains_erase {k a : α} : (set.erase k).contains a = (k ≠ a && set.contains a) := by
  simp [contains_eq_decide_mem]

theorem mem_of_mem_erase {k a : α} : a ∈ set.erase k → a ∈ set := by
  simp

theorem contains_of_contains_erase {k a : α} : (set.erase k).contains a → set.contains a := by
  rw [contains_eq_true_iff_mem, contains_eq_true_iff_mem]
  apply mem_of_mem_erase

theorem size_erase {k : α} : (set.erase k).size = if k ∈ set then set.size - 1 else set.size :=
  sorry

theorem size_erase_le {k : α} : (set.erase k).size ≤ set.size := by
  rw [size_erase]
  split <;> omega

theorem size_le_size_erase {k : α} : set.size ≤ (set.erase k).size + 1 := by
  rw [size_erase]
  split <;> omega

end Set

end Filrb
