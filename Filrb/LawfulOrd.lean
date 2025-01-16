import Mathlib.Order.Compare

/-!
This module builds the basic theory around a lawful version of the `Ord` typeclass. We are
interested in the `Ord` typeclass as it allows us to check for the `<`, `=`, `>` trichotomy in
one match.
-/

namespace Filrb

/--
A lawful version of the `Ord` typeclass.
-/
class LawfulOrd (α : Type u) [LT α] [Ord α] where
  /--
  An `Ord` instance is lawful if it corresponds precisely to `<`, `=` and `>` on its type.
  -/
  compares : ∀ (a b : α), (compare a b).Compares a b

instance [Preorder α] [Ord α] [LawfulOrd α] : LinearOrder α :=
  linearOrderOfCompares compare LawfulOrd.compares

instance : LawfulOrd Nat := sorry
instance : LawfulOrd Int := sorry
instance : LawfulOrd (Fin n) := sorry
instance : LawfulOrd String := sorry

namespace LawfulOrd

variable [Preorder α] [Ord α] [LawfulOrd α]

@[simp]
theorem compare_eq_lt {x y : α} : compare x y = .lt ↔ x < y := by
  have := LawfulOrd.compares x y
  match h : compare x y with
  | .lt => simp_all
  | .eq => simp_all
  | .gt =>
    simp only [h, Ordering.compares_gt, gt_iff_lt, reduceCtorEq, false_iff, not_lt, ge_iff_le] at *
    apply le_of_lt
    assumption

@[simp]
theorem compare_eq_eq {x y : α} : compare x y = .eq ↔ x = y := by
  have := LawfulOrd.compares x y
  match h : compare x y with
  | .lt =>
    simp only [h, Ordering.compares_lt, reduceCtorEq, false_iff, ne_eq] at *
    exact ne_of_lt this
  | .eq => simp_all
  | .gt =>
    simp only [h, Ordering.compares_gt, gt_iff_lt, reduceCtorEq, false_iff, ne_eq] at *
    exact ne_of_gt this

@[simp]
theorem compare_self {x : α} : compare x x = .eq := by
  simp

@[simp]
theorem compare_eq_gt {x y : α} : compare x y = .gt ↔ y < x := by
  have := LawfulOrd.compares x y
  match h : compare x y with
  | .lt =>
    simp only [h, Ordering.compares_lt, reduceCtorEq, false_iff, not_lt, ge_iff_le] at *
    apply le_of_lt
    assumption
  | .eq => simp_all
  | .gt => simp_all

end LawfulOrd

end Filrb
