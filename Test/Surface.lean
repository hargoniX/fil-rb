import Filrb.Plausible

/-!
This module checks the validity of the set properties for the `Raw` tree implementation, as well
as the height property.
-/

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ∀ (x : Nat), ¬x ∈ Filrb.Set.empty := by
  plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ∀ (x y : Nat) (t : Filrb.Set Nat), (y ∈ (t.insert x)) ↔ ((y ∈ t) ∨ x = y) := by
  plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ∀ (x y : Nat) (t : Filrb.Set Nat), (y ∈ (t.erase x)) ↔ ((y ∈ t) ∧ x ≠ y) := by
  plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ∀ (x : Nat) (t : Filrb.Set Nat), x ∈ t ↔ t.contains x := by
  plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ∀ (x : Nat) (t : Filrb.Set Nat), x ∉ t ↔ !t.contains x := by
  plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ∀ (t : Filrb.Set Nat), t.height ≤ 2 * Nat.log 2 t.size + 2 := by
  plausible
