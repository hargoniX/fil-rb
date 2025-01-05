1. Define the basic raw RBSet and functions on it, refer to:
  - https://arxiv.org/pdf/1908.05647
  - https://github.com/leanprover/lean4/blob/master/src/Lean/Data/RBMap.lean
  - https://www.cs.tufts.edu/comp/150FP/archive/chris-okasaki/redblack99.pdf
  - https://www.cs.cmu.edu/~rwh/students/okasaki.pdf
  Functions:
  - `RBSet.Raw`
  - `Membership`
  - `empty`
  - `insert`
  - `delete`
  - `get?`
2. Define the invariants on it
  - `BST`
  - `RBInv`
3. Prove that functions preserve the invariant
  - `empty` `BST`
  - `empty` `RBInv`
  - `insert` `BST`
  - `insert` `RBInv`
  - `delete` `BST`
  - `delete` `RBInv`
4. Pack up into a surface level `RBSet`
5. Build set theory for `RBSet.Raw`, lift to surface level `RBSet`, refer to https://functional-algorithms-verified.org/functional_data_structures_algorithms.pdf
6. Build `simp` theory based on set theory, refer to https://github.com/leanprover/lean4/blob/master/src/Std/Data/HashSet/Lemmas.lean

For fun stuff:
- Additional helper functions:
  - `isEmpty`
  - `get!`
  - `get`
  - `GetElem`
  - `min`
  - `max`
- use Ordering.cmp instead of LinearOrder
- Functional Algorithms (https://functional-algorithms-verified.org/functional_data_structures_algorithms.pdf):
  - Exercise 8.3: define and verify ofList function
- Software Foundations (https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
  - Exercise: 1 star, standard (RB_blacken_parent)
  - If feeling fancy Exercise: 4 stars, advanced (redblack_bound)
- extend to RBMap
- extend to dependent RBMap
- Widget to display the (operation on the) tree within the infoview?
