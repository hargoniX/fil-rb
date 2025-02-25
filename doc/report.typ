#import "@preview/fletcher:0.5.0" as fletcher: diagram, node, edge
#import "@preview/codelst:2.0.0": sourcecode
#import "@preview/curryst:0.1.1"
#import "template.typ": *

#let target_date = datetime(year: 2025, month: 3, day: 3)
#show : official.with(
  title: [
    Design Report:#linebreak()
    Formalization of Red-Black Trees in Lean4 #linebreak()
  ],
  author: [Daniel Soukup, Henrik Böving, Linyin Luo],
  thesis-type: "Master Praktikum: Formalization in Lean",
  supervisor: [Xavier Généreux],
  submission_date: target_date.display("[month repr:long] [day], [year]"),
)

#show figure.caption : set text(10pt)

= Introduction <introduction>
Briefly talk about rbtrees and that/how they are useful for functional programming, cite:
- the original rbtree paper
- some publication by okasaki where he points this out

= RbTree Framework <framework>
The goal of our formalization is to provide an implementation of sets as red black trees with a complete
surface level API such that users of the data structure likely never have to peek into the internals
to do a proof. For this approach we combine the general approach taken by the Lean standard library
team for data structure verification with ideas for a similar approach, specifically geared to
red black trees from @nipkowtrees. Our design takes the following steps:
1. Define an efficient representation of red black trees and the well known functional approaches to
   implementing algorithms on them efficiently in @raw.
2. Verify the key invariants from the literature for our implementation in @invariants.
3. Connect red black trees to a model of sorted lists and use this model to verify the surface level
   API of the tree in @surface.

== Raw RbTree Defintion <raw>
We have a raw rbtree definition with the following operations onto it:
- `erase`
- `insert`
- explain `baliL/R`, `baldL/R` and `appendTrees` and what they fix on traversal?
- most importantly `toGraphviz`!

Explain, why we chose that definition for rbtree.
The explanation is mostly in the doc string of Raw.lean, cite FBIP here.

=== Invariants <invariants>
Explain that these operations fulfill:
- Red-Black Invariant: used to prove a height upper bound which implies $O(log(n))$ performance characteristica
- BST invariant: used for further verification (especially for the model)

Explain the general approach to proofs by decomposition mixed with simp and aesop.
We should cite aesop here.

Explain some considerations we had in mind for our simp set.

== Surface Level API <surface>
After providing the basic operations and verifying that they preserve the invariants we can pack
them up into a subtype of red black trees that always have their invariants attached and re-expose
all invariant preserving operations as functions on these red black trees. Note that this additional
level of abstraction is zero-cost performance wise as Lean represents subtypes in the same way
as the original type #footnote[https://lean-lang.org/lean4/doc/dev/ffi.html#translating-types-from-lean-to-c].

Because this subtype is always known to be a valid binary search tree we can relate operations on
it to operations on its inorder representation as a list as seen in @nipkowtrees. To do this we must
provide:
1. For each proposition on the tree a lemma that translates the proposition to a proposition about
   sorted lists, for example for membership: `x ∈ t ↔ x ∈ t.inorder`
2. For every operation on the tree a lemma that explains what happens when `inorder` is applied
   to the result of the operation, for example for inserting an element: `inorder (t.insert x) = sortedInsert (inorder t) x`

By combining all of these lemmas into a custom simp set we can build a tactic `simp_to_model` that
translates arbitrary propositions about the surface level API into propositions about sorted lists.
As these propositions are usually provable much easier than ones about red black trees directly
it becomes much easier to both build the initial surface level API but also extend on it later on
if necessary.

Now that we have all tools to make proofs about the behavior of red black tree operations easy, the
key question is what lemmas we need to prove in order to provide a complete API for users of our
library. To determine this we use the API design approach by the Lean standard library
team which considers how any operation that produces a new tree (`insert`, `erase` etc.) interacts
with any operation that produces an output based on a tree (`size`, `contains` etc.). This leaves us
with a lemma coverage as seen in TODO table, all of which are proven either from each other or by
`simp_to_model` and induction over sorted lists.

= Performance <performance>
TODO:
- mention that we proved the lemma about height boundedness
- Some performance measurements against C++ `std::map`.


= Conclusion <conclusion>
In summary we provide a reasonably efficient red black tree implementation that very likely has
enough proof API such that no user should ever need to peek below it. Beyond usability this has the added
benefit that we can almost arbitrarily refactor the internals without breaking user code as long as
the lemmas we provide keep holding.

While we limited ourselves to just sets as red black trees, the above approach can be extended to
maps or dependent maps as has been shown in the Lean standard library for both hash and tree based
containers. Beyond this we can add more operations such as `min?`, `max?`, `ForIn` etc. very easily
by repeating the design process for that single operation.


#bibliography("references.bib", title: [References])
