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
The general framework that we use for our rbtree.
We should probably cite nipkow's paper on tree verification here.
Briefly explain how our own spin differs, then go into the details in the subsections.

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

== Model <model>
We then bundle the rbtree with its invariants for the surface level API.
The framework that connects rbtrees to operations on sorted lists using BST and thus allows us to reason about a simpler structure for high level lemmas.

Explain how we came up with the high level lemmas that are proved
(by looking at all combinations of every pair of operations and determining whether there should be a lemma for it or not).

Membership, Inorder

= Evaluation <evaluation>
Some performance measurements against C++ `std::map`.
Unclear if we want to compare with the sad coq benchmark script.

= Conclusion <conclusion>
Optional

= Future Work <futurework>
- Integration of further operations
- extending to rbmap and dependent rbmaps

#bibliography("references.bib", title: [References])
