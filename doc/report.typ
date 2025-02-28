#import "@preview/wordometer:0.1.4": word-count, total-characters
#import "@preview/drafting:0.2.1": margin-note
#import "template.typ": *

#let note = margin-note

#let target_date = datetime(year: 2025, month: 3, day: 2)
#show : official.with(
  title: [
    Design Report:#linebreak()
    Formalization of Red-Black Trees in Lean 4 #linebreak()
  ],
  author: [Daniel Soukup, Henrik Böving, Lingyin Luo],
  thesis-type: "Master Praktikum: Formalization in Lean",
  supervisor: [Xavier Généreux],
  submission_date: target_date.display("[month repr:long] [day], [year]"),
)

#show: word-count.with(exclude: (raw.where(block: true), <no-wc>))
#show figure.caption : set text(10pt)

#show raw.where(lang: "lean"): r => {
  show "inductive": set text(lmu_red)
  show "where": set text(lmu_red)
  show "|": set text(lmu_red)
  show "Type": set text(lmu_orange)
  r
}

= Introduction <introduction>
Initially introduced in @rbtOriginal, red-black trees are self-balancing binary search trees
with time complexity of $O(log(n))$ for insertion, deletion and lookup.
They perform better than naive binary search trees, which degenerate as linked lists with time complexity of $O(n)$ in the worst case.

For this reason red-black trees are widely used in computer science where efficient ordered data storage and retrieval are needed,
e.g. in the standard library implementation in different programming languages
(`std::map` from C++, `TreeMap` from Java Collections Framework)
and in the virtual memory management in operating systems (`mm_struct` in the Linux kernel).

The original implementation of red-black trees is rather imperative in nature,
which is complex to implement, requiring careful handling of pointers,
parent-child relationships, and rotations to maintain balance.
The insertion algorithm was ported to a more functional version in @Okasaki1999,
using recursion and pattern matching to enforce the two crucial red-black invariants:
- Color Invariant: Every red node has only black children, where all leaves are considered black.
- Height Invariant: Every path from a given node to any of its leaves goes through the same number of black nodes.

In this report, we follow the method presented in @nipkowtrees to verify red-black trees as presented in
@Okasaki1999 in Lean 4.
We provide a verified implementation of red-black trees and a general framework to prove properties about
operations on red-black trees in @framework.
Furthermore, we also show that our implementation is reasonably close to C++ `std::map` in terms of
performance in @performance.


= Red-Black Tree Framework <framework>
The goal of our formalization is to provide an implementation of sets as red-black trees with a complete
surface level API such that users of the data structure likely never have to peek into the internals
to do a proof. For this approach we combine the general approach taken by the Lean standard library
team for data structure verification with ideas for a similar approach, specifically geared to
red-black trees from @nipkowtrees. Our design takes the following steps:
1. Define an efficient representation of red-black trees and the well known functional approaches to
   implementing algorithms on them efficiently in @raw.
2. Verify the key invariants from the literature for our implementation in @invariants.
3. Connect red-black trees to a model of sorted lists and use this model to verify the surface level
   API of the tree in @surface.

== Raw Red-Black Tree Definitions <raw>
For the underlying red-black tree constructor, we choose the following definition:
```lean
inductive Raw (α : Type u) where
  | nil : Raw α
  | node (left : Raw α) (data : α) (color : Color) (right : Raw α) : Raw α
```
where `Color` is an inductive type of either `black` or `red`, which enables Lean to encode it as just an 8 bit integer stored within the node.
#footnote[https://lean-lang.org/lean4/doc/dev/ffi.html#translating-types-from-lean-to-c]

In addition, this definition is specifically geared towards _functional but in-place_ (FBIP) usage,
a compiler optimization for Lean 4 first described in @immutablebean.
To showcase this, let us consider some alternative ways to define it:

1. @nipkowFDSA defines a red-black tree by storing a tuple of data and color within a normal tree.
   ```sml
   datatype 'a tree = Leaf | Node ('a tree) 'a ('a tree)
   type_synonym 'a rbt = ('a × color) tree
   ```
   This introduces the overhead of an additional pointer indirection.

2. Directly encode the color in different tree constructors.\
   This will destroy FBIP as the implementation within Lean only reuses memory across the same constructor for destructive updates.
   Thus, recoloring a node after an operation would not fall under FBIP. We believe our approach to
   have an acceptable overhead (storing an additional 8 bit field) compared to calling the
   allocator more often than necessary.

The most basic operations for any data structure are `insert`, `erase` and `contains`.
Defining `contains` for any binary search tree is a very simple recursive function.

Insertion is an adaption of @nipkowFDSA to Lean4,
which is mostly the simple, functional approach to balancing demonstrated in @Okasaki1999.

Deletion is defined by Nipkow with the help of the partial function `split_min`.
It enables us to find the best-suited subtree to replace the node we want to remove from the tree.
This is a rather involved routine with lots of control branches.
Instead, we adapt deletion from the `RBMap` defined in the Lean4 Core Repository @leancorelib to our simpler red-black tree.
They make use of the function `appendTrees`,
which is a recursive definition to combine the right-most subtree of the left subtree with the left-most subtree of the right subtree,
while also correcting the colors.
This seems more straightforward to reason about, so we choose to copy that one.

== Invariants <invariants>
=== Binary Search Tree Invariant <bstinv>
We describe the most fundamental invariant of any binary search tree with the following `BST`-invariant:
```lean
inductive BST : Raw α → Prop where
  | nil : BST .nil
  | node (hleft1 : ∀ x ∈ left, x < data) (hleft2 : BST left)
         (hright1 : ∀ x ∈ right, data < x) (hright2 : BST right) :
         BST (.node left data color right)
 ```
It is essential for a correctly working `contains` to prove that both `insert` and `erase` preserve this invariant.
Otherwise we wouldn't know how to traverse the tree to find an element.
By decomposing the theorems about the operations into lemmas about how the underlying functions preserve the invariants,
we can profit a lot from a well developed `simp`-set.
Since these functions have a lot of similar cases, it would become quite repetitive to prove the subgoals without the help of automation.
Therefore we try to reduce all the used functions to common terms and functions,
s.t. the proof automation - in this case `aesop` @aesop - can reason with the context about the goals.
Afterwards the development loop mostly boils down to understanding where the proof automation gets stuck,
and then extend either `simp` or `aesop` with new theorems to enable more progress or introduce some case specific fact about e.g. transitivity.

Since this invariant is the easiest to automate due to the straightforward structure and also the easiest way to show that our red-black tree implementation has no bad code path,
we focused and accomplished this as our first major goal.

=== Red Black Tree Invariant <rbinv>
To reiterate, a red-black tree is a colored extension of a normal binary search tree with two extra invariants:
1. `ChildInv`: Every red node has only black children, where all leaves are considered black.
2. `HeightInv`: Every path from a given node to any of its leaves goes through the same number of black nodes.

The combination of those two allow us to prove a logarithmic height upper bound which implies $O(log(n))$
performance characteristica for `insert`, `erase` and `contains`.
Thus our job is to show that the empty red-black tree and any operation on a red-black tree uphold those invariants.

We follow the approach laid out by @nipkowFDSA
where he introduces two tricks to prove these invariants.
First, he describes a weaker child invariant for red-black trees,
where only the children of a node have to preserve the invariant.
```lean
def ChildInv2 (t : Raw α) : Prop :=
  ChildInv (paintColor .black t)
```
This weaker invariant is interesting as the internal recursive functions of `insert` and `erase`
do not maintain `ChildInv`. However they maintain `ChildInv2` and both `insert` and `erase` paint
the root black as a final step, allowing us to recover `ChildInv` from `ChildInv2`.
Secondly, Nipkow introduces a sufficient condition for the `HeightInv`:
```lean
inductive HeightInv : Raw α → Prop where
  | nil : HeightInv .nil
  | node (hleft : HeightInv left) (hright : HeightInv right)
         (h : left.blackHeightLeft = right.blackHeightLeft) :
         HeightInv (.node left data color right)
```
`blackHeightLeft` recursively traverses only the left subtree, and increments if the node is black.
Since `HeightInv` traverses the complete tree we can still reach conclusions about all paths from the root,
therefore allowing us to reason about the recursive cases more easily.

In comparison to the `BST`-invariant, these invariants are less straightforward to prove since there is branching over the colors.
Therefore the decomposition and the `simp` lemmas require more thought,
but are in turn also less useful without explicit information about the color of a node.
Since we do not wish to generally case split on the color - as this is only necessary for particular cases -, we had a harder time fully automating the proofs.
Beyond this, there exist code paths, where the invariants depend on each other,
e.g. where we can deduce that a node is `red` since we know it is not a `black` node and due to `HeightInv` it also cannot be `nil`.
These cases require some manual intervention before letting `simp` or `aesop` solve the remainder.

== Surface Level API <surface>
After providing the basic operations and verifying that they preserve the invariants we can pack
them up into a subtype of red-black trees that always have their invariants attached and re-expose
all invariant preserving operations as functions on these red-black trees. Note that this additional
level of abstraction is zero-cost performance wise as Lean represents subtypes in the same way
as the original type. #footnote[https://lean-lang.org/lean4/doc/dev/ffi.html#translating-types-from-lean-to-c]

Because this subtype is always known to be a valid binary search tree we can relate operations on
it to operations on its inorder representation as a list as seen in @nipkowtrees. To do this we must
provide:
1. For each proposition on the tree a lemma that translates the proposition to a proposition about
   sorted lists, for example for membership: `x ∈ t ↔ x ∈ t.inorder`
2. For every operation on the tree a lemma that explains what happens when `inorder` is applied
   to the result of the operation, for example for inserting an element: `inorder (t.insert x) = sortedInsert (inorder t) x`

By combining all of these lemmas into a custom simp set we can build a tactic `simp_to_model` that
translates arbitrary propositions about the surface level API into propositions about sorted lists.
As these propositions are usually provable much easier than ones about red-black trees directly,
it becomes much easier to both build the initial surface level API but also extend on it later on
if necessary.

Now that we have all tools to make proofs about the behavior of red-black tree operations easy, the
key question is what lemmas we need to prove in order to provide a complete API for users of our
library. To determine this we use the API design approach by the Lean standard library
team which considers how any operation in the API interacts with any other operation
and provides one or more lemmas for that interaction. This leaves us with a lemma coverage as seen
in @api-lemmas, all of which are proven either from each other or by `simp_to_model` and induction
over sorted lists.

#let check = table.cell(
  fill: green.lighten(60%),
)[#sym.checkmark]

#let na = table.cell(
  fill: gray.lighten(60%),
)[N/A]

#let gen = table.cell(
  fill: green.lighten(60%),
)[Gen]

#figure(
  table(
    columns: 8,
    table.header(
      [], [`empty`], [`insert`], [`erase`], [`isEmpty`], [`mem`], [`contains`], [`size`]
    ),
    [`empty`], na, gen, gen, check, check, check, check,
    [`insert`], gen, gen, gen, check, check, check, check,
    [`erase`], gen, gen, gen, check, check, check, check,
    [`isEmpty`], check, check, check, na, check, check, check,
    [`mem`], check, check, check, check, na, check, check,
    [`contains`], check, check, check, check, check, na, check,
    [`size`], check, check, check, check, check, check, na
  ),
  caption: [API Lemma Coverage, Gen(aralized) means provable via `simp` from others],
) <api-lemmas>


= Performance <performance>
As a last step in the design of our library we want to ensure that it has reasonable performance
characteristics. Towards this we provide both theoretical and experimental evidence. For one we have a
proof, based on the invariants from @invariants., that the height of any of our red-black trees $t$
is bounded above by $2 dot log_2(abs(t) + 1)$. This bound gives us high confidence that the
invariants we defined are meaningful and that the operations have good asymptotic behavior.

Beyond this theoretical evidence we also perform an experimental evaluation against `std::map` from
the C++ standard library which is often implemented as a red-black tree as well. This evaluation is
done on a 13th Gen Intel(R) Core(TM) i7-1360P CPU using Clang 19.1.7. We test both insertion
and lookup of sequential and randomly generated elements, the results can be seen in
@perf-data. While Lean does pay an overhead compared to C++ we believe this to be reasonable for
most use cases in Lean. Furthermore, just like many other data structures defined using `inductive`
in Lean, our red-black tree may be used as an efficient persistent data structure which `std::map`
may not.

#figure(
  grid(
    columns: (auto, auto),
    rows: (auto, auto),
    image("figures/sequential_insert.svg"),
    image("figures/sequential_search.svg"),
    image("figures/random_insert.svg"),
    image("figures/random_search.svg"),
  ),
  caption: [Performance Evaluation vs C++ `std::map`]
) <perf-data>


= Conclusion <conclusion>
In summary we provide a reasonably efficient red black tree implementation that likely has
enough proof API such that no user should ever need to peek below it. Beyond usability this has the added
benefit that we can almost arbitrarily refactor the internals without breaking user code as long as
the lemmas we provide keep holding.

While we limited ourselves to just sets as red black trees, the above approach can be extended to
maps or dependent maps as has been shown in the Lean standard library for both hash and tree based
containers. Beyond this we can add more operations such as `min?`, `max?`, `ForIn` etc. very easily
by repeating the design process for that single operation.

#[Total counted characters without code blocks: #total-characters] <no-wc>

#bibliography("references.bib", title: [References])
