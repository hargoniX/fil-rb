#import "@preview/fletcher:0.5.0" as fletcher: diagram, node, edge
#import "@preview/codelst:2.0.0": sourcecode
#import "@preview/curryst:0.1.1"
#import "@preview/wordometer:0.1.4": word-count, total-characters
#import "@preview/drafting:0.2.1": margin-note
#import "template.typ": *

#let note = margin-note

#let target_date = datetime(year: 2025, month: 3, day: 3)
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

#show: word-count.with(exclude: (strike, raw.where(block: true), <no-wc>))
#show figure.caption : set text(10pt)

#show raw.where(lang: "lean"): r => {
  show "inductive": set text(lmu_red)
  show "where": set text(lmu_red)
  show "|": set text(lmu_red)
  show "Type": set text(lmu_orange)
  r
}

= Introduction <introduction>
Red-Black Trees (RbTree) #note(side:left)[Let's stick to just "red-black tree"] are self-balancing binary search
trees with time complexity of $O(log(n))$. #note[Time complexity for which operations etc.]
This performance is ensured by balance maintaining via color properties #note(side:left)[Color properties
doesn't really mean anything to people that don't already know rbtrees. Instead we should probably
say something like, rotations guided by colors of the nodes.] and rotations.
Without balancing, it #note["It" is not really clear here, we should explain that non self balancing
trees degenerate in this fashion] will degenerate to $O(n)$ as a linked list in the worst case.

Since their first introduction by Guibas and Sedegewick@rbtOriginal #note[Just stick to @rbtOriginal for now no spelling out the authors yourself, same with other citations],
RbTrees have been widely used in computer science where efficient ordered data storage and retrieval are needed,
e.g. in the standard library implementation in different programming languages
(`std::map` from C++, `TreeMap` from Java Collections Framework)
and in the virtual memory management in operating systems (`mm_struct` in the Linux kernel).

Besides Guibas and Sedgewick, #note(side:left)[This should explain first that the initial algorithm is rather
imperative in nature and that it was thus necessary for Okasaki to do some work towards this.]
Okasaki has firstly come up with an functional version of RbTree insertion algorithm,
which is implemented simply and elegantly in Haskell@Okasaki1999.
Unlike an imperative implementation of RbTree
which handles detailed operations on the tree structure,
the functional version focuses on enforcing the invariants, #note[This is a bit weird to say,
obviously the imperative code also sticks to the invariants]
which are crucial for maintaining balance, in a more descriptive manner.
They are:
- Color Invariant: No red node has a red parent. The root color and the empty RbTree are considered as black.
- Height Invariant: Every path from the root to an empty node contains the same number of black nodes.

In this report, we follow the method from @nipkowtrees to build our formalization of RbTrees in Lean4.
We provide a verified implementation of RbTrees and a general framework to prove properties about
operations on RbTrees in @framework.
Furthermore, we also show that our implementation has close performance compared with C++ `std::map`
in @performance.


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

== Raw Red-Black Tree Defintions <raw>
For the underlying red-black tree constructor, we choose the following definition:
```lean
inductive Raw (α : Type u) where
  | nil : Raw α
  | node (left : Raw α) (data : α) (color : Color) (right : Raw α) : Raw α
```
where `Color` is an inductive type of either `black` or `red`, which enables Lean to encode it as just an 8 bit integer stored within the node.
#footnote[https://lean-lang.org/lean4/doc/dev/ffi.html#translating-types-from-lean-to-c]

In addition, this definition is specifically geared towards _functional but in-place_ (FBIP) usage.
To showcase this, let us consider some alternative ways to define it:

1. @nipkowFDSA defines a red-black tree by storing a tuple of data and color within a normal tree.
   ```sml
   datatype 'a tree = Leaf | Node ('a tree) 'a ('a tree)
   type_synonym 'a rbt = ('a × color) tree
   ```
   This introduces the overhead of an additional pointer indirection.

2. Directly encode the color in different tree constructors.\
   This will destroy FBIP as the implementation within Lean only reuses memory across the same constructor for destructive updates @immutablebean.
   Thus, recoloring a node after an operation would not fall under FBIP. We believe our approach to
   have an acceptable overhead (storing an additional 8 bit field) compared to calling the
   allocator more often than necessary.

The most basic operations for any data structure are `insert`, `erase` and `contains`.
Defining `contains` for any binary search tree is a very simple recursive function.

// TODO: do we want to explain how balancing works and how they operate on traversal?
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
A red-black tree is a colored extension to a normal binary search tree with two major new invariants:
#note[I am still not happy with this introduction, but the later note on restructuring probably will impact this sentence as well]

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

// Explain some considerations we had in mind for our simp set.
To prove that `insert` and `erase` preserve both of these invariants,
we decompose the theorem into lemmas about how the underlying functions preserve the invariants.
This decomposition profits a lot from a strong `simp` set,
where - beside the trivial properties about every function - we mostly try to reduce the different functions to common terms,
s.t. the proof automation - in this case `aesop` @aesop - can reason with the context about the goals.

Since these functions have a lot of cases, it becomes quite repetitive to prove these subgoals without automation.
So the development loop mostly boils down to understanding where the proof automation gets stuck
and then extend either `simp` or `aesop` with new theorems to enable more progress. However we did
observe situations where just equipping `simp` or `aesop` with more knowledge does not solve a
goal. For example both of the red-black-tree-specific invariants are dependent on the color
of the node. However we do not wish to generally case split on the color as this is only necessary
for very particular cases. Beyond this, there exist code paths, where the invariants depend on each other,
e.g. where we can deduce that a node is `red` since we know it is not a `black` node and due to
`HeightInv` it also cannot be `nil`. These cases require some manual intervention before letting
`simp` or `aesop` solve the remainder.

#note(side:left)[Given that we proved this first and it is easier maybe this section should be higher? - I agree, but I didnt find a good transition the other way around. Will fix this evening]
Finally, it is essential for @surface and a correctly working `contains` to prove that operations on a red-black tree preserve the `BST`-invariant,
therefore letting us know that `inorder` results in a sorted list.
In comparison to the other invariants, the `BST`-invariant is more straightforward to decompose since there is no branching over the colors.
Therefore the same decomposition mechanism combined with reasonable `aesop`-calls
are able to handle most of the proofs besides some transitivity.
Since this invariant is the easiest to automate and also the easiest way to show that our red-black tree implementation has no bad code path,
we focused on this as our first major goal.

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

#[#ctext([*DELETE THIS BEFORE SUBMITTING*], red): Total characters: #total-characters (titlepage, code and this line excluded)] <no-wc>

#bibliography("references.bib", title: [References])
