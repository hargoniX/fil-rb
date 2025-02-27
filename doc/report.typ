#import "@preview/fletcher:0.5.0" as fletcher: diagram, node, edge
#import "@preview/codelst:2.0.0": sourcecode
#import "@preview/curryst:0.1.1"
#import "@preview/wordometer:0.1.4": word-count, total-characters
#import "template.typ": *

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

#show: word-count.with(exclude: (strike, raw, <no-wc>))
#show figure.caption : set text(10pt)

#show raw.where(lang: "lean"): r => {
  show "inductive": set text(lmu_red)
  show "where": set text(lmu_red)
  show "|": set text(lmu_red)
  show "Type": set text(lmu_orange)
  r
}

= Introduction <introduction>
Red-Black Tree (RbTree) is a kind of self-balancing binary search
trees with time complexity of $O(log(n))$,
ensured by balance maintaning via color properties and rotations.
Otherwise the performace will degenerate to $O(n)$ as a linked list in worst case.

Since its first introduction by Guibas and Sedegewick@rbtOriginal,
RbTree has been widely used in computer science where efficient ordered data storage and retrieval are needed,
e.g. in the standard library implementation in different programming languages
(`std::map` from C++, `TreeMap` from Java Collections Framework)
and in the virtual memory management by operating systems (`mm_struct` in Linux kernel).

Besides Guibas and Sedgewick,
Okasaki has fistly come up with an functional version of RbTree insertion algorithm,
which is implementated simply and compactly in Haskell@Okasaki1999.
Unlike an imperative implementation of RbTree which need to deal with detailed opeations on the tree structure,
the functional implementation rather focuses on the description of the invariants which are crucial to balancing.
They are:
- Color Invariant: No red node has a red parent. The root color and the empty RbTree are considered as black.
- Height Invariant: Every path from the root to an empty node contains the same number
of black nodes.

In this report, we follow the method from Nipkow et al.(2024)@fdc to build our formalization of RbTree in Lean4.
We provide a verified implementation of RbTree and a general framework to prove properties about opeations on RbTree.
Furthermore, we also show that our implementation has close performance compared with C++ `std::map`.


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

== Raw RbTree Defintions <raw>
For the underlying RbTree constructor, we chose the following definition:
```lean
inductive Raw (α : Type u) where
  | nil : Raw α
  | node (left : Raw α) (data : α) (color : Color) (right : Raw α) : Raw α
```
where `Color` is an inductive type of either `black` or `red`, which enables Lean to encode it as just an 8 bit integer stored within the node.

In addition, this definition is specifically geared towards _functional but in-place_ (FBIP) usage.
To showcase this, let us consider some alternative ways to define it:

1. #cite(<nipkowFDSA>, form: "prose") defines a RbTree by a tuple of a normal tree and a color.
   ```coq
   datatype 'a tree = Leaf | Node ('a tree) 'a ('a tree)
   type_synonym 'a rbt = ('a × color) tree
   ```
   This introduces the overhead of an additional pointer indirection.

2. Directly encode the color in different tree constructors.\
   This will destroy FBIP as the implementation within Lean only reuses memory across the same constructor for destructive updates @immutablebean.
   Thus, recoloring a node after an operation would not fall under FBIP.

We believe our approach to be an acceptable overhead compared to calling the allocator more often than necessary.

The most basic operations for any datastructure are `insert`, `erase` and `contains`.
// TODO: do we want to explain `baliL/R`, `baldL/R` and what they fix on traversal?
Defining Containment for any binary search tree is a very simple recursive function.

Insertion is an adaption of #cite(<nipkowFDSA>, form: "prose") to Lean4,
which is mostly #cite(<Okasaki1999>, form: "prose") simple, functional approach to balancing.

Deletion is defined by Nipkow with the help of the partial function `split_min`.
It enables us to find the best-suited subtree to replace the node we want to remove from the tree.
This is a rather involved routine with lots of control branches.
Instead, we adapted deletion from the `RBMap` defined in the Lean4 Core Repository @leancorelib to our simpler Tree.
They make use of the function `appendTrees`,
which is a recursive definition to combine the right-most subtree of the left subtree with the left-most subtree of the right subtree,
while also correcting the colors.
This seemed more straightforward to reason about, so we choose to copy that one.

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
team which considers how any operation in the API interacts with any operation any other operation
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
proof, based on the invariants from @invariants., that the height of any of our red black trees $t$
is bounded above by $2 dot log_2(abs(t) + 1)$. This bound gives us high confidence that the
invariants we defined are meaningful and that the operations have good asymptotic behavior.

Beyond this theoretical evidence we also performed an experimental evaluation against `std::map` from
the C++ standard library which is often implemented as a red black tree as well. This evaluation was
performed on a 13th Gen Intel(R) Core(TM) i7-1360P CPU using Clang 19.1.7. We tested both insertion
and lookup of sequential and randomly generated elements, the results can be seen in
@perf-data. While Lean does pay an overhead compared to C++ we believe this to be reasonable for
most use cases in Lean. Furthermore, just like many other data structures defined using `inductive`
in Lean, our red black tree may be used as an efficient persistent data structure which `std::map`
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

#[Total characters: #total-characters (titlepage, code and this line excluded)] <no-wc>

#bibliography("references.bib", title: [References])
