#import "@preview/codelst:2.0.0": sourcecode
#import "@preview/touying:0.5.5": *
#import "@preview/diagraph:0.3.0" : raw-render
#import themes.metropolis: *

#let g_lean_blue = rgb("#0073A3")

#let target_date = datetime(year: 2025, month: 1, day: 15)

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Automated Bit-Level Reasoning in Lean 4],
    author: [Henrik Böving],
    date: target_date.display(),
    institution: [Lean FRO],
  ),
  config-colors(
    primary: g_lean_blue,
    secondary: g_lean_blue,
  ),
  config-common(
    slide-level: 2
  )
)

#title-slide()


= Motivation

== Motivation

A slide with some *important* information and an equation:
#v(8%)
$ x_(n+1) = (x_n + a / x_n) / 2 $

#pagebreak()

#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  def naive (state : BitVec 32) : BitVec 32 :=
    (((state.zeroExtend 64) * 48271) % 0x7fffffff).extractLsb 31 0

  def opt (state : BitVec 32) : BitVec 32 :=
    let product := (state.zeroExtend 64) * 48271
    let x := ((product &&& 0x7fffffff) + (product >>> 31)).extractLsb 31 0
    let x := (x &&& 0x7fffffff) + (x >>> 31)
    x

  theorem opt_correct {state : BitVec 32} (h1 : state > 0) (h2 : state < 0x7fffffff) :
      naive state = opt state := by
    unfold naive opt
    sorry -- now what?
  ```
  )
]


== Another topic
Initial content of the slide
#pause
Extra content for the same slide referencing @cadical:

== And Inverter Graphs (AIG)

// This is probably doable with some grid and pause/meanwhile?
#slide[
  #[
    #show raw: set text(size: 13pt)
    #sourcecode(
      ```lean
      inductive Decl (α : Type) where
        | const (b : Bool)
        | atom (idx : α)
        | gate (l r : Nat) (linv rinv : Bool)

      structure AIG (α : Type) where
        decls : Array (Decl α)
        cache : Cache α decls
        invariant : IsDAG α decls
      ```)
  ]
  #uncover("2-")[
    Need to:
    - write translators from `BVExpr` to `AIG`
    - build `AIG` theory
    - prove equivalence to `BitVec` operations:
      - thanks to Siddharth Bhat for `BitVec` theory!
  ]
][
  #[
    #set align(center)
    #show raw: set text(size: 13pt)
    ```
    #[.atom 0, .atom 1,
      .gate 0 1 true false, .gate 0 2 true true]
    ```
    #raw-render(
      ```dot
    Digraph AIG {
      0 [label="0", shape=doublecircle];
      1 [label="1", shape=doublecircle];
      2 [label="2 ∧",shape=trapezium];
      3 [label="3 ∧",shape=trapezium];
      3 -> 0 [color=red];
      3 -> 2 [color=red];
      2 -> 0 [color=red];
      2 -> 1 [color=blue];
    }
    ```)
  ]
]

= Performance Evaluation
== What's out there?
- 1
- 2
  - 2.1
  - 2.2
- 3

== Conclusion
- nipkow proofs
- reduce proofs to model
- performs on the same magnitude as an optimized c++ implementation

= Questions?

= Bibliography <touying:hidden>
== Bibliography <touying:hidden>
#bibliography("references.bib")
