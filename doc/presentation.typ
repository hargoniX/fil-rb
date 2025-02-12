#import "@preview/touying:0.5.5": *
#import "@preview/diagraph:0.3.0" : raw-render
#import "@preview/codelst:2.0.0": sourcecode
#import "@preview/fletcher:0.5.0" as fletcher: diagram, node, edge
#import "@preview/ctheorems:1.1.3": *
#import themes.metropolis: *

#let g_lmu_green = rgb("#00883A") // dark-green LMU

#let th_pres = thmbox("theorem", "Theorem", base: none,
  fill: rgb("#eeffee"), inset: 15pt, breakable: true
)
#show: thmrules.with(qed-symbol: $square$)

#let target_date = datetime(year: 2025, month: 3, day: 3)

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Formalizing RBTrees in Lean4],
    subtitle: [Some fun stuff],
    author: [Daniel Soukup, Henrik Böving, Lingyin Luo],
    date: target_date.display(),
    institution: text(14pt, smallcaps("Ludwig-Maximilians-Universität München")),
    logo: figure(image("figures/sigillum.svg", height: 35%)),
  ),
  footer: self => self.info.institution,
  header-right: align(image("figures/sigillum.svg", height: 400%), left),
  footer-progress: false,
  config-colors(
    primary: g_lmu_green,
    secondary: g_lmu_green,
  ),
  config-common(
    slide-level: 2
  ),
  config-page(
    header-ascent: 15%,
  )
)

// should do something like for the relevant lean snippets
//#show raw.where(lang: "agda"): r => {
//  show "plus": set text(lmu_blue)
//  show "+": set text(lmu_blue)
//  show "_+_": set text(lmu_blue)
//  show "ℕ": set text(lmu_blue)
//  show "zero": set text(g_prim)
//  show "suc": set text(g_prim)
//  r
//}

#title-slide()

= Outline <touying:hidden>

#outline(title: none, indent: 1em, depth: 1)

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

== Lean MLIR
#figure(
  image("figures/sigillum.svg", height: 80%),
  caption: [LMU sigillum],
)

== Theorem
#th_pres("Confluence ")[
  For any well-typed term $t$ if $t arrow.r.squiggly^* u_1$ and $t arrow.r.squiggly^* u_2$ for some terms $u_1$ and $u_2$, then there is a term $v$ such that $u_1 arrow.r.squiggly^* v$ and $u_2 arrow.r.squiggly^* v$.
]

== Conclusion
- nipkow proofs
- reduce proofs to model
- performs on the same magnitude as an optimized c++ implementation

= Questions?

= Bibliography <touying:hidden>
== Bibliography <touying:hidden>
#bibliography("references.bib")
