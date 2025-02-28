#import "@preview/ctheorems:1.1.3": *
#import "@preview/lovelace:0.3.0": *

// Colors used across the template.
#let ctext(x, color) = text(fill: color)[#x]
#let agda_green = rgb("#006C5C")
#let agda_blue = rgb("#003050")
#let lmu_blue = rgb("#0F1987")
#let lmu_cyan = rgb("#009FE3")
#let lmu_orange = rgb("#ff8c00")
#let lmu_green = rgb("#00883A")
#let lmu_red = red

// ctheorems
#let theorem = thmbox(
  "theorem", "Theorem", fill: rgb("#eeffee"), inset: 10pt, breakable: true
)
#let definition = thmbox(
  "definition", "Definition", inset: (top: 0em), breakable: true
)
#let example = thmplain("example", "Example", inset: (top: 0em), breakable: true)
#let proof = thmproof("proof", "Proof", inset: (top: 0em), breakable: true)

// other
#let sblock(x) = block(fill: luma(240), inset: 10pt, radius: 3pt, width: 100%)[#x]
#let mypseudocode(..e) = pseudocode-list(booktabs: true, booktabs-stroke: 1pt + black, hooks: .5em, ..e)

#let titlepage(
  title: "",
  author: "",
  matriculation: "",
  thesis-type: "",
  supervisor: "",
  submission_date: "",
  paper-size: "",
) = {
  set align(center)
  // Institution
  text(14pt, smallcaps("Ludwig-Maximilians-Universität München"))
  linebreak()
  text(14pt, smallcaps("Chair of theoretical Computer Science and Theorem Proving"))
  v(5%)
  image("figures/sigillum.svg", width: 25%)

  // Title
  v(5%)
  line(length: 105%)
  text(16pt, weight: 500, title)
  line(length: 105%)
  v(5%)
  text(14pt)[#thesis-type]
  linebreak()
  text(14pt)[in course type Computer Science]

  // Author information
  v(1fr) // push to bottom
  set align(left)
  grid(
    columns: (100pt, 1fr),
    gutter: 1em,
    "Students:", [#author],
    "Supervisor:", [#supervisor],
    "Submission date:", [#submission_date],
  )
  v(5%)
}

#let official(
  title: "",
  author: "",
  thesis-type: "",
  supervisor: "",
  submission_date: "",
  paper-size: "a4",
  lang: "en",
  body
) = {
  set document(title: title)
  set text(font: "New Computer Modern", size: 11pt, lang: lang)
  set heading(numbering: "1.1")
  set par(leading: 0.65em, justify: true, spacing: 1.2em)
  set list(indent: 1em, spacing: 10pt, tight: false)
  set enum(numbering: "1.", indent: 1em, spacing: 10pt, tight: false)

  show link: set text(fill: blue.darken(60%))
  show raw: set text(font: "JuliaMono", size: 10pt)
  show outline.entry.where(level: 1): it => {
    v(12pt, weak: true)
    strong(it)
  }
  show: thmrules

  // No numbering for titlepage, toc, and abstract
  set page(paper: paper-size, numbering: none)
  titlepage(
    title: title,
    author: author,
    thesis-type: thesis-type,
    supervisor: supervisor,
    submission_date: submission_date,
    paper-size: paper-size
  )
  outline(depth: 3)
  pagebreak()

  // Main Matter
  counter(page).update(1)
  set page(numbering: "1", number-align: center)
  body
}
