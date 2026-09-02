// Lilaq port of fig:comparison-wasm-opt-optimizations from 05-evaluation.tex
#import "@preview/lilaq:0.6.0" as lq

#set page(width: auto, height: auto, margin: 5pt)
// Latin Modern matches the thesis body font; the others are fallbacks.
#set text(font: ("Latin Modern Roman", "New Computer Modern", "Libertinus Serif"), size: 10pt)

// Rotate the x tick labels by -45deg, like `xticklabel style={rotate=315}`.
#show: lq.show_(
  lq.tick-label.with(kind: "x"),
  it => box(width: 0pt, align(right, rotate(-45deg, reflow: true, it))),
)

#let benchmarks = ("demo1", "vs_easy", "vs_hard", "binom", "color", "sha_fast", "ack_3_9", "coqprime")

#let no-opts     = (2, 22, 89, 18, 200, 78, 105, 89)
#let coalesce    = (2, 19, 85, 11, 53, 59, 106, 84)
#let o1          = (2, 18, 73, 9, 48, 51, 93, 74)
#let o2          = (2, 18, 73, 9, 47, 50, 92, 75)

// babyblueeyes, and dvips Gray at 35% / 65% / 100%.
#let c-no-opts  = rgb("#A1CAF1")
#let c-coalesce = rgb("#D3D3D3")
#let c-o1       = rgb("#ACACAC")
#let c-o2       = rgb("#808080")

#let xs = range(benchmarks.len())
#let bar-width = 0.19

#lq.diagram(
  width: 12cm,
  height: 7cm,
  ylabel: [Run time (ms)],
  ylim: (0, 210),
  grid: none,
  margin: 4%,
  legend: (position: top + left),
  xaxis: (
    ticks: xs.zip(benchmarks),
    subticks: none,
    mirror: false,
  ),
  yaxis: (
    ticks: (50, 100, 150, 200).map(y => (y, str(y))),
    subticks: 1, // one minor tick between majors: 25, 75, 125, 175
    mirror: false,
  ),

  lq.bar(xs, no-opts,  offset: -1.5 * bar-width, width: bar-width, fill: c-no-opts,  stroke: 0.5pt + black, label: [No opts.]),
  lq.bar(xs, coalesce, offset: -0.5 * bar-width, width: bar-width, fill: c-coalesce, stroke: 0.5pt + black, label: [wasm-opt --coalesce-locals]),
  lq.bar(xs, o1,       offset: 0.5 * bar-width,  width: bar-width, fill: c-o1,       stroke: 0.5pt + black, label: [wasm-opt -O1]),
  lq.bar(xs, o2,       offset: 1.5 * bar-width,  width: bar-width, fill: c-o2,       stroke: 0.5pt + black, label: [wasm-opt -O2]),
)
