// Run times of the CertiRocq benchmarks, one bar group per benchmark:
// unoptimized, the two binaryen references, and this pass.  Lilaq port of
// fig:comparison-wasm-opt-optimizations from 05-evaluation.tex.
//
// The numbers come from results.json, which `benchmark.py --json results.json`
// writes -- nothing here is hardcoded, re-run the benchmark to update the plot.
#import "@preview/lilaq:0.6.0" as lq

#let data = json("results.json")

#set page(width: auto, height: auto, margin: 5pt)
// Latin Modern matches the thesis body font; the others are fallbacks.
#set text(font: ("Latin Modern Roman", "New Computer Modern", "Libertinus Serif"), size: 10pt)

// Rotate the x tick labels by -45deg, like `xticklabel style={rotate=315}`.
#show: lq.show_(
  lq.tick-label.with(kind: "x"),
  it => box(width: 0pt, align(right, rotate(-45deg, reflow: true, it))),
)

// (folder in results.json, legend entry, fill).  babyblueeyes for the
// unoptimized baseline, dvips Gray at 35% / 65% for what binaryen does on its
// own, and a saturated blue for the verified pass.
#let series = (
  ("before", [No opts.], rgb("#A1CAF1")),
  ("before-O2", [wasm-opt -O2], rgb("#D3D3D3")),
  ("before-cl", [wasm-opt \-\-coalesce-locals], rgb("#ACACAC")),
  ("after", [local coalescing (verified)], rgb("#3B6EA5")),
).filter(s => s.at(0) in data.results)

#let value(folder, program) = data.results.at(folder).at(program).time_main

// Programs whose main() is over in a millisecond or two carry no signal at
// this resolution -- their four bars are all 0 or 1 -- so they are left out.
#let programs = data.programs.filter(p => (
  calc.max(..series.map(s => value(s.at(0), p))) >= 5
))
#let xs = range(programs.len())

#let bar-width = 0.8 / series.len()
#let ymax = calc.max(
  ..series.map(s => programs.map(p => value(s.at(0), p))).flatten(),
)

#lq.diagram(
  width: 12cm,
  height: 7cm,
  ylabel: [Run time (ms)],
  ylim: (0, ymax * 1.15),
  grid: none,
  margin: 4%,
  // top right: the tall `color` bar group sits on the left half.
  legend: (position: top + right),
  xaxis: (
    ticks: xs.zip(programs.map(p => raw(p))),
    subticks: none,
    mirror: false,
  ),
  yaxis: (subticks: 1, mirror: false),

  ..series
    .enumerate()
    .map(((i, s)) => lq.bar(
      xs,
      programs.map(p => value(s.at(0), p)),
      offset: (i - (series.len() - 1) / 2) * bar-width,
      width: bar-width,
      fill: s.at(2),
      stroke: 0.5pt + black,
      label: s.at(1),
    )),
)

#v(2pt)
#text(size: 8pt, fill: luma(40%))[
  Mean of #data.runs runs per benchmark (after #data.warmup warmup runs),
  #data.engine.
]
