# Lean verification status

The complete unbounded graph reduction has passed Lean. The remaining
work is to close the size-10 finite constants and check the final theorem
with those dependencies. The public research release is authorized while
that computation continues; it does not claim completed end-to-end Lean
verification.

## Exact theorem and checked reduction

`C20.C20Statement`, defined in `C20Statement.lean`, states:
for every m ≥ 3, two connected successor cycles on `Fin m` and a simple
spoke-alternating circuit of length at most 20 admit six perfect matchings
covering each edge exactly twice. There is no upper bound on m and no
supplied matching, boundary type, or gap witness in that target.

`C20.c20_from_finite` in `C20Assemble.lean` proves
`MatchingBoundaryTheorem → C20Statement`. The entire deduction passed
[run 33923291931](https://github.com/fcescob/bf-c20/actions/runs/33923291931),
including all dependencies. Its axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The checked construction includes:

- The complete even-order case by alternating cycle edges.
- Extraction of the actual circuit vertices and its two domino matchings.
- First-return compression from the actual connected cycles, with exact
  distances and parity laws for paths of arbitrary length.
- Normalization at a common root, reversing one cycle when needed.
- The proof that the compressed flags have odd parity on odd cycles.
- Transfer from literal finite row equations to the compressed cycles.
- Expansion of the finite matching patterns into physical perfect
  matchings and assembly of the six-matching double cover.

The principal modules are `C20Cycles`, `C20Kernel`, `C20Even`,
`C20Compression`, `C20Domino`, `C20Coordinates`, `C20Normalize`,
`C20Encoding`, `C20Reversal`, `C20ParityFinite`, `C20Parity`,
`C20Expansion`, `C20Three`, and `C20Assemble`. The default `lake build`
checks this deduction. It has no admitted proof or native-evaluation axiom.

## Remaining finite proof

`MatchingBoundaryTheorem` quantifies over k ∈ {2,4,6,8,10}, every order
`0 :: tail` whose tail permutes {1,…,k−1}, and every pair of odd flag
vectors. It asserts the existence of two or four explicit matching
patterns whose spoke masks partition the k vertices. It does not assume
connectivity of the two domino matchings, so it covers more states than
the original symmetry-reduced C++ census.

`C20BoundaryMatching.lean` proves that the Boolean checker implies this
literal matching conclusion. Every proposed pattern is checked at every
vertex in both boundary cycles. `BoundarySearch.lean` supplies candidate
masks; the proof does not assume that its search heuristic is correct.

`C20MatchingFinite/Head0.lean` through `Head9.lean` divide the k=10
computation by the second vertex of the order. These use `native_decide`.
`C20MatchingSmall.lean` proves the constants for k = 2, 4, 6, and 8.
[Run 33924041597](https://github.com/fcescob/bf-c20/actions/runs/33924041597)
checked them in 7.7 seconds after compiling the evaluator. The size-2 and
size-4 proofs use kernel reduction; sizes 6 and 8 use native evaluation.
`C20MatchingFinite.lean` combines these smaller cases and every size-10
shard into `matching_up_to_ten_native`. The size-10 jobs are still running.
A completed runtime calculation alone is not a closed Lean theorem.

`C20Theorem.lean` applies the finite theorem to `c20_from_finite` to produce
`C20.c20 : C20Statement`. This file and all finite dependencies must pass
together before the result is described as fully Lean verified. The
complete theorem workflow checks source identity when it reuses shard
artifacts from a previous run.

## Reproduction and trust

With the pinned toolchain installed:

```sh
lake build
lake env lean C20Assemble.lean
```

These commands check and print dependencies for the complete graph
reduction. The full proof target additionally runs the finite computations:

```sh
lake build C20Theorem
lake env lean C20Theorem.lean
```

Lean 4.28.0 and Mathlib 4.28.0 are pinned in `lean-toolchain` and
`lake-manifest.json`. The finite checker uses bundled `Std`; Mathlib is
used for structural graph and permutation reasoning. No external C++
result is imported into Lean.

The finite proof deliberately uses native evaluation. In addition to the
usual logical axioms, `native_decide` trusts `Lean.ofReduceBool`,
`Lean.trustCompiler`, Lean's compiler, and the native implementations of
core operations. This is a larger trusted base than kernel-only
reduction. The final axiom audit must contain no `sorryAx` or user-supplied
axiom. The repository retains earlier finite-check experiments, but the
final target uses the direct matching checker described above.

## Graph semantics and scope

`Cycle V` has mutually inverse successor and predecessor maps and no
loops. `ConnectedCycle` makes each map one cyclic orbit. For `Fin m` and
m ≥ 3 these encode two simple m-cycles. The spoke matching identifies
their vertex-position sets. `ShortCircuit` lists distinct spoke positions
with alternating outer and inner adjacency, so its k positions describe
a circuit with 2k edges.

`EdgeSet` records a Boolean indicator for each spoke and each outgoing
outer and inner cycle edge. `PerfectMatching` asserts at each vertex that
the spoke, incoming edge, and outgoing edge indicators sum to one.
`DoubleCover` asserts six perfect matchings and multiplicity two for
every edge. Repeated matchings are allowed.

The formal target is existence of a six-matching double cover. The
additional class-2 statement in `PROOF.md` specifying two distinguished
members is not separately named in the current formal target. Neither
the written nor formal result asserts that every cycle-permutation graph
has an alternating circuit of length at most 20.
