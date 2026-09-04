# What Lean proves

**Publication target:** `C20.C20Statement` in `C20Statement.lean` states
the whole theorem from two connected cycles and a short alternating
circuit, with no boundary or matching witnesses assumed. A checked proof
of that statement is still required. Defining it is not proving it.

The core statement is `C20.five_matchings_cover` in `C20.lean`:
for **any vertex-position type V**, any two cycles with odd closed orbits,
and any five perfect matchings whose spoke sets partition V, adjoining
the spoke matching gives six perfect matchings covering every edge twice.
There is no upper bound on a cycle length, and no finite census premise.

The second theorem, `C20.tait_double_cover`, proves that three perfect
matchings partitioning all edges produce a six-matching double cover by
repeating each matching twice. These are the two terminal branches in the
written proof.

The stronger constructive theorem `C20.good_partition_cover` takes five
spoke classes that partition V, together with a `GapWitness` on each cycle
for each class. It constructs the cycle edges, proves the resulting five
edge sets are perfect matchings, and then applies the lifting theorem.

`GapWitness.distance v` is the distance to the next selected position,
allowing zero at a selected position. Its explicit laws say: distance is
zero exactly at selected positions; away from them it decreases by one
along a successor step; immediately after a selected position it is even.
The written odd-gap argument supplies those laws because consecutive
selected positions are separated by an odd number of edges. The formal
construction selects an outgoing cycle edge exactly when the distance is
positive and even. `gap_incidence` checks its exact vertex incidence.

## Further checked components

`C20Gaps.lean` now proves `C20.common_good_partition_cover`: the actual
nonempty common-good cyclic-arc classes imply the full cover. It derives
first-hit distances from connectedness, so those distances are no longer
assumed. This component passed remote Lean checking in run 33915901637.

`C20Boundary.lean` proves soundness of explicit boundary witnesses and
completeness of the permutation generator. `BoundarySearch.lean` proves
that a successful finite Boolean check implies the boundary dichotomy
for every enumerated permutation and odd flag pair. Pure Lean runtime
checks through k=10 passed. Run 33916749650 checked the size-10 Boolean
in 22:05.02 on a remote runner. These runtime checks alone are not closed
Lean proofs of the finite constants. `C20Finite.lean` closes k=4 by
kernel reduction. A k=6 kernel-reduction probe exceeded 15 minutes.

`C20Expansion.lean` proves local matching incidence is preserved by
expanding boundary edges into paths of arbitrary lengths, given the
stated first-hit compression equations. It passed Lean checking in
run 33917042568; that run failed later at the separate finite-constant
proof, not at the expansion lemma.

`C20Cycles.lean` and `C20Kernel.lean` establish exact cycle periods and
extract the actual circuit vertex set and cyclic lists. `C20Even.lean`
proves the full graph conclusion for every even m. `C20Compression.lean`
derives the connected boundary cycle and expansion interface from any
nontrivial selected set. These components passed run 33919711175.

The separate `C20NativeFinite.lean` experiment attempts all remaining
finite constants using Lean's native evaluator. Its trust boundary
includes `Lean.ofReduceBool`, the compiler, and native implementations
of core operations. This is not kernel-only evaluation. The experiment
is excluded from the default build and does not open the publication gate.

The complete C20 theorem is still unformalized and the publication gate
remains closed.

## Encoding and semantics

`Cycle V` gives mutually inverse successor and predecessor maps, with no
loops. An `EdgeSet V` has Boolean indicators for a spoke at v, the outer
cycle edge from v to its outer successor, and the inner cycle edge from v
to its inner successor. These label the actual edges of a cycle-permutation
graph after using M to identify both cycles' position sets. The theorem
works for a broader class of odd closed orbits too.

At the outer copy of v the incident edges are exactly its spoke, the
outgoing outer edge at v, and the incoming outer edge at `prev v`.
`PerfectMatching` asserts their three Boolean indicators sum to one; it
asserts the analogous equation at the inner copy. Thus it encodes the
usual perfect-matching condition directly. The cycle edges are labelled
objects; if this model is instantiated on 2-cycles it retains parallel
edges. The written theorem uses simple cycles of length at least three.

`DoubleCover` asserts both that all six selected edge sets are perfect
matchings and that every spoke, outer edge and inner edge has multiplicity
two. It permits repeated matchings. `Five` and `Six` are explicit ordered
tuples, with no quotient by permutations.

The proof first sums the five perfect-matching equations at a vertex.
Exactly one uses the spoke, so the adjacent cycle-edge counts add to four.
`odd_recurrence` proves that this recurrence on an odd closed orbit forces
every count to be two. Adding M then covers every spoke twice too.

## Formal trust boundary

Run `lake build` with the pinned Lean 4.28.0 toolchain, then
`lake env lean C20.lean` to print the axiom dependencies. That core file
imports `Std`; the structural modules also import pinned Mathlib.
Arithmetic automation in the default build produces kernel-checked terms.
No external C++ result is imported into Lean. The default build has no
added axiom, admitted proof, or `native_decide` proof. The separate native
experiment and its additional trust are described above. The basic Lean principles
`propext` and `Quot.sound` are reported by the axiom audit; the constructive
gap proof also uses `Classical.choice` through standard proof automation.

The following steps are **not** yet Lean formalized:

1. Completing the domino normalization and boundary-flag dictionary from Q. Vertex-set extraction and first-return compression are checked.
2. Identifying complement cycle parity with the auxiliary weighted graph.
3. Closing the full finite boundary theorem in Lean. Permutation-enumeration completeness and witness-checker soundness are proved, but the successful runtime calculations are not themselves proof terms for the finite constants.
4. Transferring both finite conclusions back to the actual graph, including extracting alternating matchings from an even switched complement.

Those steps are proved in the written argument and checked computationally
where applicable. The complete C20 result is therefore computer-assisted;
the Lean component verifies its final unbounded lifting implications.
A successful Lean build alone must not be cited as a full formal proof of
the short-circuit theorem.

## Formalization mechanism

Target: the lifting implication consumed by the C20 cover construction.
Representation: exact Boolean edge incidence and integer multiplicities.
Candidate lemma: the universally quantified `five_matchings_cover` above.
Inputs: five physical perfect matchings and a spoke partition, derived
in §4 of the written proof. Certificate: a Lean kernel-checked proof term.
Kill condition: a scope mismatch, an admitted obligation, or a compilation
failure prevents describing this component as formally proved. The
finite reduction is never replaced by a sampled graph calculation.
