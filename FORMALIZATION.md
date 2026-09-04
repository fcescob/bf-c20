# What Lean proves

The exact main statement is `C20.five_matchings_cover` in `C20.lean`:
for **any vertex-position type V**, any two cycles with odd closed orbits,
and any five perfect matchings whose spoke sets partition V, adjoining
the spoke matching gives six perfect matchings covering every edge twice.
There is no upper bound on a cycle length, and no finite census premise.

The second theorem, `C20.tait_double_cover`, proves that three perfect
matchings partitioning all edges produce a six-matching double cover by
repeating each matching twice. These are the two terminal branches in the
written proof.

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
`lake env lean C20.lean` to print the axiom dependencies. The only import
is `Std`. Arithmetic automation produces kernel-checked terms.
There is no external C++ result imported into Lean, and no added axiom,
admitted proof, or `native_decide` proof.

The following steps are **not** yet Lean formalized:

1. Extracting and normalizing the boundary type from Q.
2. Identifying complement cycle parity with the auxiliary weighted graph.
3. Proving exhaustive coverage and checking the full finite boundary lemma in Lean.
4. Constructing the five perfect matchings from common-good classes, including arbitrary gap lengths.
5. Extracting the two alternating perfect matchings from an even complement.

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
