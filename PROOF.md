# Berge–Fulkerson covers from a spoke-alternating circuit of length at most 20

4 September 2026. **Computer-assisted theorem, with an independently replayed
finite certificate.** No proof for all cycle-permutation graphs is claimed.

## Theorem C20

Let G consist of two vertex-disjoint cycles C and D of the same length m ≥ 3,
together with a perfect matching M between their vertex sets. If G contains
an M-alternating circuit of length at most 20, then G has six perfect
matchings covering every edge exactly twice. There is no bound on m.

More precisely, put N = M △ E(Q) for such a circuit Q. If G is class 2,
the construction below supplies a Berge–Fulkerson cover containing both
M and N. In the other branch the proof explicitly constructs a Tait
colouring and doubles its three colour classes.

The externally published sufficient condition has circuit length at most
16: Luo, Hao, Luo, Zhang and Zhou, *Berge–Fulkerson Conjecture, Perfect
Matching Partial Coverings and Odd Dividers*, JGT (2026),
[doi:10.1002/jgt.70097](https://onlinelibrary.wiley.com/doi/full/10.1002/jgt.70097).
The statement was checked against the publisher's abstract on 4 September
2026; the full text was unavailable. The proof here does not import that
theorem or any of its uninspected hypotheses. Priority beyond that
comparison has not been established.

## 1. Reduction to finitely many boundary types

Identify both cycle vertex sets with a common position set V using M. If
m is even, colour M with one colour and alternate two other colours on
each cycle. Doubling the three perfect matchings proves the theorem.
Henceforth m is odd.

Let Q be an M-alternating circuit of length 2k and let K ⊆ V be its spoke
positions. Each use of a spoke switches between C and D, so k is even.
The edges of Q on C form a matching covering precisely K; the same is
true on D. Consequently K has even runs in both cyclic orders. Since
m is odd and k is even, K is proper. Its even runs have unique domino
tilings, denoted α_C and α_D. After contracting the k spokes of Q,
α_C ∪ α_D is connected. Parallel edges are retained in this auxiliary
union. The perfect matching N consists of these dominoes and all spokes
outside K; it is exactly M △ E(Q).

List K in its C-order as 0,1,…,k−1, starting at a domino's first vertex.
Then α_C = {(0,1),(2,3),…,(k−2,k−1)}. Write its D-order as
d = (d_0,…,d_{k−1}), starting at position 0 and orienting D towards 0's
α_D-partner. Thus d_0 = 0 and α_D = {(d_0,d_1),(d_2,d_3),…}.
Every possible D-order is a permutation of {0,…,k−1} of this form.

Put n = k/2. For each j modulo n, let t_C(j) be the number of positions
outside K on the C-arc from 2j+1 to 2j+2 modulo k. Define t_D(j) similarly
between d_{2j+1} and d_{2j+2}. There are no outside positions on the
domino edges. Hence

    Σ_j t_C(j) = Σ_j t_D(j) = m−k, an odd integer.

Write c_j = t_C(j) mod 2 and e_j = t_D(j) mod 2. Both flag vectors have
odd Hamming weight. All assertions used below depend only on d, c and e,
not on the lengths or orderings of the outside positions. In particular,
arbitrarily long even additions to any gaps do not change the type.

The arc between successive listed K-positions has edge-length parity
1 at an even index and 1+c_j at odd index 2j+1 on C; on D use e_j.
All parity sums below are modulo 2.

## 2. The complementary 2-factor

Let μ_C pair 2j+1 with 2j+2 modulo k, assigning that edge weight c_j.
Let μ_D pair d_{2j+1} with d_{2j+2}, with weight e_j. Their union U is a
2-regular multigraph on K; two parallel edges form a valid component.

**Parity lemma.** F = G−N is an even 2-factor if and only if the sum of
edge weights on every component of U is even.

**Proof.** F contains all spokes in K and no spokes outside K. Its
remaining edges are the C- and D-paths represented by the μ edges.
Suppressing the outside vertices and contracting the K-spokes gives U,
with one F-cycle for each U-component. A component on h vertices has h
μ edges. Lifting it uses h spokes and paths of total length
h + Σ t. Its cycle length is 2h + Σ t, whose parity is the component's
weight sum. ∎

If F is even, alternate two colours along each F-cycle. Their edge sets
A and B are perfect matchings, disjoint from N, and

    N, N, A, A, B, B

is the required cover. Thus only a non-even F needs the next lemma.

## 3. The finite boundary lemma

For a nonempty subset S ⊆ K, call S *good* in an order if every cyclic
arc between consecutive S-positions has odd edge-length according to
the parity data above. This includes the full-cycle arc for a singleton.
Since the full cycle has odd length, a good set has odd cardinality.

**Boundary lemma.** For k ∈ {4,6,8,10}, for every permutation d with
d_0=0 for which α_C ∪ α_D is connected, and for every pair of odd-weight
flag vectors c,e, at least one of the following holds:

1. Every component of U has even weight.
2. K partitions into four nonempty sets, each good in both orders.

This is a finite statement. Its exhaustive certificate, generation and
independent replay are specified in Section 5. No graph sampling or
assumption on graph order is used to establish it.

For k=2 the lemma is unnecessary: both flag vectors are (1), U consists
of two parallel edges with even total weight, and Section 2 applies.

## 4. Lifting a four-partition to six matchings

Suppose the second conclusion supplies S_1,…,S_4. Set S_0 = V\K.
The set S_0 is nonempty and good in both original cycles: the positions
between consecutive S_0-positions form an even run of K, so their
connecting arc has odd length. Section 1 shows that S_1,…,S_4 are good
in the original cycles as well, for every actual choice of outside gaps.

For i=0,…,4, define P_i to use the spokes at S_i and the unique perfect
matching of each even path left after deleting S_i from C and D.
Thus every P_i is a perfect matching. In particular P_0=N.

Every spoke occurs once among P_0,…,P_4. Consider the number a_j of these
five matchings using the j-th edge of C. At each vertex exactly one P_i
uses its spoke and four use a cycle edge. Therefore

    a_{j−1} + a_j = 4  for every j modulo m.

Because m is odd, alternating these equations around C forces a_j=2
for every j. The same argument applies to D. It follows that

    M, P_0, P_1, P_2, P_3, P_4

covers every spoke twice and every cycle edge twice. This proves C20
from the boundary lemma. If G is class 2, the even-factor alternative
cannot occur, proving the stated strengthening. ∎

## 5. Exhaustiveness, certificate and replay

The only symmetry reduction is cyclic rotation of the n C-dominoes.
Relabel by a rotation through an even number of K-positions, choosing
c's smallest binary value under cyclic rotation. Then restart and,
if necessary, reverse the D-order so that its first vertex is 0 and
its next vertex is 0's α_D-partner. This preserves all hypotheses,
U-component parities and the existence of a common good partition.
All D-orders and all odd D-flag vectors are still enumerated.

The C-flag representatives, with bit j representing c_j, are:

| k | Representatives | Number of odd D-flags |
|---|---|---:|
| 4 | 1 | 2 |
| 6 | 1, 7 | 4 |
| 8 | 1, 7 | 8 |
| 10 | 1, 7, 11, 31 | 16 |

Both programs enumerate all (k−1)! permutations with d_0=0 exactly once,
retaining those with connected α_C ∪ α_D. Their number is

    [2^(n−1) (n−1)!]^2.

Indeed, the α_D-matchings whose union with α_C is connected are counted
by fixing the first directed α_C edge, then ordering and orienting the
remaining n−1 α_C-dominoes around the alternating circuit. This gives
2^(n−1)(n−1)! choices. For each resulting α_D, its pairs may be ordered
and oriented in d in that many ways with the pair containing 0 fixed
first and 0 fixed first within that pair. Both programs assert the
resulting order counts and the total number of flag cases.

`exhaustive_local.cpp` checks component parities by disjoint-set union.
For every non-even state it searches the complete list of possible
four-partition sizes:

| k | Size patterns |
|---|---|
| 4 | 1+1+1+1 |
| 6 | 3+1+1+1 |
| 8 | 5+1+1+1; 3+3+1+1 |
| 10 | 7+1+1+1; 5+3+1+1; 3+3+3+1 |

Good subsets are generated using prefix parities. Each local good-set
table is cross-checked by direct cyclic-arc traversal; every returned
partition is also checked by traversal. A failure stops with a printed
type and exit code 2. A positive non-even state writes its four masks,
each as an unsigned 16-bit little-endian integer. Even states write no
record. The certificate follows increasing k, lexicographic d, increasing
C representative, then increasing D flag. It is stored as
`partitions.bin.gz`.

`replay_certificate.cpp` contains no partition search. It uses a graph
traversal to test α-connectivity, alternately walks μ edges to check
component parity, and verifies each supplied class by summing the
lengths of its cyclic arcs. It checks disjointness and full union for
every partition and requires exact certificate EOF. The mathematical
symmetry argument above, rather than program output, justifies omitting
the other C-flags.

The generation and replay counts agree exactly:

| k | Connected D-orders | Normalized states | Even factor | Certified partition |
|---|---:|---:|---:|---:|
| 4 | 4 | 8 | 7 | 1 |
| 6 | 64 | 512 | 392 | 120 |
| 8 | 2,304 | 36,864 | 25,896 | 10,968 |
| 10 | 147,456 | 9,437,184 | 6,234,704 | 3,202,480 |
| Total | | 9,474,568 | 6,260,999 | 3,213,569 |

The uncompressed certificate has exactly 3,213,569 × 8 = 25,708,552 bytes.
Both jobs returned rc=0, with complete success lines. Generation took
1.83 seconds and replay 2.01 seconds on AWS c7a.large. All computation
ran remotely, with assertions enabled. SHA256SUMS binds the retained
sources, certificate and logs. This is a computer-assisted proof;
the final cover-lifting implications are now formalized in `C20.lean`. The
finite reduction and boundary lemma are not Lean-formalized; no independent
human or peer review is claimed. See `FORMALIZATION.md` for the precise scope.

As a separate consistency test, `verify_physical_lifts.py` inflated 2,000
types into actual graphs, adding arbitrary even gap lengths and using
independent permutations of outside positions on C and D. It constructed
six perfect matchings in every graph and directly checked every vertex
degree and every edge's multiplicity. The graphs had up to 70 vertices.
This test checks implementation consistency; the unbounded lifting
argument is the proof in Sections 1, 2 and 4.

Self-contained reproduction is provided by `./verify.sh`. It uses only a
C++17 compiler and Python 3.9 or later, keeps assertions enabled, regenerates
all cases, compares the raw certificate against the banked bytes, replays
every record, and checks the physical lifts. The original job infrastructure
and research repository are unnecessary. The text-only gist can regenerate
the omitted binary certificate and verify its published raw SHA-256:

    51fe93dad24911b568121b928fb14c308ceccd3c1af337ddf50576b0c8322fc8

Lean's bundled standard library suffices to check the formal component.
Run `lake build` and `lake env lean C20.lean` with the pinned toolchain.

## 6. Exact contribution and remaining gap

Theorem C20 adds the alternating-circuit length-20 case to the currently
recorded sufficient condition of length 16. It also proves that in a
class-2 graph every single-circuit kernel of size at most 10 splits into
four common-good odd sets. In particular every six-element kernel in a
class-2 graph contains a common-good triple: if it were not a single
circuit, a size-two circuit would occur, forcing the even-factor case.
Thus no separate splittability hypothesis is needed in the class-2
six-kernel setting.

No bounded-order graph census is being promoted to an unbounded theorem:
the finite boundary reduction was proved before the exhaustive step,
and its lifting works for arbitrary outside size and arrangement.

The full cycle-permutation case remains open in this session. It would
suffice, for example, to prove every class-2 graph in the class has an
M-alternating circuit of length at most 20. That assertion is not proved
here. The universal short-circuit bound and the full Berge–Fulkerson conjecture
remain open; neither is established by this package.
