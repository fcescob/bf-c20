# Berge–Fulkerson C(20): six perfect matchings from a short alternating circuit

**Complete Lean proof of the C(20) double-cover theorem.**

[`C20.c20`](C20Theorem.lean) passed
[end-to-end verification](https://github.com/fcescob/bf-c20/actions/runs/33924229219)
on 4 September 2026 at 22:12 UTC. The proof has no `sorry` or
user-supplied axiom. The finite computation uses Lean's native evaluator;
its additional compiler trust is explicit below and in
[FORMALIZATION.md](FORMALIZATION.md).

**Computer-assisted theorem · 4 September 2026**

Let a graph consist of two disjoint cycles of the same length, together
with a perfect matching **M** between them. If it has an **M-alternating
circuit of length at most 20**, it has six perfect matchings in which
**every edge occurs exactly twice**. The two cycles can be arbitrarily long.

The written proof also shows that for a class-2 graph (one with no proper
three-edge-colouring), the construction includes both M and M △ E(Q),
where Q is the given circuit. This additional specification of two
distinguished members is not a separate target of the current Lean proof.
Repeated perfect matchings are allowed in a cover.

This repository is a self-contained proof package. Read [PROOF.md](PROOF.md)
for all definitions, the finite reduction, the symmetry argument, and the
unbounded lifting proof. The result does **not** establish that every
cycle-permutation graph has such a short circuit, or prove the full
Berge–Fulkerson conjecture.

## Evidence and formalization scope

| Part | Evidence in this package |
|---|---|
| Actual graph → finite matching boundary theorem → six-matching cover | Lean theorem `C20.c20_from_finite`, including normalization, parity, indexing, and arbitrary path lengths |
| Finite dichotomy for k = 4, 6, 8, 10 | All 9,474,568 normalized states checked; 3,213,569 partition certificates replayed by the original C++ package |
| Direct finite matching certificates for the Lean graph reduction | Checker soundness and all constants k=2,4,6,8,10 proved in Lean |
| Even cycle lengths | Complete Lean proof `C20.even_order_cover` |
| Actual graph implementation | 2,000 deterministic physical graph checks; supplementary tests |

The complete theorem has the original graph hypotheses only: two connected
simple cycles and a short alternating circuit. All compression,
normalization, finite enumeration, and lifting obligations are discharged.
The [finite proof run](https://github.com/fcescob/bf-c20/actions/runs/33924043380)
proved every size-10 shard, and the
[combined check](https://github.com/fcescob/bf-c20/actions/runs/33924229219)
proved `C20.c20`. Its exact axiom audit is retained in
[lean-full-axioms.log](lean-full-axioms.log).

## Reproduce

Requirements: a C++17 compiler, Python 3.9+, Bash; Lean is separate.
No mathematical library, solver, private repository, AWS account or
original research environment is needed.

```sh
git clone https://github.com/fcescob/bf-c20.git
cd bf-c20
./verify.sh
```

This regenerates every finite case, compares the certificate byte for
byte, independently replays it, and checks the 2,000 physical lifts.
Assertions are explicitly enabled. `out/` holds generated files.
The repository includes the 3.6 MiB compressed certificate. A text-only
copy regenerates the certificate itself
and checks its published SHA-256.

For certificate replay alone:

```sh
mkdir -p out
gzip -dc partitions.bin.gz > out/partitions.bin
c++ -std=c++17 -O2 -UNDEBUG replay_certificate.cpp -o out/replay
./out/replay
```

For the checked graph reduction, with
[elan](https://github.com/leanprover/elan) installed:

```sh
lake build
lake env lean C20Assemble.lean
```

To reproduce the complete Lean proof, including the finite computation:

```sh
lake build C20Theorem
lake env lean C20Theorem.lean
```

Lean **4.28.0** and Mathlib **4.28.0** are pinned. The default build checks
the whole unbounded deduction and excludes native finite computations.
The finite proof uses `native_decide`, whose additional trust includes
`Lean.ofReduceBool`, `Lean.trustCompiler`, and Lean's native compiler and
core implementations. No C++ result is imported into Lean.

The [GitHub Actions workflows](https://github.com/fcescob/bf-c20/actions)
run the checks remotely. The complete theorem workflow also checks that
reused finite proof artifacts come from exactly the same checker sources.
The default build checks the graph reduction quickly. `lake build
C20Theorem` also recomputes all finite proofs and can take substantially
longer. The remote finite workflow splits size 10 into nine nonempty
batches (plus an empty head-0 case); the measured head-1 proof took
5 minutes 34 seconds with native libraries loaded.

## Original certificate census

| Spokes k on Q | Connected D-orders | States | Even complement | Four-class certificate |
|---|---:|---:|---:|---:|
| 4 | 4 | 8 | 7 | 1 |
| 6 | 64 | 512 | 392 | 120 |
| 8 | 2,304 | 36,864 | 25,896 | 10,968 |
| 10 | 147,456 | 9,437,184 | 6,234,704 | 3,202,480 |
| **Total** | | **9,474,568** | **6,260,999** | **3,213,569** |

The k = 2 case is proved directly in the note and by kernel reduction in
Lean. Even cycle lengths are handled by an explicit three-edge-colouring.
The Lean finite theorem proves a stronger enumeration without the C-flag
rotation reduction or the domino-connectivity filter: its size-10 case
covers 9! × 16 × 16 = 92,897,280 states.

## Files and provenance

- [PROOF.md](PROOF.md): complete written proof and certificate format.
- [C20Theorem.lean](C20Theorem.lean): the complete formal theorem.
- [FORMALIZATION.md](FORMALIZATION.md): definitions, proof structure, reproduction, and trust boundary.
- [exhaustive_local.cpp](exhaustive_local.cpp): enumeration and certificate generation.
- [replay_certificate.cpp](replay_certificate.cpp): independent checking algorithm with no partition search.
- `partitions.bin.gz`: every non-even state's four classes, in the specified order.
- `exhaustive.log`, `replay.log`, `physical_lifts.log`: retained original successful remote outputs.
- `verify_physical_lifts.py`, `verify_local_construction.py`: deterministic implementation consistency tests.
- `SHA256SUMS`: hashes of the distributed proof artifacts.

Original enumeration and replay ran separately on AWS on 4 September
2026. Their algorithms differ, but both were written by the same coding
agent; this is not an independent human audit. This package and its Lean
component were prepared with OpenAI Codex. No peer review is claimed.

The published length-16 sufficient condition appears in Luo, Hao, Luo,
Zhang and Zhou, *Berge–Fulkerson Conjecture, Perfect Matching Partial
Coverings and Odd Dividers*, JGT (2026),
[doi:10.1002/jgt.70097](https://doi.org/10.1002/jgt.70097).
That comparison was checked against the publisher's abstract. This
proof does not depend on that theorem. No exhaustive priority search is
claimed.
