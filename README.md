# C20: six perfect matchings from a short alternating circuit

**Computer-assisted theorem · 4 September 2026**

Share this repository or the [standalone gist](https://gist.github.com/fcescob/59ce2639b82277aad07b7f337403f628).
Both contain everything needed to read and reproduce the result.

Let a graph consist of two disjoint cycles of the same length, together
with a perfect matching **M** between them. If it has an **M-alternating
circuit of length at most 20**, it has six perfect matchings in which
**every edge occurs exactly twice**. The two cycles can be arbitrarily long.

For a class-2 graph (one with no proper three-edge-colouring), the
construction includes both M and M △ E(Q), where Q is the given circuit.
Repeated perfect matchings are allowed in a cover.

This repository is a self-contained proof package. Read [PROOF.md](PROOF.md)
for all definitions, the finite reduction, the symmetry argument, and the
unbounded lifting proof. The result does **not** establish that every
cycle-permutation graph has such a short circuit, or prove the full
Berge–Fulkerson conjecture.

## Evidence and formalization scope

| Part | Evidence in this package |
|---|---|
| Graph → finite boundary type; symmetry normalization | Mathematical proofs in [PROOF.md](PROOF.md), §§1–3 and 5 |
| Finite dichotomy for k = 4, 6, 8, 10 | All 9,474,568 normalized states checked; 3,213,569 partition certificates replayed |
| Odd-gap distance witnesses for five classes → six explicit perfect matchings | Lean theorem `C20.good_partition_cover`; the distance witnesses are supplied by the written odd-gap construction |
| Five perfect matchings with partitioned spokes → six-edge double cover on two odd cycles | Kernel-checked Lean theorem `C20.five_matchings_cover` in [C20.lean](C20.lean) |
| Three perfect matchings partitioning the edges → doubled cover | Lean theorem `C20.tait_double_cover` |
| Actual graph implementation | 2,000 deterministic physical graph checks; supplementary tests, not the source of unbounded scope |

**This is a complete computer-assisted proof with a partial Lean
formalization, not an end-to-end Lean proof of C20.** The strongest Lean
theorem takes five spoke classes with odd-gap distance witnesses and
constructs all six perfect matchings. The boundary reduction and finite
C++ computation remain outside Lean. See [FORMALIZATION.md](FORMALIZATION.md)
for the exact interface and unformalized steps.

## Reproduce

Requirements: a C++17 compiler, Python 3.9+, Bash; Lean is separate.
No mathematical library, solver, private repository, AWS account or
original research environment is needed.

```sh
git clone https://github.com/fcescob/c20-cover.git
cd c20-cover
./verify.sh
```

This regenerates every finite case, compares the certificate byte for
byte, independently replays it, and checks the 2,000 physical lifts.
Assertions are explicitly enabled. `out/` holds generated files.
The repository includes the 3.6 MiB compressed certificate. A text-only
copy, such as the accompanying gist, regenerates the certificate itself
and checks its published SHA-256.

For certificate replay alone:

```sh
mkdir -p out
gzip -dc partitions.bin.gz > out/partitions.bin
c++ -std=c++17 -O2 -UNDEBUG replay_certificate.cpp -o out/replay
./out/replay
```

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake build
lake env lean C20.lean
```

Lean **4.28.0** is pinned in `lean-toolchain`; only its bundled `Std`
library is imported. The file also works by itself with that toolchain.
There are no added axioms, admitted obligations, or `native_decide` calls.
The file prints the axioms used by its principal theorems.

The [GitHub Actions workflow](https://github.com/fcescob/c20-cover/actions)
runs the proof and all finite checks on a remote runner.
The [initial complete verification](https://github.com/fcescob/c20-cover/actions/runs/33914852262)
passed the constructive Lean proof, exhaustive reproduction, certificate
replay, and text-only distribution path.

## Exact finite counts

| Spokes k on Q | Connected D-orders | States | Even complement | Four-class certificate |
|---|---:|---:|---:|---:|
| 4 | 4 | 8 | 7 | 1 |
| 6 | 64 | 512 | 392 | 120 |
| 8 | 2,304 | 36,864 | 25,896 | 10,968 |
| 10 | 147,456 | 9,437,184 | 6,234,704 | 3,202,480 |
| **Total** | | **9,474,568** | **6,260,999** | **3,213,569** |

The k = 2 case is proved directly in the note. Even cycle lengths are
handled by an explicit three-edge-colouring.

## Files and provenance

- [PROOF.md](PROOF.md): complete written proof and certificate format.
- [C20.lean](C20.lean), [FORMALIZATION.md](FORMALIZATION.md): checked formal component and its precise scope.
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
