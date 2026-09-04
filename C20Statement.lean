import C20Gaps

/-!+# The exact publication target

This file defines the full graph theorem, rather than a conditional
lifting theorem. There is intentionally no claim that it is proved yet.
The public research release does not claim its end-to-end verification is complete.

The graph has vertices (outer,v) and (inner,v), with a spoke between the
two copies of v and the cycle edges given by c and d. Connected successor
cycles on Fin m, with m >= 3, are precisely two simple m-cycles.
-/

namespace C20

def cyclicNext {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (by have h := i.isLt; omega)⟩

def Adjacent {V : Type} (c : Cycle V) (u v : V) : Prop :=
  c.next u = v ∨ c.next v = u

/-- A simple spoke-alternating circuit: the k spoke positions are
distinct, and intervening cycle edges alternate outer/inner. The graph
circuit has 2*k edges. Reversing or restarting the circuit allows its
first cycle edge to be outer. -/
structure ShortCircuit {V : Type} (c d : Cycle V) where
  size : Nat
  min_two : 2 ≤ size
  even : size % 2 = 0
  length_le_twenty : 2 * size ≤ 20
  vertex : Fin size → V
  injective : ∀ i j, vertex i = vertex j → i = j
  outer_step : ∀ i, i.val % 2 = 0 → Adjacent c (vertex i) (vertex (cyclicNext i))
  inner_step : ∀ i, i.val % 2 = 1 → Adjacent d (vertex i) (vertex (cyclicNext i))

/-- Full C20: no supplied boundary type, partition, distance witness,
perfect matching, or finite computation appears among the hypotheses. -/
def C20Statement : Prop :=
  ∀ m : Nat, 3 ≤ m → ∀ c d : Cycle (Fin m),
    ConnectedCycle c → ConnectedCycle d → ShortCircuit c d →
    ∃ cover : Six (Fin m), DoubleCover c d cover

end C20
