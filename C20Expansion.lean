import C20

/-!+# Lifting boundary edge choices across arbitrary outside paths

A boundary vertex stands for an actual kernel vertex; a boundary edge
stands for a path in the original cycle. Only the parity of the number
of internal vertices matters. This file proves the local matching
extension, without bounding any path length.
-/

namespace C20

def parityBit (n : Nat) : Bool := decide (n % 2 = 1)

theorem parityBit_pred (n : Nat) (hn : 0 < n) :
    parityBit (n - 1) = !(parityBit n) := by
  unfold parityBit
  cases h : decide (n % 2 = 1) <;> simp_all <;> omega

theorem alternating_bits (a : Bool) (n : Nat) (hn : 0 < n) :
    bit (a.xor (parityBit n)) + bit (a.xor (parityBit (n - 1))) = 1 := by
  rw [parityBit_pred n hn]
  cases a <;> cases parityBit n <;> rfl

theorem starting_bit (a : Bool) (n : Nat) (hn : 0 < n) :
    bit a + bit ((a.xor (parityBit n)).xor (parityBit (n - 1))) = 1 := by
  rw [parityBit_pred n hn]
  cases a <;> cases parityBit n <;> rfl

/-- The exact first-hit compression interface for a cycle and its kernel.
`index v` is the next boundary vertex; `distance v` counts steps to it.
Distance zero marks the kernel. A boundary step starts the next gap.
The parity datum records the number of internal vertices of that gap. -/
structure Expansion {V W : Type} (c : Cycle V) (b : Cycle W) (gap : W → Bool) where
  index : V → W
  distance : V → Nat
  outside_step : ∀ v, distance v ≠ 0 →
    distance v = distance (c.next v) + 1 ∧ index v = index (c.next v)
  boundary_step : ∀ v, distance v = 0 → index (c.next v) = b.next (index v)
  boundary_parity : ∀ v, distance v = 0 → parityBit (distance (c.next v)) = gap (index v)

def boundaryIncoming {W : Type} (b : Cycle W) (gap edge : W → Bool) (w : W) : Bool :=
  (edge (b.prev w)).xor (gap (b.prev w))

def expandedSelected {V W : Type} {c : Cycle V} {b : Cycle W} {gap : W → Bool}
    (x : Expansion c b gap) (s : W → Bool) (v : V) : Bool :=
  decide (x.distance v = 0) && s (x.index v)

def expandedEdges {V W : Type} {c : Cycle V} {b : Cycle W} {gap : W → Bool}
    (x : Expansion c b gap) (edge : W → Bool) (v : V) : Bool :=
  if x.distance v = 0 then edge (x.index v)
  else (boundaryIncoming b gap edge (x.index v)).xor (parityBit (x.distance v - 1))

/-- Boundary matching incidence lifts along every gap of any length. -/
theorem expanded_incidence {V W : Type} {c : Cycle V} {b : Cycle W} {gap : W → Bool}
    (x : Expansion c b gap) (s edge : W → Bool)
    (boundary : ∀ w, bit (s w) + bit (boundaryIncoming b gap edge w) + bit (edge w) = 1) :
    ∀ v, bit (expandedSelected x s v) + bit (expandedEdges x edge (c.prev v)) +
      bit (expandedEdges x edge v) = 1 := by
  have forward : ∀ v, bit (expandedSelected x s (c.next v)) +
      bit (expandedEdges x edge v) + bit (expandedEdges x edge (c.next v)) = 1 := by
    intro v
    by_cases hv : x.distance v = 0
    · have hi := x.boundary_step v hv
      have hp := x.boundary_parity v hv
      by_cases hn : x.distance (c.next v) = 0
      · have hg : gap (x.index v) = false := by
          rw [hn] at hp
          exact hp.symm
        have h := boundary (x.index (c.next v))
        simpa [expandedSelected, expandedEdges, hn, hv, boundaryIncoming, hi,
          b.prev_next, hg, bit] using h
      · have h := starting_bit (edge (x.index v)) (x.distance (c.next v)) (by omega)
        simpa [expandedSelected, expandedEdges, hn, hv, hi, boundaryIncoming,
          b.prev_next, ← hp, bit] using h
    · have hs := x.outside_step v hv
      by_cases hn : x.distance (c.next v) = 0
      · have hv1 : x.distance v = 1 := by omega
        have h := boundary (x.index (c.next v))
        simpa [expandedSelected, expandedEdges, hn, hv1, hs.2, parityBit, bit] using h
      · have h := alternating_bits (boundaryIncoming b gap edge (x.index (c.next v)))
          (x.distance (c.next v)) (by omega)
        have hd : x.distance v - 1 = x.distance (c.next v) := by omega
        simpa [expandedSelected, expandedEdges, hn, hv, hs.2, hd, bit] using h
  intro v
  have h := forward (c.prev v)
  simpa only [c.next_prev] using h

end C20

#print axioms C20.expanded_incidence
