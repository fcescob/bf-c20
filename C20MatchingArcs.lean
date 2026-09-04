import C20Domino
import C20Even

/-! The converse odd-arc lemma and the actual outside spoke class. -/

namespace C20

theorem firstHit_tail {V : Type} (f : V → V) (s : V → Bool) (v : V) (n : Nat)
    (h : FirstHit f s v (n + 1)) : FirstHit f s (f v) n := by
  constructor
  · simpa only [walk_succ_start] using h.1
  · intro i hi
    simpa only [walk_succ_start] using h.2 (i + 1) (by omega)

theorem incidence_selected_edge_false {V : Type} (c : Cycle V) (s edge : V → Bool)
    (incidence : ∀ v, bit (s v) + bit (edge (c.prev v)) + bit (edge v) = 1)
    (v : V) (hv : s v = true) : edge v = false := by
  have h := incidence v
  rw [hv] at h
  cases he : edge v <;> simp_all [bit]

/-- The incoming edge at distance n from the next selected spoke has
exactly the parity of n. This also checks the endpoint n=0. -/
theorem matching_firstHit_parity {V : Type} (c : Cycle V) (s edge : V → Bool)
    (incidence : ∀ v, bit (s v) + bit (edge (c.prev v)) + bit (edge v) = 1) :
    ∀ n v, FirstHit c.next s v n → edge (c.prev v) = parityBit n := by
  intro n
  induction n with
  | zero =>
    intro v hn
    have hs : s v = true := hn.1
    have h := incidence v
    rw [hs] at h
    cases he : edge (c.prev v) <;> simp_all [bit, parityBit]
  | succ n ih =>
    intro v hn
    have hs : s v = false := hn.2 0 (by omega)
    have hnext : edge v = parityBit n := by
      simpa only [c.prev_next] using ih (c.next v) (firstHit_tail c.next s v n hn)
    have h := incidence v
    rw [hs] at h
    have he : edge (c.prev v) = !(edge v) := by
      cases hp : edge (c.prev v) <;> cases hq : edge v <;> simp_all [bit]
    rw [he, hnext, parityBit_succ]

/-- Every perfect matching's nonempty spoke class has odd successive arcs. -/
theorem matching_oddArcs {V : Type} (c : Cycle V) (s edge : V → Bool)
    (incidence : ∀ v, bit (s v) + bit (edge (c.prev v)) + bit (edge v) = 1) :
    OddArcs c s := by
  intro v hv n hn
  have he := incidence_selected_edge_false c s edge incidence v hv
  have hh := matching_firstHit_parity c s edge incidence n (c.next v) hn
  simp only [c.prev_next, he] at hh
  have hp : n % 2 ≠ 1 := by
    intro hp
    simp [parityBit, hp] at hh
  omega

def matchingCommonGood {V : Type} (c d : Cycle V) (p : EdgeSet V)
    (hp : PerfectMatching c d p) (nonempty : ∃ v, p.spoke v = true) : CommonGood c d :=
  ⟨p.spoke, nonempty, matching_oddArcs c _ _ hp.1, matching_oddArcs d _ _ hp.2⟩

/-- The outside class is common-good, derived from the actual circuit.
It is nonempty because m is odd whereas the circuit uses an even number
of distinct spoke positions. -/
theorem circuit_outside_commonGood {m : Nat} (hm : 3 ≤ m) (odd : m % 2 = 1)
    (c d : Cycle (Fin m)) (cc : ConnectedCycle c) (dc : ConnectedCycle d)
    (q : ShortCircuit c d) :
    ∃ outside : CommonGood c d, ∀ v, outside.selected v = decide (v ∉ circuitKernel q) := by
  rcases circuit_switch_matching hm c d cc dc q with ⟨p, hp, hs⟩
  rcases circuitKernel_proper odd q with ⟨v, hv⟩
  have hnonempty : ∃ v, p.spoke v = true := ⟨v, by rw [hs v]; simp [hv]⟩
  exact ⟨matchingCommonGood c d p hp hnonempty, hs⟩

end C20

#print axioms C20.matching_oddArcs
#print axioms C20.circuit_outside_commonGood
