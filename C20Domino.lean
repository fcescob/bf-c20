import C20Kernel

namespace C20

/-- A fixed-point-free pairing of selected positions along actual cycle edges. -/
structure Domino {V W : Type} (c : Cycle V) (vertex : W → V) where
  mate : W → W
  involutive : Function.Involutive mate
  adjacent : ∀ i, Adjacent c (vertex i) (vertex (mate i))

noncomputable def dominoEdges {V W : Type} {c : Cycle V} {vertex : W → V}
    (dom : Domino c vertex) (v : V) : Bool := by
  classical
  exact decide (∃ i, vertex i = v ∧ vertex (dom.mate i) = c.next v)

/-- A pairing along cycle edges has exactly one incident edge at every
selected vertex, and none at any other vertex. -/
theorem domino_incidence {m : Nat} (hm : 3 ≤ m) (c : Cycle (Fin m))
    (connected : ConnectedCycle c) {W : Type} [Fintype W] (vertex : W → Fin m)
    (inj : Function.Injective vertex) (dom : Domino c vertex) :
    ∀ v, bit (decide (¬ ∃ i, vertex i = v)) +
      bit (dominoEdges dom (c.prev v)) + bit (dominoEdges dom v) = 1 := by
  classical
  intro v
  by_cases hv : ∃ i, vertex i = v
  · rcases hv with ⟨i, rfl⟩
    have hout : (∃ j, vertex j = vertex i ∧ vertex (dom.mate j) = c.next (vertex i)) ↔
        vertex (dom.mate i) = c.next (vertex i) := by
      constructor
      · rintro ⟨j, hj, he⟩
        have hji := inj hj
        simpa only [hji] using he
      · intro h; exact ⟨i, rfl, h⟩
    have hin : (∃ j, vertex j = c.prev (vertex i) ∧
        vertex (dom.mate j) = c.next (c.prev (vertex i))) ↔
        vertex (dom.mate i) = c.prev (vertex i) := by
      constructor
      · rintro ⟨j, hj, he⟩
        rw [c.next_prev] at he
        have hji : j = dom.mate i := by
          have h := congrArg dom.mate (inj he)
          exact (dom.involutive j).symm.trans h
        simpa only [hji] using hj
      · intro h
        exact ⟨dom.mate i, h, by rw [dom.involutive, c.next_prev]⟩
    have ha : vertex (dom.mate i) = c.next (vertex i) ∨
        vertex (dom.mate i) = c.prev (vertex i) := by
      rcases dom.adjacent i with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by simpa only [c.prev_next] using congrArg c.prev h)
    have hn := cycle_neighbors_distinct hm c connected (vertex i)
    simp only [dominoEdges, hout, hin]
    have hsel : (∃ j, vertex j = vertex i) := ⟨i, rfl⟩
    simp only [hsel, not_true_eq_false, decide_false, bit]
    rcases ha with ha | ha
    · simp [ha, hn]
    · simp [ha, Ne.symm hn]
  · have hout : ¬ ∃ i, vertex i = v ∧ vertex (dom.mate i) = c.next v := by
      rintro ⟨i, hi, _⟩; exact hv ⟨i, hi⟩
    have hin : ¬ ∃ i, vertex i = c.prev v ∧
        vertex (dom.mate i) = c.next (c.prev v) := by
      rintro ⟨i, _, hi⟩
      exact hv ⟨dom.mate i, by simpa only [c.next_prev] using hi⟩
    simp [dominoEdges, hv, hout, hin, bit]

/-- Two actual domino matchings on the same selected positions produce
the switched spoke matching, using all spokes outside those positions. -/
theorem paired_kernel_matching {m : Nat} (hm : 3 ≤ m) (c d : Cycle (Fin m))
    (cc : ConnectedCycle c) (dc : ConnectedCycle d) {W : Type} [Fintype W]
    (vertex : W → Fin m) (inj : Function.Injective vertex)
    (outer : Domino c vertex) (inner : Domino d vertex) :
    ∃ p : EdgeSet (Fin m), PerfectMatching c d p ∧
      ∀ v, p.spoke v = decide (¬ ∃ i, vertex i = v) := by
  classical
  refine ⟨⟨fun v => decide (¬ ∃ i, vertex i = v), dominoEdges outer, dominoEdges inner⟩,
    ⟨domino_incidence hm c cc vertex inj outer,
      domino_incidence hm d dc vertex inj inner⟩, fun _ => rfl⟩

def outerPair {k : Nat} (he : k % 2 = 0) (i : Fin k) : Fin k :=
  if hi : i.val % 2 = 0 then ⟨i.val + 1, by have h := i.isLt; omega⟩
  else ⟨i.val - 1, by have h := i.isLt; omega⟩

theorem outerPair_val {k : Nat} (he : k % 2 = 0) (i : Fin k) :
    (outerPair he i).val = if i.val % 2 = 0 then i.val + 1 else i.val - 1 := by
  unfold outerPair
  split <;> rfl

theorem outerPair_involutive {k : Nat} (he : k % 2 = 0) :
    Function.Involutive (outerPair he) := by
  intro i
  apply Fin.ext
  simp only [outerPair_val]
  split_ifs <;> omega

theorem outerPair_adjacent {V : Type} {c d : Cycle V} (q : ShortCircuit c d) :
    ∀ i, Adjacent c (q.vertex i) (q.vertex (outerPair q.even i)) := by
  intro i
  by_cases hi : i.val % 2 = 0
  · have hp : outerPair q.even i = cyclicNext i := by
      apply Fin.ext
      simp only [outerPair, hi, ↓reduceDIte, cyclicNext]
      have hlt : i.val + 1 < q.size := by have h := i.isLt; have he := q.even; omega
      exact (Nat.mod_eq_of_lt hlt).symm
    rw [hp]
    exact q.outer_step i hi
  · let j := outerPair q.even i
    have hj : j.val % 2 = 0 := by simp only [j, outerPair, hi, ↓reduceDIte]; omega
    have hn : cyclicNext j = i := by
      apply Fin.ext
      simp only [cyclicNext, j, outerPair, hi, ↓reduceDIte]
      have hp : i.val - 1 + 1 = i.val := by omega
      rw [hp, Nat.mod_eq_of_lt i.isLt]
    have h := q.outer_step j hj
    rw [hn] at h
    exact h.elim Or.inr Or.inl

def outerDomino {V : Type} {c d : Cycle V} (q : ShortCircuit c d) : Domino c q.vertex :=
  ⟨outerPair q.even, outerPair_involutive q.even, outerPair_adjacent q⟩

theorem cyclicNext_val {k : Nat} (i : Fin k) :
    (cyclicNext i).val = if i.val + 1 < k then i.val + 1 else 0 := by
  simp only [cyclicNext]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hi : i.val + 1 = k := by have hlt := i.isLt; omega
    rw [hi, Nat.mod_self]

theorem cyclicNext_injective (k : Nat) : Function.Injective (@cyclicNext k) := by
  intro i j h
  have he := congrArg Fin.val h
  rw [cyclicNext_val, cyclicNext_val] at he
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  split_ifs at he <;> omega

noncomputable def cyclicPerm (k : Nat) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective cyclicNext
    ⟨cyclicNext_injective k, Finite.surjective_of_injective (cyclicNext_injective k)⟩

theorem cyclicNext_parity {k : Nat} (he : k % 2 = 0) (i : Fin k) :
    (cyclicNext i).val % 2 = 1 - i.val % 2 := by
  rw [cyclicNext_val]
  split_ifs <;> have hi := i.isLt <;> omega

/-- Restarting a circuit one spoke later exchanges its outer and inner roles. -/
noncomputable def rotateCircuit {V : Type} {c d : Cycle V} (q : ShortCircuit c d) :
    ShortCircuit d c where
  size := q.size
  min_two := q.min_two
  even := q.even
  length_le_twenty := q.length_le_twenty
  vertex i := q.vertex (cyclicNext i)
  injective i j h := cyclicNext_injective q.size (q.injective _ _ h)
  outer_step i hi := q.inner_step (cyclicNext i) (by rw [cyclicNext_parity q.even, hi])
  inner_step i hi := q.outer_step (cyclicNext i) (by rw [cyclicNext_parity q.even, hi])

noncomputable def innerDomino {V : Type} {c d : Cycle V} (q : ShortCircuit c d) :
    Domino d q.vertex := by
  let p := cyclicPerm q.size
  refine ⟨fun i => p (outerPair q.even (p.symm i)), ?_, ?_⟩
  · intro i
    simp only [p.symm_apply_apply, outerPair_involutive q.even (p.symm i), p.apply_symm_apply]
  · intro i
    have h := outerPair_adjacent (rotateCircuit q) (p.symm i)
    change Adjacent d (q.vertex (p (p.symm i)))
      (q.vertex (p (outerPair q.even (p.symm i)))) at h
    simpa only [p.apply_symm_apply] using h

/-- The short alternating circuit itself supplies the switched matching. -/
theorem circuit_switch_matching {m : Nat} (hm : 3 ≤ m) (c d : Cycle (Fin m))
    (cc : ConnectedCycle c) (dc : ConnectedCycle d) (q : ShortCircuit c d) :
    ∃ p : EdgeSet (Fin m), PerfectMatching c d p ∧
      ∀ v, p.spoke v = decide (v ∉ circuitKernel q) := by
  rcases paired_kernel_matching hm c d cc dc q.vertex q.injective
    (outerDomino q) (innerDomino q) with ⟨p, hp, hs⟩
  refine ⟨p, hp, ?_⟩
  intro v
  simpa only [mem_circuitKernel] using hs v

end C20

#print axioms C20.paired_kernel_matching
#print axioms C20.outerDomino
#print axioms C20.circuit_switch_matching
