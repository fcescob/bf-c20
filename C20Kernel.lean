import C20Cycles

namespace C20

def circuitKernel {m : Nat} {c d : Cycle (Fin m)} (q : ShortCircuit c d) : Finset (Fin m) :=
  Finset.univ.image q.vertex

theorem mem_circuitKernel {m : Nat} {c d : Cycle (Fin m)} (q : ShortCircuit c d)
    (v : Fin m) : v ∈ circuitKernel q ↔ ∃ i, q.vertex i = v := by
  simp [circuitKernel]

theorem card_circuitKernel {m : Nat} {c d : Cycle (Fin m)} (q : ShortCircuit c d) :
    (circuitKernel q).card = q.size := by
  rw [circuitKernel, Finset.card_image_of_injective _ q.injective]
  simp

theorem circuitKernel_nonempty {m : Nat} {c d : Cycle (Fin m)} (q : ShortCircuit c d) :
    (circuitKernel q).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_circuitKernel]
  have h := q.min_two
  omega

/-- In the odd-cycle branch there is an outside position. -/
theorem circuitKernel_proper {m : Nat} (hm : m % 2 = 1) {c d : Cycle (Fin m)}
    (q : ShortCircuit c d) : ∃ v, v ∉ circuitKernel q := by
  by_contra h
  push_neg at h
  have he : circuitKernel q = Finset.univ := by
    ext v
    simp [h v]
  have hc : q.size = m := by
    rw [← card_circuitKernel q, he]
    simp
  have hq := q.even
  omega

/-- Extract a duplicate-free cyclic list of the kernel from either cycle.
The subsequent reduction must still prove its domino and gap properties. -/
theorem exists_kernel_list {m : Nat} (hm : 0 < m) {c d : Cycle (Fin m)}
    (q : ShortCircuit c d) (cycle : Cycle (Fin m)) (connected : ConnectedCycle cycle) :
    ∃ full kernel : List (Fin m), full.Nodup ∧ full.length = m ∧
      full.formPerm = cycle.toPerm ∧
      kernel = full.filter (fun v => decide (v ∈ circuitKernel q)) ∧
      kernel.Nodup ∧ kernel.length = q.size ∧
      (∀ v, v ∈ kernel ↔ v ∈ circuitKernel q) := by
  rcases exists_cycle_list hm cycle connected with ⟨full, hnd, hlen, hall, hperm⟩
  let kernel := full.filter (fun v => decide (v ∈ circuitKernel q))
  have hkn : kernel.Nodup := hnd.filter _
  have hmem : ∀ v, v ∈ kernel ↔ v ∈ circuitKernel q := by
    intro v
    simp [kernel, hall v]
  have hset : kernel.toFinset = circuitKernel q := by
    ext v
    simpa using hmem v
  have hkl : kernel.length = q.size := by
    rw [← List.toFinset_card_of_nodup hkn, hset, card_circuitKernel]
  exact ⟨full, kernel, hnd, hlen, hperm, rfl, hkn, hkl, hmem⟩

end C20

#print axioms C20.circuitKernel_proper
#print axioms C20.exists_kernel_list
