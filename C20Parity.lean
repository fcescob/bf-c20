import C20Encoding
import C20ParityFinite
import C20Three

namespace C20

theorem exists_gapFlags {k : Nat} (gap : Fin k → Bool)
    (even : ∀ i, i.val % 2 = 0 → gap i = false) :
    ∃ flags : Nat, flags < 2 ^ (k / 2) ∧ ∀ i, gap i = Boundary.gapBit flags i.val := by
  let f : Fin (k / 2) → Bool := fun j => gap ⟨2 * j.val + 1, by have h := j.isLt; omega⟩
  refine ⟨encodeBits f, encodeBits_lt f, ?_⟩
  intro i
  by_cases hi : i.val % 2 = 0
  · simp [Boundary.gapBit, hi, even i hi]
  · have hj : i.val / 2 < k / 2 := by have h := i.isLt; omega
    have he : gap i = f ⟨i.val / 2, hj⟩ := by
      dsimp only [f]
      congr 1
      apply Fin.ext
      omega
    rw [he, ← encodeBits_testBit f ⟨i.val / 2, hj⟩]
    simp [Boundary.gapBit, hi]

theorem orderLabels_self {W : Type} {k : Nat} (coords : Fin k ≃ W) :
    orderLabels coords coords.symm = List.range k := by
  simp only [orderLabels, Equiv.symm_apply_apply, List.ofFn_val]

theorem oddCycle_no_empty_matching {V : Type} (c : Cycle V) (odd : OddCycle c)
    (root : V) (edge : V → Bool)
    (incidence : ∀ v, bit (edge (c.prev v)) + bit (edge v) = 1) : False := by
  rcases odd with ⟨r, hr⟩
  have h := odd_recurrence_two c.next (fun v => 2 * bit (edge v)) r hr (fun v => by
    have hi := incidence (c.next v)
    simp only [c.prev_next] at hi
    change 2 * bit (edge v) + 2 * bit (edge (c.next v)) = 2
    omega)
  have hroot := h root
  change 2 * bit (edge root) = 1 at hroot
  omega

/-- Odd physical cycles force odd gap flags. This uses a small
kernel-checked parity certificate, avoiding an unproved gap-length sum. -/
theorem compressed_flags_odd {m k : Nat} (c : Cycle (Fin m)) (s : Fin m → Bool)
    (cc : ConnectedCycle c) (nonempty : ∃ v, s v = true)
    [Nontrivial {v // s v = true}] (odd : OddCycle c) (hk : k ∈ [2, 4, 6, 8, 10])
    (root : {v // s v = true}) (coords : Fin k ≃ {v // s v = true})
    (next : ∀ i, coords (cyclicNext i) = (compressedCycle c s cc nonempty).next (coords i))
    (flags : Nat) (bound : flags < 2 ^ (k / 2))
    (gaps : ∀ i, compressedGap c s cc nonempty (coords i) = Boundary.gapBit flags i.val) :
    flags ∈ Boundary.oddFlags k := by
  by_contra wrong
  have row := Boundary.wrongParity_matching k hk flags bound wrong
  rw [← orderLabels_self coords] at row
  have boundary := rowMatching_transfer (compressedCycle c s cc nonempty)
    (compressedGap c s cc nonempty) coords coords.symm next flags 0
    (Boundary.emptyCycleEdges k flags) gaps row
  let edge := fun w => Boundary.selected (Boundary.emptyCycleEdges k flags) (coords.symm w).val
  let x := compressionExpansion c s cc nonempty
  have lifted := expanded_incidence x (fun _ => false) edge (fun w => by
    simpa only [Boundary.selected, Nat.zero_testBit, bit] using boundary w)
  apply oddCycle_no_empty_matching c odd root.val (expandedEdges x edge)
  intro v
  have h := lifted v
  simpa [expandedSelected, bit] using h

/-- Complete flags and gap dictionary for one oriented physical cycle. -/
theorem normalize_cycle {m : Nat} (hm : 3 ≤ m) {c : Cycle (Fin m)}
    {s : Fin m → Bool} (dom : KernelDomino c s) (cc : ConnectedCycle c)
    (nonempty : ∃ v, s v = true) [Nontrivial {v // s v = true}]
    (odd : OddCycle c) (root : {v // s v = true}) (hr : dom.out root = true)
    (k : Nat) (card : Fintype.card {v // s v = true} = k) (hk : k ∈ [2, 4, 6, 8, 10]) :
    let coords := cycleCoordinates (compressedCycle c s cc nonempty)
      (compressedCycle_connected c s cc nonempty) root k card
    ∃ flags : Nat, flags ∈ Boundary.oddFlags k ∧
      ∀ i, compressedGap c s cc nonempty (coords i) = Boundary.gapBit flags i.val := by
  let coords := cycleCoordinates (compressedCycle c s cc nonempty)
    (compressedCycle_connected c s cc nonempty) root k card
  have even : ∀ i : Fin k, i.val % 2 = 0 → compressedGap c s cc nonempty (coords i) = false := by
    intro i hi
    have h := coordinate_even_gap hm dom cc nonempty root hr k card i hi
    change parityBit (firstDistance c s cc nonempty (c.next (coords i).val)) = false
    rw [h]
    rfl
  rcases exists_gapFlags (fun i => compressedGap c s cc nonempty (coords i)) even with ⟨flags, bound, gaps⟩
  refine ⟨flags, ?_, gaps⟩
  exact compressed_flags_odd c s cc nonempty odd hk root coords
    (cycleCoordinates_next _ _ _ _ _) flags bound gaps

end C20

#print axioms C20.normalize_cycle
