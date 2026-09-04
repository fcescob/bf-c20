import C20BoundaryMatching

namespace C20.Boundary

/-- An attempted matching with no spokes, used only to exclude the
wrong gap parity. Every proposed edge mask is checked literally. -/
def emptyCycleEdges (k flags : Nat) : Nat := Id.run do
  let mut edge := false
  let mut mask := 0
  for i in List.range (k - 1) do
    edge := !(edge.xor (gapBit flags i))
    if edge then mask := mask ||| (1 <<< (i + 1))
  return mask

def wrongParityCheck (k : Nat) : Bool :=
  (List.range (2 ^ (k / 2))).all fun flags =>
    if flags ∈ oddFlags k then true
    else rowMatchingOK (List.range k) flags 0 (emptyCycleEdges k flags)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem wrongParity_two : wrongParityCheck 2 = true := by decide +kernel
theorem wrongParity_four : wrongParityCheck 4 = true := by decide +kernel
theorem wrongParity_six : wrongParityCheck 6 = true := by decide +kernel
theorem wrongParity_eight : wrongParityCheck 8 = true := by decide +kernel
theorem wrongParity_ten : wrongParityCheck 10 = true := by decide +kernel

/-- Wrong-parity flags force a forbidden empty-spoke cycle matching. -/
theorem wrongParity_matching (k : Nat) (hk : k ∈ [2, 4, 6, 8, 10]) (flags : Nat)
    (bound : flags < 2 ^ (k / 2)) (wrong : flags ∉ oddFlags k) :
    RowMatching (List.range k) flags 0 (emptyCycleEdges k flags) := by
  have hcheck : wrongParityCheck k = true := by
    simp only [List.mem_cons, List.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact wrongParity_two
    · exact wrongParity_four
    · exact wrongParity_six
    · exact wrongParity_eight
    · exact wrongParity_ten
  have h := List.all_eq_true.mp hcheck flags (by simpa using bound)
  simp only [wrong, ↓reduceIte] at h
  exact rowMatchingOK_sound _ _ _ _ h

end C20.Boundary

#print axioms C20.Boundary.wrongParity_matching
