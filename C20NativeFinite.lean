import C20Finite

/-! Experimental finite closure using Lean's native evaluator.

IMPORTANT: `native_decide` trusts Lean.ofReduceBool, the Lean compiler,
and native implementations of core data operations. This is a larger
trust boundary than the kernel-only theorem in C20Finite.lean.
This file is separate from the default build and does not establish the
full graph theorem or open the publication gate.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace C20.Boundary

theorem allBoundaryStates_two : allBoundaryStates 2 = true := by decide +kernel

theorem allBoundaryStates_six_native : allBoundaryStates 6 = true := by native_decide
theorem allBoundaryStates_eight_native : allBoundaryStates 8 = true := by native_decide
theorem allBoundaryStates_ten_native : allBoundaryStates 10 = true := by native_decide

/-- Full finite dichotomy; its native-evaluation dependency is explicit. -/
theorem boundary_up_to_ten_native (k : Nat) (hk : k ∈ [2, 4, 6, 8, 10])
    (tail : List Nat) (cf df : Nat)
    (hperm : tail.Perm ((List.range (k - 1)).map (· + 1)))
    (hc : cf ∈ oddFlags k) (hd : df ∈ oddFlags k)
    (connected : connectedDominoes k (0 :: tail) = true) :
    Conclusion ⟨k, 0 :: tail, cf, df⟩ := by
  apply allBoundaryStates_sound k tail cf df hperm hc hd connected
  simp at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact allBoundaryStates_two
  · exact allBoundaryStates_four
  · exact allBoundaryStates_six_native
  · exact allBoundaryStates_eight_native
  · exact allBoundaryStates_ten_native

end C20.Boundary

#print axioms C20.Boundary.allBoundaryStates_two
#print axioms C20.Boundary.boundary_up_to_ten_native
