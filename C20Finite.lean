import BoundarySearch

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace C20.Boundary

/-- Smallest boundary case, evaluated and checked by the Lean kernel. -/
theorem allBoundaryStates_four : allBoundaryStates 4 = true := by decide +kernel

/-- The six-spoke case, also checked by kernel reduction. -/
theorem allBoundaryStates_six : allBoundaryStates 6 = true := by decide +kernel

theorem boundary_four (tail : List Nat) (cf df : Nat)
    (hperm : tail.Perm [1, 2, 3])
    (hc : cf ∈ oddFlags 4) (hd : df ∈ oddFlags 4)
    (connected : connectedDominoes 4 (0 :: tail) = true) :
    Conclusion ⟨4, 0 :: tail, cf, df⟩ := by
  apply allBoundaryStates_sound 4 tail cf df _ hc hd connected allBoundaryStates_four
  exact hperm

end C20.Boundary

#print axioms C20.Boundary.boundary_four
#print axioms C20.Boundary.allBoundaryStates_six
