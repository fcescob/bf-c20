import C20BoundaryMatching

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C20.Boundary

theorem matching_two : allMatchingStates 2 = true := by decide +kernel
theorem matching_four : allMatchingStates 4 = true := by decide +kernel
theorem matching_six_native : allMatchingStates 6 = true := by native_decide
theorem matching_eight_native : allMatchingStates 8 = true := by native_decide

end C20.Boundary

#print axioms C20.Boundary.matching_two
#print axioms C20.Boundary.matching_four
#print axioms C20.Boundary.matching_six_native
#print axioms C20.Boundary.matching_eight_native
