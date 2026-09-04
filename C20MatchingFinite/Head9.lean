import C20BoundaryMatching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace C20.Boundary

/-- Native evaluation: trusts Lean.ofReduceBool and the Lean compiler. -/
theorem matching_ten_head_9 : allMatchingStatesShard 10 9 = true := by native_decide

end C20.Boundary

#print axioms C20.Boundary.matching_ten_head_9
