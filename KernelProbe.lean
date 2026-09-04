import C20Finite

/-! Separate performance probe; not part of the default build. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem kernelProbe_six : C20.Boundary.allBoundaryStates 6 = true := by decide +kernel

#print axioms kernelProbe_six
