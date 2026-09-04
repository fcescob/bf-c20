import C20Assemble
import C20MatchingFinite

/-! Full C20 theorem. This file must pass together with all finite shards.

The finite calculation uses native_decide and therefore explicitly
trusts Lean.ofReduceBool and Lean's native compiler. The unbounded graph
reduction is checked with only the usual logical axioms.
-/

namespace C20

theorem c20 : C20Statement :=
  c20_from_finite Boundary.matching_up_to_ten_native

end C20

#print C20.c20
#print axioms C20.c20
