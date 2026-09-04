import C20MatchingSmall
import C20MatchingFinite.Head0
import C20MatchingFinite.Head1
import C20MatchingFinite.Head2
import C20MatchingFinite.Head3
import C20MatchingFinite.Head4
import C20MatchingFinite.Head5
import C20MatchingFinite.Head6
import C20MatchingFinite.Head7
import C20MatchingFinite.Head8
import C20MatchingFinite.Head9

/-! Direct matching certificates, with explicit native compiler trust.
C20Theorem.lean applies this finite theorem to the checked graph deduction.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C20.Boundary

theorem matching_ten_shards (head : Nat) (hh : head < 10) :
    allMatchingStatesShard 10 head = true := by
  have h : head = 0 ∨ head = 1 ∨ head = 2 ∨ head = 3 ∨ head = 4 ∨ head = 5 ∨ head = 6 ∨ head = 7 ∨ head = 8 ∨ head = 9 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact matching_ten_head_0
  · exact matching_ten_head_1
  · exact matching_ten_head_2
  · exact matching_ten_head_3
  · exact matching_ten_head_4
  · exact matching_ten_head_5
  · exact matching_ten_head_6
  · exact matching_ten_head_7
  · exact matching_ten_head_8
  · exact matching_ten_head_9

theorem matching_up_to_ten_native (k : Nat) (hk : k ∈ [2, 4, 6, 8, 10])
    (tail : List Nat) (cf df : Nat)
    (hperm : tail.Perm ((List.range (k - 1)).map (· + 1)))
    (hc : cf ∈ oddFlags k) (hd : df ∈ oddFlags k) :
    MatchingConclusion ⟨k, 0 :: tail, cf, df⟩ := by
  simp at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact allMatchingStates_sound 2 tail cf df hperm hc hd matching_two
  · exact allMatchingStates_sound 4 tail cf df hperm hc hd matching_four
  · exact allMatchingStates_sound 6 tail cf df hperm hc hd matching_six_native
  · exact allMatchingStates_sound 8 tail cf df hperm hc hd matching_eight_native
  · exact matchingShard_sound 10 (tail.headD 0) tail cf df hperm hc hd rfl
      (matching_ten_shards _ (boundary_head_lt 10 (by decide) tail hperm))

end C20.Boundary
#print axioms C20.Boundary.matching_up_to_ten_native
