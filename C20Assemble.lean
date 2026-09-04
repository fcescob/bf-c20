import C20Parity
import C20Reversal

namespace C20

theorem filter_length_two {A : Type} (f : A → Bool) (a b : A) :
    ([a, b].filter f).length = bit (f a) + bit (f b) := by
  cases f a <;> cases f b <;> rfl

theorem filter_length_four {A : Type} (f : A → Bool) (a b c d : A) :
    ([a, b, c, d].filter f).length = bit (f a) + bit (f b) + bit (f c) + bit (f d) := by
  cases f a <;> cases f b <;> cases f c <;> cases f d <;> rfl

/-- Two or four lifted kernel matchings, together with the switched
matching, close the odd-cycle proof. -/
theorem cover_of_patterns {V A : Type} (c d : Cycle V) (hc : OddCycle c) (hd : OddCycle d)
    (s : V → Bool) (outside : EdgeSet V) (houtside : PerfectMatching c d outside)
    (hspoke : ∀ v, outside.spoke v = !(s v))
    (patterns : List A) (hlen : patterns.length = 2 ∨ patterns.length = 4)
    (mask : A → {v // s v = true} → Bool)
    (lifts : ∀ a ∈ patterns, ∃ p : EdgeSet V, PerfectMatching c d p ∧ p.spoke = classOnGraph s (mask a))
    (partition : ∀ w, (patterns.filter (fun a => mask a w)).length = 1) :
    ∃ cover : Six V, DoubleCover c d cover := by
  rcases hlen with hlen | hlen
  · rcases List.length_eq_two.mp hlen with ⟨a, b, rfl⟩
    rcases lifts a (by simp) with ⟨pa, hpa, hsa⟩
    rcases lifts b (by simp) with ⟨pb, hpb, hsb⟩
    refine ⟨⟨outside, ⟨outside, pa, pa, pb, pb⟩⟩,
      three_spoke_partition_cover c d hc hd outside pa pb houtside hpa hpb ?_⟩
    intro v
    rw [hspoke v, hsa, hsb]
    cases hv : s v with
    | false => simp [classOnGraph, hv, bit]
    | true =>
      have h := partition ⟨v, hv⟩
      rw [filter_length_two] at h
      simpa [classOnGraph, hv, bit] using h
  · rcases List.length_eq_four.mp hlen with ⟨a, b, e, f, rfl⟩
    rcases lifts a (by simp) with ⟨pa, hpa, hsa⟩
    rcases lifts b (by simp) with ⟨pb, hpb, hsb⟩
    rcases lifts e (by simp) with ⟨pe, hpe, hse⟩
    rcases lifts f (by simp) with ⟨pf, hpf, hsf⟩
    let five : Five (EdgeSet V) := ⟨outside, pa, pb, pe, pf⟩
    refine ⟨⟨spokes V, five⟩, five_matchings_cover c d hc hd five
      ⟨houtside, hpa, hpb, hpe, hpf⟩ ?_⟩
    intro v
    change bit (outside.spoke v) + bit (pa.spoke v) + bit (pb.spoke v) +
      bit (pe.spoke v) + bit (pf.spoke v) = 1
    rw [hspoke v, hsa, hsb, hse, hsf]
    cases hv : s v with
    | false => simp [classOnGraph, hv, bit]
    | true =>
      have h := partition ⟨v, hv⟩
      rw [filter_length_four] at h
      simpa [classOnGraph, hv, bit] using h

def MatchingBoundaryTheorem : Prop :=
  ∀ k : Nat, k ∈ [2, 4, 6, 8, 10] → ∀ tail : List Nat, ∀ cf df : Nat,
    tail.Perm ((List.range (k - 1)).map (· + 1)) →
    cf ∈ Boundary.oddFlags k → df ∈ Boundary.oddFlags k →
    Boundary.MatchingConclusion ⟨k, 0 :: tail, cf, df⟩

/-- Any cyclic permutation of the labels beginning with zero is one of
the exact tail permutations accepted by the finite theorem. -/
theorem order_tail {k : Nat} (hk : 0 < k) (order : List Nat)
    (perm : order.Perm (List.range k)) (zero : order.getD 0 0 = 0) :
    ∃ tail, order = 0 :: tail ∧ tail.Perm ((List.range (k - 1)).map (· + 1)) := by
  cases order with
  | nil =>
    have h := perm.length_eq
    simp at h
    omega
  | cons a tail =>
    have ha : a = 0 := zero
    subst a
    refine ⟨tail, rfl, ?_⟩
    have he : k = (k - 1) + 1 := by omega
    rw [he, List.range_succ_eq_map] at perm
    exact List.Perm.cons_inv perm

end C20

#print axioms C20.cover_of_patterns
