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

theorem odd_root_cover (finite : MatchingBoundaryTheorem) {m : Nat} (hm : 3 ≤ m)
    (odd : m % 2 = 1) (c d : Cycle (Fin m)) (cc : ConnectedCycle c) (dc : ConnectedCycle d)
    (q : ShortCircuit c d) (root : {v // kernelSelected q v = true})
    (croot : (circuitKernelDomino q c (outerDomino q)).out root = true)
    (droot : (circuitKernelDomino q d (innerDomino q)).out root = true) :
    ∃ cover : Six (Fin m), DoubleCover c d cover := by
  let s := kernelSelected q
  let ne := kernelSelected_nonempty q
  let card := kernelSelected_card q
  let bc := compressedCycle c s cc ne
  let bd := compressedCycle d s dc ne
  let cs := cycleCoordinates bc (compressedCycle_connected c s cc ne) root q.size card
  let ds := cycleCoordinates bd (compressedCycle_connected d s dc ne) root q.size card
  have hcOdd := oddCycle_of_odd_card odd c cc
  have hdOdd := oddCycle_of_odd_card odd d dc
  have hsize := circuit_size_cases q
  rcases normalize_cycle hm (circuitKernelDomino q c (outerDomino q)) cc ne hcOdd
    root croot q.size card hsize with ⟨cf, hcf, cgap⟩
  rcases normalize_cycle hm (circuitKernelDomino q d (innerDomino q)) dc ne hdOdd
    root droot q.size card hsize with ⟨df, hdf, dgap⟩
  let order := orderLabels ds cs.symm
  have positive : 0 < q.size := by have h := q.min_two; omega
  let z : Fin q.size := ⟨0, positive⟩
  have cs0 : cs z = root := rfl
  have ds0 : ds z = root := rfl
  have hzero : order.getD 0 0 = 0 := by
    change (List.ofFn (fun i => (cs.symm (ds i)).val)).getD z.val 0 = 0
    rw [getD_ofFn, ds0, ← cs0, cs.symm_apply_apply]
    rfl
  rcases order_tail positive order (orderLabels_perm ds cs.symm) hzero with ⟨tail, ht, hperm⟩
  rcases finite q.size hsize tail cf df hperm hcf hdf with ⟨patterns, hlen, hrows, hpartition⟩
  let mask := fun p : Boundary.Pattern => fun w : {v // s v = true} =>
    Boundary.selected p.mask (cs.symm w).val
  have lifts : ∀ p ∈ patterns, ∃ pm : EdgeSet (Fin m), PerfectMatching c d pm ∧
      pm.spoke = classOnGraph s (mask p) := by
    intro p hp
    have rowC : Boundary.RowMatching (orderLabels cs cs.symm) cf p.mask p.outer := by
      rw [orderLabels_self]
      exact (hrows p hp).1
    have rowD : Boundary.RowMatching (orderLabels ds cs.symm) df p.mask p.inner := by
      change Boundary.RowMatching order df p.mask p.inner
      rw [ht]
      exact (hrows p hp).2
    have ho := rowMatching_transfer bc (compressedGap c s cc ne) cs cs.symm
      (cycleCoordinates_next _ _ _ _ _) cf p.mask p.outer cgap rowC
    have hi := rowMatching_transfer bd (compressedGap d s dc ne) ds cs.symm
      (cycleCoordinates_next _ _ _ _ _) df p.mask p.inner dgap rowD
    exact lift_compressed_matching c d s cc dc ne (mask p)
      (fun w => Boundary.selected p.outer (cs.symm w).val)
      (fun w => Boundary.selected p.inner (cs.symm w).val) ho hi
  rcases circuit_switch_matching hm c d cc dc q with ⟨outside, houtside, hspoke⟩
  have hs : ∀ v, outside.spoke v = !(s v) := by
    intro v
    rw [hspoke v]
    simp [s, kernelSelected]
  apply cover_of_patterns c d hcOdd hdOdd s outside houtside hs patterns hlen mask lifts
  intro w
  exact hpartition (cs.symm w).val (cs.symm w).isLt

theorem exists_forward_root {m : Nat} (hm : 3 ≤ m) {c : Cycle (Fin m)}
    {s : Fin m → Bool} (dom : KernelDomino c s) (cc : ConnectedCycle c)
    (nonempty : ∃ v, s v = true) : ∃ root, dom.out root = true := by
  rcases nonempty with ⟨v, hv⟩
  let root : {v // s v = true} := ⟨v, hv⟩
  cases h : dom.out root with
  | true => exact ⟨root, h⟩
  | false =>
    refine ⟨nextSelected c s cc ⟨v, hv⟩ root, ?_⟩
    simpa only [h, Bool.not_false] using dom.out_toggle hm cc ⟨v, hv⟩ root

/-- The entire graph reduction, conditional only on the separately
stated finite matching theorem. No supplied graph witness remains. -/
theorem c20_from_finite (finite : MatchingBoundaryTheorem) : C20Statement := by
  intro m hm c d cc dc q
  by_cases even : m % 2 = 0
  · exact even_order_cover (by omega) even c d cc dc
  · have odd : m % 2 = 1 := by omega
    let cd := circuitKernelDomino q c (outerDomino q)
    let dd := circuitKernelDomino q d (innerDomino q)
    rcases exists_forward_root hm cd cc (kernelSelected_nonempty q) with ⟨root, cr⟩
    cases dr : dd.out root with
    | true => exact odd_root_cover finite hm odd c d cc dc q root cr dr
    | false =>
      have dr' : dd.reverse.out root = true := by
        simpa only [dr, Bool.not_false] using dd.out_reverse hm dc root
      have hroot : (circuitKernelDomino q.reverseInner d.reverse (innerDomino q.reverseInner)).out root = true := by
        exact dr'
      rcases odd_root_cover finite hm odd c d.reverse cc (reverse_connected d dc)
        q.reverseInner root cr hroot with ⟨cover, hcover⟩
      exact ⟨_, reverseInner_cover c d cover hcover⟩

end C20

#print axioms C20.cover_of_patterns
#print axioms C20.c20_from_finite
