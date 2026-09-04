import C20Cycles
import C20Expansion

/-! The even-order branch, with no boundary or circuit hypotheses. -/

namespace C20

theorem parityBit_succ (n : Nat) : parityBit (n + 1) = !(parityBit n) := by
  have h := parityBit_pred (n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  cases hn : parityBit n <;> cases hs : parityBit (n + 1) <;> simp_all

/-- Every connected cycle of even cardinality has alternating edge colours. -/
theorem exists_alternating_edges {m : Nat} (hm : 0 < m) (he : m % 2 = 0)
    (c : Cycle (Fin m)) (connected : ConnectedCycle c) :
    ∃ edge : Fin m → Bool, ∀ v, edge (c.next v) = !(edge v) := by
  classical
  let root : Fin m := ⟨0, hm⟩
  let selected : Fin m → Bool := fun v => decide (v = root)
  have hits := hits_of_connected c selected connected ⟨root, by simp [selected]⟩
  let dist := fun v => Classical.choose (exists_firstHit c.next selected v (hits v))
  have spec : ∀ v, FirstHit c.next selected v (dist v) :=
    fun v => Classical.choose_spec (exists_firstHit c.next selected v (hits v))
  have hz : dist root = 0 := firstHit_unique c.next selected root _ _ (spec root)
    (firstHit_zero c.next selected root (by simp [selected]))
  have full : FirstHit c.next selected (c.next root) (m - 1) := by
    constructor
    · have hlen : m - 1 + 1 = m := by omega
      rw [← walk_succ_start, hlen, walk_full_cycle hm c connected]
      simp [selected]
    · intro i hi
      simp only [selected, decide_eq_false_iff_not]
      intro h
      have hr : walk c.next (i + 1) root = root := by
        rw [walk_succ_start]
        exact h
      have hd := (walk_return_iff hm c connected root (i + 1)).mp hr
      have hle := Nat.le_of_dvd (by omega : 0 < i + 1) hd
      omega
  have hn : dist (c.next root) = m - 1 :=
    firstHit_unique c.next selected _ _ _ (spec _) full
  refine ⟨fun v => parityBit (dist v), ?_⟩
  intro v
  by_cases hv : v = root
  · subst v
    simp only [hz, hn, parityBit]
    have hp : (m - 1) % 2 = 1 := by omega
    simp [hp]
  · have hs : selected v = false := by simp [selected, hv]
    have hdist : dist v = dist (c.next v) + 1 :=
      firstHit_unique c.next selected v _ _ (spec v)
        (firstHit_succ c.next selected v _ hs (spec (c.next v)))
    rw [hdist, parityBit_succ, Bool.not_not]

theorem bit_not_add (b : Bool) : bit (!b) + bit b = 1 := by
  cases b <;> rfl

/-- The full graph conclusion for even m. The short circuit is unnecessary. -/
theorem even_order_cover {m : Nat} (hm : 0 < m) (he : m % 2 = 0)
    (c d : Cycle (Fin m)) (cc : ConnectedCycle c) (dc : ConnectedCycle d) :
    ∃ cover : Six (Fin m), DoubleCover c d cover := by
  rcases exists_alternating_edges hm he c cc with ⟨outer, ho⟩
  rcases exists_alternating_edges hm he d dc with ⟨inner, hi⟩
  let a : EdgeSet (Fin m) := ⟨fun _ => false, outer, inner⟩
  let b : EdgeSet (Fin m) := ⟨fun _ => false, fun v => !(outer v), fun v => !(inner v)⟩
  have hop : ∀ v, outer v = !(outer (c.prev v)) := by
    intro v
    simpa only [c.next_prev] using ho (c.prev v)
  have hip : ∀ v, inner v = !(inner (d.prev v)) := by
    intro v
    simpa only [d.next_prev] using hi (d.prev v)
  have ha : PerfectMatching c d a := by
    constructor
    · intro v
      change 0 + bit (outer (c.prev v)) + bit (outer v) = 1
      rw [hop v]
      cases outer (c.prev v) <;> rfl
    · intro v
      change 0 + bit (inner (d.prev v)) + bit (inner v) = 1
      rw [hip v]
      cases inner (d.prev v) <;> rfl
  have hb : PerfectMatching c d b := by
    constructor
    · intro v
      change 0 + bit (!(outer (c.prev v))) + bit (!(outer v)) = 1
      rw [hop v]
      cases outer (c.prev v) <;> rfl
    · intro v
      change 0 + bit (!(inner (d.prev v))) + bit (!(inner v)) = 1
      rw [hip v]
      cases inner (d.prev v) <;> rfl
  refine ⟨⟨spokes (Fin m), ⟨spokes (Fin m), a, a, b, b⟩⟩,
    tait_double_cover c d _ a b (spokes_perfect c d) ha hb ?_ ?_ ?_⟩
  · intro v; rfl
  · intro v
    change 0 + bit (outer v) + bit (!(outer v)) = 1
    cases outer v <;> rfl
  · intro v
    change 0 + bit (inner v) + bit (!(inner v)) = 1
    cases inner v <;> rfl

end C20

#print axioms C20.even_order_cover
