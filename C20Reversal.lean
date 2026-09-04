import C20Normalize

namespace C20

def Cycle.reverse {V : Type} (c : Cycle V) : Cycle V where
  next := c.prev
  prev := c.next
  prev_next := c.next_prev
  next_prev := c.prev_next
  next_ne v h := c.next_ne v (by simpa only [c.next_prev] using (congrArg c.next h).symm)

theorem reverse_connected {V : Type} [Finite V] (c : Cycle V) (cc : ConnectedCycle c) :
    ConnectedCycle c.reverse := by
  intro u v
  rcases cc u v with ⟨n, hn⟩
  have h : c.toPerm.SameCycle u v :=
    ⟨(n : Int), by simpa only [zpow_natCast, toPerm_pow_apply] using hn⟩
  rcases h.inv.exists_nat_pow_eq with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  change (c.reverse.toPerm ^ j) u = v at hj
  simpa only [toPerm_pow_apply] using hj

theorem adjacent_reverse_iff {V : Type} (c : Cycle V) (u v : V) :
    Adjacent c.reverse u v ↔ Adjacent c u v := by
  constructor
  · intro h
    rcases h with h | h
    · change c.prev u = v at h
      exact Or.inr (by simpa only [c.next_prev] using (congrArg c.next h).symm)
    · change c.prev v = u at h
      exact Or.inl (by simpa only [c.next_prev] using (congrArg c.next h).symm)
  · intro h
    rcases h with h | h
    · exact Or.inr (by simpa only [c.prev_next] using (congrArg c.prev h).symm)
    · exact Or.inl (by simpa only [c.prev_next] using (congrArg c.prev h).symm)

def KernelDomino.reverse {m : Nat} {c : Cycle (Fin m)} {s : Fin m → Bool}
    (dom : KernelDomino c s) : KernelDomino c.reverse s :=
  ⟨dom.mate, dom.involutive, fun v => (adjacent_reverse_iff c _ _).mpr (dom.adjacent v)⟩

theorem KernelDomino.out_reverse {m : Nat} (hm : 3 ≤ m) {c : Cycle (Fin m)}
    {s : Fin m → Bool} (dom : KernelDomino c s) (cc : ConnectedCycle c)
    (v : {v // s v = true}) : dom.reverse.out v = !(dom.out v) := by
  cases h : dom.out v with
  | false =>
    have hp := dom.mate_prev v h
    simp [KernelDomino.out, KernelDomino.reverse, Cycle.reverse, hp]
  | true =>
    have hn : c.next v.val = (dom.mate v).val := by simpa [KernelDomino.out] using h
    have hp : c.prev v.val ≠ (dom.mate v).val := by
      rw [← hn]
      exact Ne.symm (cycle_neighbors_distinct hm c cc v.val)
    simp [KernelDomino.out, KernelDomino.reverse, Cycle.reverse, hp]

def ShortCircuit.reverseInner {V : Type} {c d : Cycle V} (q : ShortCircuit c d) :
    ShortCircuit c d.reverse where
  size := q.size
  min_two := q.min_two
  even := q.even
  length_le_twenty := q.length_le_twenty
  vertex := q.vertex
  injective := q.injective
  outer_step := q.outer_step
  inner_step i hi := (adjacent_reverse_iff d _ _).mpr (q.inner_step i hi)

def reverseInnerEdges {V : Type} (d : Cycle V) (p : EdgeSet V) : EdgeSet V :=
  ⟨p.spoke, p.outer, fun v => p.inner (d.next v)⟩

def Five.map {A B : Type} (f : A → B) (p : Five A) : Five B :=
  ⟨f p.p₀, f p.p₁, f p.p₂, f p.p₃, f p.p₄⟩

theorem reverseInner_matching {V : Type} (c d : Cycle V) (p : EdgeSet V)
    (hp : PerfectMatching c d.reverse p) : PerfectMatching c d (reverseInnerEdges d p) := by
  constructor
  · exact hp.1
  · intro v
    have h := hp.2 v
    change bit (p.spoke v) + bit (p.inner (d.next v)) + bit (p.inner v) = 1 at h
    change bit (p.spoke v) + bit (p.inner (d.next (d.prev v))) + bit (p.inner (d.next v)) = 1
    rw [d.next_prev]
    omega

theorem reverseInner_cover {V : Type} (c d : Cycle V) (s : Six V)
    (hs : DoubleCover c d.reverse s) :
    DoubleCover c d ⟨reverseInnerEdges d s.first, s.rest.map (reverseInnerEdges d)⟩ := by
  rcases hs with ⟨hn, hp, hsp, ho, hi⟩
  refine ⟨reverseInner_matching c d s.first hn, ?_, hsp, ho, ?_⟩
  · rcases hp with ⟨h0, h1, h2, h3, h4⟩
    exact ⟨reverseInner_matching c d _ h0, reverseInner_matching c d _ h1,
      reverseInner_matching c d _ h2, reverseInner_matching c d _ h3,
      reverseInner_matching c d _ h4⟩
  · intro v
    exact hi (d.next v)

end C20

#print axioms C20.reverseInner_cover
